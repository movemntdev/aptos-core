// Copyright © Aptos Foundation
// Parts of the project are originally copyright © Meta Platforms, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Implementation of writing logs to both local printers (e.g. stdout) and remote loggers
//! (e.g. Logstash)

use crate::{
    counters::{STRUCT_LOG_PARSE_ERROR_COUNT, STRUCT_LOG_QUEUE_ERROR_COUNT},
    logger::Logger,
    Event, Filter, Key, Level, Metadata,
};
use aptos_infallible::RwLock;
use backtrace::Backtrace;
use chrono::{SecondsFormat, Utc};
use once_cell::sync::Lazy;
use serde::{ser::SerializeStruct, Serialize, Serializer};
use std::{
    collections::BTreeMap,
    env, fmt,
    fmt::Debug,
    io::{Stdout, Write},
    ops::{Deref, DerefMut},
    str::FromStr,
    sync::{self, Arc},
    time::Duration,
};
use strum_macros::EnumString;

const RUST_LOG: &str = "RUST_LOG";
pub const RUST_LOG_TELEMETRY: &str = "RUST_LOG_TELEMETRY";
const RUST_LOG_FORMAT: &str = "RUST_LOG_FORMAT";
/// Default size of log write channel, if the channel is full, logs will be dropped
pub const CHANNEL_SIZE: usize = 10000;
const FLUSH_TIMEOUT: Duration = Duration::from_secs(5);

/// Note: To disable length limits, set `RUST_LOG_FIELD_MAX_LEN` to -1.
const RUST_LOG_FIELD_MAX_LEN_ENV_VAR: &str = "RUST_LOG_FIELD_MAX_LEN";
static RUST_LOG_FIELD_MAX_LEN: Lazy<usize> = Lazy::new(|| {
    env::var(RUST_LOG_FIELD_MAX_LEN_ENV_VAR)
        .ok()
        .and_then(|value| i64::from_str(&value).map(|value| value as usize).ok())
        .unwrap_or(TruncatedLogString::DEFAULT_MAX_LEN)
});

struct TruncatedLogString(String);

impl TruncatedLogString {
    const DEFAULT_MAX_LEN: usize = 10 * 1024;
    const TRUNCATION_SUFFIX: &'static str = "(truncated)";

    fn new(s: String) -> Self {
        let mut truncated = s;

        if truncated.len() > RUST_LOG_FIELD_MAX_LEN.saturating_add(Self::TRUNCATION_SUFFIX.len()) {
            truncated.truncate(*RUST_LOG_FIELD_MAX_LEN);
            truncated.push_str(Self::TRUNCATION_SUFFIX);
        }
        TruncatedLogString(truncated)
    }
}

impl DerefMut for TruncatedLogString {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Deref for TruncatedLogString {
    type Target = String;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<String> for TruncatedLogString {
    fn from(value: String) -> Self {
        TruncatedLogString::new(value)
    }
}

impl From<TruncatedLogString> for String {
    fn from(val: TruncatedLogString) -> Self {
        val.0
    }
}

#[derive(EnumString)]
#[strum(serialize_all = "lowercase")]
enum LogFormat {
    Json,
    Text,
}

/// A single log entry emitted by a logging macro with associated metadata
#[derive(Debug)]
pub struct LogEntry {
    metadata: Metadata,
    thread_name: Option<String>,
    /// The program backtrace taken when the event occurred. Backtraces
    /// are only supported for errors and must be configured.
    backtrace: Option<String>,
    hostname: Option<&'static str>,
    namespace: Option<&'static str>,
    timestamp: String,
    data: BTreeMap<Key, serde_json::Value>,
    message: Option<String>,
    peer_id: Option<&'static str>,
    chain_id: Option<u8>,
}

// implement custom serializer for LogEntry since we want to promote the `metadata.level` field into a top-level `level` field
// and prefix the remaining metadata attributes as `source.<metadata_field>` which can't be expressed with serde macros alone.
impl Serialize for LogEntry {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut state = serializer.serialize_struct("LogEntry", 9)?;
        state.serialize_field("level", &self.metadata.level())?;
        state.serialize_field("source", &self.metadata)?;
        if let Some(thread_name) = &self.thread_name {
            state.serialize_field("thread_name", thread_name)?;
        }
        if let Some(hostname) = &self.hostname {
            state.serialize_field("hostname", hostname)?;
        }
        if let Some(namespace) = &self.namespace {
            state.serialize_field("namespace", namespace)?;
        }
        state.serialize_field("timestamp", &self.timestamp)?;
        if let Some(message) = &self.message {
            state.serialize_field("message", message)?;
        }
        if !&self.data.is_empty() {
            state.serialize_field("data", &self.data)?;
        }
        if let Some(backtrace) = &self.backtrace {
            state.serialize_field("backtrace", backtrace)?;
        }
        if let Some(peer_id) = &self.peer_id {
            state.serialize_field("peer_id", peer_id)?;
        }
        state.end()
    }
}

impl LogEntry {
    fn new(event: &Event, thread_name: Option<&str>, enable_backtrace: bool) -> Self {
        use crate::{Value, Visitor};

        struct JsonVisitor<'a>(&'a mut BTreeMap<Key, serde_json::Value>);

        impl<'a> Visitor for JsonVisitor<'a> {
            fn visit_pair(&mut self, key: Key, value: Value<'_>) {
                let v = match value {
                    Value::Debug(d) => serde_json::Value::String(
                        TruncatedLogString::from(format!("{:?}", d)).into(),
                    ),
                    Value::Display(d) => {
                        serde_json::Value::String(TruncatedLogString::from(d.to_string()).into())
                    },
                    Value::Serde(s) => match serde_json::to_value(s) {
                        Ok(value) => value,
                        Err(e) => {
                            // Log and skip the value that can't be serialized
                            eprintln!("error serializing structured log: {} for key {:?}", e, key);
                            return;
                        },
                    },
                };

                self.0.insert(key, v);
            }
        }

        let metadata = *event.metadata();
        let thread_name = thread_name.map(ToOwned::to_owned);
        let message = event
            .message()
            .map(fmt::format)
            .map(|s| TruncatedLogString::from(s).into());

        static HOSTNAME: Lazy<Option<String>> = Lazy::new(|| {
            hostname::get()
                .ok()
                .and_then(|name| name.into_string().ok())
        });

        static NAMESPACE: Lazy<Option<String>> =
            Lazy::new(|| env::var("KUBERNETES_NAMESPACE").ok());

        let hostname = HOSTNAME.as_deref();
        let namespace = NAMESPACE.as_deref();
        let peer_id = None;
        let chain_id = None;

        let backtrace = if enable_backtrace && matches!(metadata.level(), Level::Error) {
            let mut backtrace = Backtrace::new();
            let mut frames = backtrace.frames().to_vec();
            if frames.len() > 3 {
                frames.drain(0..3); // Remove the first 3 unnecessary frames to simplify backtrace
            }
            backtrace = frames.into();
            Some(format!("{:?}", backtrace))
        } else {
            None
        };

        let mut data = BTreeMap::new();
        for schema in event.keys_and_values() {
            schema.visit(&mut JsonVisitor(&mut data));
        }

        Self {
            metadata,
            thread_name,
            backtrace,
            hostname,
            namespace,
            timestamp: Utc::now().to_rfc3339_opts(SecondsFormat::Micros, true),
            data,
            message,
            peer_id,
            chain_id,
        }
    }

    pub fn metadata(&self) -> &Metadata {
        &self.metadata
    }

    pub fn thread_name(&self) -> Option<&str> {
        self.thread_name.as_deref()
    }

    pub fn backtrace(&self) -> Option<&str> {
        self.backtrace.as_deref()
    }

    pub fn hostname(&self) -> Option<&str> {
        self.hostname
    }

    pub fn namespace(&self) -> Option<&str> {
        self.namespace
    }

    pub fn timestamp(&self) -> &str {
        self.timestamp.as_str()
    }

    pub fn data(&self) -> &BTreeMap<Key, serde_json::Value> {
        &self.data
    }

    pub fn message(&self) -> Option<&str> {
        self.message.as_deref()
    }

    pub fn peer_id(&self) -> Option<&str> {
        self.peer_id
    }

    pub fn chain_id(&self) -> Option<u8> {
        self.chain_id
    }
}

/// A builder for a `AptosData`, configures what, where, and how to write logs.
pub struct AptosDataBuilder {
    channel_size: usize,
    tokio_console_port: Option<u16>,
    enable_backtrace: bool,
    level: Level,
    remote_level: Level,
    telemetry_level: Level,
    printer: Option<Box<dyn Writer>>,
    custom_format: Option<fn(&LogEntry) -> Result<String, fmt::Error>>,
}

impl AptosDataBuilder {
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self {
            channel_size: CHANNEL_SIZE,
            tokio_console_port: None,
            enable_backtrace: false,
            level: Level::Info,
            remote_level: Level::Info,
            telemetry_level: Level::Warn,
            printer: Some(Box::new(StdoutWriter::new())),
            custom_format: None,
        }
    }

    pub fn enable_backtrace(&mut self) -> &mut Self {
        self.enable_backtrace = true;
        self
    }

    pub fn level(&mut self, level: Level) -> &mut Self {
        self.level = level;
        self
    }

    pub fn remote_level(&mut self, level: Level) -> &mut Self {
        self.remote_level = level;
        self
    }

    pub fn telemetry_level(&mut self, level: Level) -> &mut Self {
        self.telemetry_level = level;
        self
    }

    pub fn channel_size(&mut self, channel_size: usize) -> &mut Self {
        self.channel_size = channel_size;
        self
    }

    pub fn printer(&mut self, printer: Box<dyn Writer + Send + Sync + 'static>) -> &mut Self {
        self.printer = Some(printer);
        self
    }

    pub fn tokio_console_port(&mut self, tokio_console_port: Option<u16>) -> &mut Self {
        self.tokio_console_port = tokio_console_port;
        self
    }

    pub fn custom_format(
        &mut self,
        format: fn(&LogEntry) -> Result<String, fmt::Error>,
    ) -> &mut Self {
        self.custom_format = Some(format);
        self
    }

    pub fn init(&mut self) {
        self.build();
    }

    fn build_filter(&self) -> Filter {
        // Keep this block same as upstream, which also builds a telemetry filter
        let local_filter = {
            let mut filter_builder = Filter::builder();

            if env::var(RUST_LOG).is_ok() {
                filter_builder.with_env(RUST_LOG);
            } else {
                filter_builder.filter_level(self.level.into());
            }

            filter_builder.build()
        };

        local_filter
    }

    fn build_logger(&mut self) -> Arc<AptosData> {
        let filter = self.build_filter();

        if let Ok(log_format) = env::var(RUST_LOG_FORMAT) {
            let log_format = LogFormat::from_str(&log_format).unwrap();
            self.custom_format = match log_format {
                LogFormat::Json => Some(json_format),
                LogFormat::Text => Some(text_format),
            }
        }

        Arc::new(AptosData {
            enable_backtrace: self.enable_backtrace,
            sender: None,
            printer: self.printer.take(),
            filter: RwLock::new(filter),
            formatter: self.custom_format.take().unwrap_or(text_format),
        })
    }

    pub fn build(&mut self) -> Arc<AptosData> {
        let logger = self.build_logger();

        let tokio_console_port = if cfg!(feature = "tokio-console") {
            self.tokio_console_port
        } else {
            None
        };

        crate::logger::set_global_logger(logger.clone(), tokio_console_port);
        logger
    }
}

pub struct AptosData {
    enable_backtrace: bool,
    sender: Option<sync::mpsc::SyncSender<LoggerServiceEvent>>,
    printer: Option<Box<dyn Writer>>,
    filter: RwLock<Filter>,
    pub(crate) formatter: fn(&LogEntry) -> Result<String, fmt::Error>,
}

impl AptosData {
    pub fn builder() -> AptosDataBuilder {
        AptosDataBuilder::new()
    }

    #[allow(clippy::new_ret_no_self)]
    pub fn new() -> AptosDataBuilder {
        Self::builder()
    }

    pub fn init_for_testing() {
        // Create the Aptos Data Builder
        let mut builder = Self::builder();
        builder
            .enable_backtrace()
            .printer(Box::new(StdoutWriter::new()));

        // If RUST_LOG wasn't specified, default to Debug logging
        if env::var(RUST_LOG).is_err() {
            builder.level(Level::Debug);
        }

        builder.build();
    }

    pub fn set_local_filter(&self, filter: Filter) {
        *self.filter.write() = filter;
    }

    fn send_entry(&self, entry: LogEntry) {
        if let Some(printer) = &self.printer {
            let s = (self.formatter)(&entry).expect("Unable to format");
            printer.write(s);
        }

        if let Some(sender) = &self.sender {
            if sender
                .try_send(LoggerServiceEvent::LogEntry(entry))
                .is_err()
            {
                STRUCT_LOG_QUEUE_ERROR_COUNT.inc();
            }
        }
    }
}

impl Logger for AptosData {
    fn enabled(&self, metadata: &Metadata) -> bool {
        self.filter.read().enabled(metadata)
    }

    fn record(&self, event: &Event) {
        let entry = LogEntry::new(
            event,
            ::std::thread::current().name(),
            self.enable_backtrace,
        );

        self.send_entry(entry)
    }

    fn flush(&self) {
        if let Some(sender) = &self.sender {
            let (oneshot_sender, oneshot_receiver) = sync::mpsc::sync_channel(1);
            match sender.try_send(LoggerServiceEvent::Flush(oneshot_sender)) {
                Ok(_) => {
                    if let Err(err) = oneshot_receiver.recv_timeout(FLUSH_TIMEOUT) {
                        eprintln!("[Logging] Unable to flush recv: {}", err);
                    }
                },
                Err(err) => {
                    eprintln!("[Logging] Unable to flush send: {}", err);
                    std::thread::sleep(FLUSH_TIMEOUT);
                },
            }
        }
    }
}

enum LoggerServiceEvent {
    LogEntry(LogEntry),
    Flush(sync::mpsc::SyncSender<()>),
}

/// A trait encapsulating the operations required for writing logs.
pub trait Writer: Send + Sync {
    /// Write the log.
    fn write(&self, log: String);

    /// Write the log in an async task.
    fn write_buferred(&mut self, log: String);
}

/// A struct for writing logs to stdout
struct StdoutWriter {
    buffer: std::io::BufWriter<Stdout>,
}

impl StdoutWriter {
    pub fn new() -> Self {
        let buffer = std::io::BufWriter::new(std::io::stdout());
        Self { buffer }
    }
}
impl Writer for StdoutWriter {
    /// Write log to stdout
    fn write(&self, log: String) {
        println!("{}", log);
    }

    fn write_buferred(&mut self, log: String) {
        self.buffer
            .write_fmt(format_args!("{}\n", log))
            .unwrap_or_default();
    }
}

/// A struct for writing logs to a file
pub struct FileWriter {
    log_file: RwLock<std::fs::File>,
}

impl FileWriter {
    pub fn new(log_file: std::path::PathBuf) -> Self {
        let file = std::fs::OpenOptions::new()
            .append(true)
            .create(true)
            .open(log_file)
            .expect("Unable to open log file");
        Self {
            log_file: RwLock::new(file),
        }
    }
}

impl Writer for FileWriter {
    /// Write to file
    fn write(&self, log: String) {
        if let Err(err) = writeln!(self.log_file.write(), "{}", log) {
            eprintln!("Unable to write to log file: {}", err);
        }
    }

    fn write_buferred(&mut self, log: String) {
        self.write(log);
    }
}

/// Converts a record into a string representation:
/// UNIX_TIMESTAMP LOG_LEVEL [thread_name] FILE:LINE MESSAGE JSON_DATA
/// Example:
/// 2020-03-07 05:03:03 INFO [thread_name] common/aptos-logger/src/lib.rs:261 Hello { "world": true }
fn text_format(entry: &LogEntry) -> Result<String, fmt::Error> {
    use std::fmt::Write;

    let mut w = String::new();
    write!(w, "{}", entry.timestamp)?;

    if let Some(thread_name) = &entry.thread_name {
        write!(w, " [{}]", thread_name)?;
    }

    write!(
        w,
        " {} {}",
        entry.metadata.level(),
        entry.metadata.source_path()
    )?;

    if let Some(message) = &entry.message {
        write!(w, " {}", message)?;
    }

    if !entry.data.is_empty() {
        write!(w, " {}", serde_json::to_string(&entry.data).unwrap())?;
    }

    Ok(w)
}

// converts a record into json format
fn json_format(entry: &LogEntry) -> Result<String, fmt::Error> {
    match serde_json::to_string(&entry) {
        Ok(s) => Ok(s),
        Err(_) => {
            // TODO: Improve the error handling here. Currently we're just increasing some misleadingly-named metric and dropping any context on why this could not be deserialized.
            STRUCT_LOG_PARSE_ERROR_COUNT.inc();
            Err(fmt::Error)
        },
    }
}

#[cfg(test)]
mod tests {
    use super::LogEntry;
    use crate::{
        aptos_logger::{json_format, TruncatedLogString},
        debug, error, info,
        logger::Logger,
        trace, warn, Event, Key, KeyValue, Level, Metadata, Schema, Value, Visitor,
    };
    use chrono::{DateTime, Utc};
    #[cfg(test)]
    use pretty_assertions::assert_eq;
    use serde_json::Value as JsonValue;
    use std::{
        env,
        sync::{
            mpsc::{self, Receiver, SyncSender},
            Arc,
        },
        thread,
    };

    #[derive(serde::Serialize)]
    #[serde(rename_all = "snake_case")]
    enum Enum {
        FooBar,
    }

    struct TestSchema<'a> {
        foo: usize,
        bar: &'a Enum,
    }

    impl Schema for TestSchema<'_> {
        fn visit(&self, visitor: &mut dyn Visitor) {
            visitor.visit_pair(Key::new("foo"), Value::from_serde(&self.foo));
            visitor.visit_pair(Key::new("bar"), Value::from_serde(&self.bar));
        }
    }

    struct LogStream {
        sender: SyncSender<LogEntry>,
        enable_backtrace: bool,
    }

    impl LogStream {
        fn new(enable_backtrace: bool) -> (Self, Receiver<LogEntry>) {
            let (sender, receiver) = mpsc::sync_channel(1024);
            let log_stream = Self {
                sender,
                enable_backtrace,
            };
            (log_stream, receiver)
        }
    }

    impl Logger for LogStream {
        fn enabled(&self, metadata: &Metadata) -> bool {
            metadata.level() <= Level::Debug
        }

        fn record(&self, event: &Event) {
            let entry = LogEntry::new(
                event,
                ::std::thread::current().name(),
                self.enable_backtrace,
            );
            self.sender.send(entry).unwrap();
        }

        fn flush(&self) {}
    }

    fn set_test_logger() -> Receiver<LogEntry> {
        let (logger, receiver) = LogStream::new(true);
        let logger = Arc::new(logger);
        crate::logger::set_global_logger(logger, None);
        receiver
    }

    // TODO: Find a better mechanism for testing that allows setting the logger not globally
    #[test]
    fn basic() {
        let receiver = set_test_logger();
        let number = 12345;

        // Send an info log
        let before = Utc::now();
        let mut line_num = line!();
        info!(
            TestSchema {
                foo: 5,
                bar: &Enum::FooBar
            },
            test = true,
            category = "name",
            KeyValue::new("display", Value::from_display(&number)),
            "This is a log"
        );

        let after = Utc::now();

        let mut entry = receiver.recv().unwrap();

        // Ensure standard fields are filled
        assert_eq!(entry.metadata.level(), Level::Info);
        assert_eq!(
            entry.metadata.target(),
            module_path!().split("::").next().unwrap()
        );
        assert_eq!(entry.message.as_deref(), Some("This is a log"));
        assert!(entry.backtrace.is_none());

        // Ensure json formatter works
        // hardcoding a timestamp and hostname to make the tests deterministic and not depend on environment
        let original_timestamp = entry.timestamp;
        entry.timestamp = String::from("2022-07-24T23:42:29.540278Z");
        entry.hostname = Some("test-host");
        line_num += 1;
        let thread_name = thread::current().name().map(|s| s.to_string()).unwrap();

        let expected = format!("{{\"level\":\"INFO\",\"source\":{{\"package\":\"aptos_logger\",\"file\":\"crates/aptos-logger/src/aptos_logger.rs:{line_num}\"}},\"thread_name\":\"{thread_name}\",\"hostname\":\"test-host\",\"timestamp\":\"2022-07-24T23:42:29.540278Z\",\"message\":\"This is a log\",\"data\":{{\"bar\":\"foo_bar\",\"category\":\"name\",\"display\":\"12345\",\"foo\":5,\"test\":true}}}}");

        assert_eq!(json_format(&entry).unwrap(), expected);

        entry.timestamp = original_timestamp;

        // Log time should be the time the structured log entry was created
        let timestamp = DateTime::parse_from_rfc3339(&entry.timestamp).unwrap();
        let timestamp: DateTime<Utc> = DateTime::from(timestamp);
        assert!(before <= timestamp && timestamp <= after);

        // Ensure data stored is the right type
        assert_eq!(
            entry.data.get(&Key::new("foo")).and_then(JsonValue::as_u64),
            Some(5)
        );
        assert_eq!(
            entry.data.get(&Key::new("bar")).and_then(JsonValue::as_str),
            Some("foo_bar")
        );
        assert_eq!(
            entry
                .data
                .get(&Key::new("display"))
                .and_then(JsonValue::as_str),
            Some(format!("{}", number)).as_deref(),
        );
        assert_eq!(
            entry
                .data
                .get(&Key::new("test"))
                .and_then(JsonValue::as_bool),
            Some(true),
        );
        assert_eq!(
            entry
                .data
                .get(&Key::new("category"))
                .and_then(JsonValue::as_str),
            Some("name"),
        );

        // Test error logs contain backtraces
        error!("This is an error log");
        let entry = receiver.recv().unwrap();
        assert!(entry.backtrace.is_some());

        // Test all log levels work properly
        // Tracing should be skipped because the Logger was setup to skip Tracing events
        trace!("trace");
        debug!("debug");
        info!("info");
        warn!("warn");
        error!("error");

        let levels = &[Level::Debug, Level::Info, Level::Warn, Level::Error];

        for level in levels {
            let entry = receiver.recv().unwrap();
            assert_eq!(entry.metadata.level(), *level);
        }

        // Verify that the thread name is properly included
        let handler = thread::Builder::new()
            .name("named thread".into())
            .spawn(|| info!("thread"))
            .unwrap();

        handler.join().unwrap();
        let entry = receiver.recv().unwrap();
        assert_eq!(entry.thread_name.as_deref(), Some("named thread"));

        // Test Debug and Display inputs
        let debug_struct = DebugStruct {};
        let display_struct = DisplayStruct {};

        error!(identifier = ?debug_struct, "Debug test");
        error!(identifier = ?debug_struct, other = "value", "Debug2 test");
        error!(identifier = %display_struct, "Display test");
        error!(identifier = %display_struct, other = "value", "Display2 test");
        error!("Literal" = ?debug_struct, "Debug test");
        error!("Literal" = ?debug_struct, other = "value", "Debug test");
        error!("Literal" = %display_struct, "Display test");
        error!("Literal" = %display_struct, other = "value", "Display2 test");
        error!("Literal" = %display_struct, other = "value", identifier = ?debug_struct, "Mixed test");
    }

    struct DebugStruct {}

    impl std::fmt::Debug for DebugStruct {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "DebugStruct!")
        }
    }

    struct DisplayStruct {}

    impl std::fmt::Display for DisplayStruct {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "DisplayStruct!")
        }
    }

    #[test]
    fn test_log_event_truncation() {
        let log_entry = LogEntry::new(
            &Event::new(
                &Metadata::new(Level::Error, "target", "hyper", "source_path"),
                Some(format_args!(
                    "{}",
                    "a".repeat(2 * TruncatedLogString::DEFAULT_MAX_LEN)
                )),
                &[
                    &KeyValue::new(
                        "key1",
                        Value::Debug(&"x".repeat(2 * TruncatedLogString::DEFAULT_MAX_LEN)),
                    ),
                    &KeyValue::new(
                        "key2",
                        Value::Display(&"y".repeat(2 * TruncatedLogString::DEFAULT_MAX_LEN)),
                    ),
                ],
            ),
            Some("test_thread"),
            false,
        );
        assert_eq!(
            log_entry.message,
            Some(format!(
                "{}{}",
                "a".repeat(TruncatedLogString::DEFAULT_MAX_LEN),
                "(truncated)"
            ))
        );
        assert_eq!(
            log_entry.data().first_key_value().unwrap().1,
            &serde_json::Value::String(format!(
                "\"{}{}",
                "x".repeat(TruncatedLogString::DEFAULT_MAX_LEN - 1),
                "(truncated)"
            ))
        );
        assert_eq!(
            log_entry.data().last_key_value().unwrap().1,
            &serde_json::Value::String(format!(
                "{}{}",
                "y".repeat(TruncatedLogString::DEFAULT_MAX_LEN),
                "(truncated)"
            ))
        );
    }
}
