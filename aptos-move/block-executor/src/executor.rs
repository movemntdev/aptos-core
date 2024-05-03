// Copyright © Aptos Foundation
// Parts of the project are originally copyright © Meta Platforms, Inc.
// SPDX-License-Identifier: Apache-2.0

use crate::{
    counters,
    counters::VM_INIT_SECONDS,
    errors::*,
    executor_utilities::*,
    limit_processor::BlockGasLimitProcessor,
    task::{ExecutionStatus, ExecutorTask, TransactionOutput},
    txn_commit_hook::TransactionCommitHook,
    txn_last_input_output::TxnLastInputOutput,
    types::ReadWriteSummary,
    view::{LatestView, SequentialState, ViewState},
};
use aptos_aggregator::{
    delayed_change::{ApplyBase, DelayedChange},
    types::{code_invariant_error, expect_ok},
};
use aptos_logger::{error, info};
use aptos_mvhashmap::{
    types::{TxnIndex, ValueWithLayout},
    unsync_map::UnsyncMap,
};
use aptos_types::{
    block_executor::config::BlockExecutorConfig,
    executable::Executable,
    state_store::{state_value::StateValue, TStateView},
    transaction::{BlockExecutableTransaction as Transaction, BlockOutput},
    write_set::TransactionWrite,
};
use aptos_vm_logging::{alert, init_speculative_logs, prelude::*};
use aptos_vm_types::change_set::randomly_check_layout_matches;
use bytes::Bytes;
use claims::assert_none;
use core::panic;
use fail::fail_point;
use move_core_types::{value::MoveTypeLayout, vm_status::StatusCode};
use num_cpus;
use std::{
    cell::RefCell,
    collections::{BTreeMap, HashMap},
    marker::{PhantomData, Sync},
    sync::Arc,
};

pub struct BlockExecutor<T, E, S, L, X> {
    // Number of active concurrent tasks, corresponding to the maximum number of rayon
    // threads that may be concurrently participating in parallel execution.
    config: BlockExecutorConfig,
    transaction_commit_hook: Option<L>,
    phantom: PhantomData<(T, E, S, L, X)>,
}

impl<T, E, S, L, X> BlockExecutor<T, E, S, L, X>
where
    T: Transaction,
    E: ExecutorTask<Txn = T>,
    S: TStateView<Key = T::Key> + Sync,
    L: TransactionCommitHook<Output = E::Output>,
    X: Executable + 'static,
{
    /// The caller needs to ensure that concurrency_level > 1 (0 is illegal and 1 should
    /// be handled by sequential execution) and that concurrency_level <= num_cpus.
    pub fn new(config: BlockExecutorConfig, transaction_commit_hook: Option<L>) -> Self {
        assert!(
            config.local.concurrency_level > 0 && config.local.concurrency_level <= num_cpus::get(),
            "Parallel execution concurrency level {} should be between 1 and number of CPUs",
            config.local.concurrency_level
        );
        if config.local.concurrency_level != 1 {
            info!("Parallel execution is disabled in this implementation");
        }
        Self {
            config,
            transaction_commit_hook,
            phantom: PhantomData,
        }
    }

    fn apply_output_sequential(
        unsync_map: &UnsyncMap<T::Key, T::Tag, T::Value, X, T::Identifier>,
        output: &E::Output,
        resource_write_set: Vec<(T::Key, Arc<T::Value>, Option<Arc<MoveTypeLayout>>)>,
    ) -> Result<(), SequentialBlockExecutionError<E::Error>> {
        for (key, write_op, layout) in resource_write_set.into_iter() {
            unsync_map.write(key, write_op, layout);
        }

        for (group_key, metadata_op, group_ops) in output.resource_group_write_set().into_iter() {
            for (value_tag, (group_op, maybe_layout)) in group_ops.into_iter() {
                unsync_map.insert_group_op(&group_key, value_tag, group_op, maybe_layout)?;
            }
            unsync_map.write(group_key, Arc::new(metadata_op), None);
        }

        for (key, write_op) in output.aggregator_v1_write_set().into_iter() {
            unsync_map.write(key, Arc::new(write_op), None);
        }

        for (key, write_op) in output.module_write_set().into_iter() {
            unsync_map.write_module(key, write_op);
        }

        let mut second_phase = Vec::new();
        let mut updates = HashMap::new();
        for (id, change) in output.delayed_field_change_set().into_iter() {
            match change {
                DelayedChange::Create(value) => {
                    assert_none!(
                        unsync_map.fetch_delayed_field(&id),
                        "Sequential execution must not create duplicate aggregators"
                    );
                    updates.insert(id, value);
                },
                DelayedChange::Apply(apply) => {
                    match apply.get_apply_base_id(&id) {
                        ApplyBase::Previous(base_id) => {
                            updates.insert(
                                id,
                                expect_ok(apply.apply_to_base(
                                    unsync_map.fetch_delayed_field(&base_id).unwrap(),
                                ))
                                .unwrap(),
                            );
                        },
                        ApplyBase::Current(base_id) => {
                            second_phase.push((id, base_id, apply));
                        },
                    };
                },
            }
        }
        for (id, base_id, apply) in second_phase.into_iter() {
            updates.insert(
                id,
                expect_ok(
                    apply.apply_to_base(
                        updates
                            .get(&base_id)
                            .cloned()
                            .unwrap_or_else(|| unsync_map.fetch_delayed_field(&base_id).unwrap()),
                    ),
                )
                .unwrap(),
            );
        }
        for (id, value) in updates.into_iter() {
            unsync_map.write_delayed_field(id, value);
        }

        Ok(())
    }

    pub(crate) fn execute_transactions_sequential(
        &self,
        executor_arguments: E::Argument,
        signature_verified_block: &[T],
        base_view: &S,
        resource_group_bcs_fallback: bool,
    ) -> Result<BlockOutput<E::Output>, SequentialBlockExecutionError<E::Error>> {
        let num_txns = signature_verified_block.len();
        let init_timer = VM_INIT_SECONDS.start_timer();
        let executor = E::init(executor_arguments);
        drop(init_timer);

        let start_counter = gen_id_start_value(true);
        let counter = RefCell::new(start_counter);
        let unsync_map = UnsyncMap::new();
        let mut ret = Vec::with_capacity(num_txns);
        let mut block_limit_processor = BlockGasLimitProcessor::<T>::new(
            self.config.onchain.block_gas_limit_type.clone(),
            num_txns,
        );

        let last_input_output: TxnLastInputOutput<T, E::Output, E::Error> =
            TxnLastInputOutput::new(num_txns as TxnIndex);

        for (idx, txn) in signature_verified_block.iter().enumerate() {
            let latest_view = LatestView::<T, S, X>::new(
                base_view,
                ViewState::Unsync(SequentialState::new(&unsync_map, start_counter, &counter)),
                idx as TxnIndex,
            );
            let res = executor.execute_transaction(&latest_view, txn, idx as TxnIndex);
            let must_skip = matches!(res, ExecutionStatus::SkipRest(_));
            match res {
                ExecutionStatus::Abort(err) => {
                    if let Some(commit_hook) = &self.transaction_commit_hook {
                        commit_hook.on_execution_aborted(idx as TxnIndex);
                    }
                    error!(
                        "Sequential execution FatalVMError by transaction {}",
                        idx as TxnIndex
                    );
                    // Record the status indicating the unrecoverable VM failure.
                    return Err(SequentialBlockExecutionError::ErrorToReturn(
                        BlockExecutionError::FatalVMError(err),
                    ));
                },
                ExecutionStatus::DelayedFieldsCodeInvariantError(msg) => {
                    if let Some(commit_hook) = &self.transaction_commit_hook {
                        commit_hook.on_execution_aborted(idx as TxnIndex);
                    }
                    alert!("Sequential execution DelayedFieldsCodeInvariantError error by transaction {}: {}", idx as TxnIndex, msg);
                    return Err(SequentialBlockExecutionError::ErrorToReturn(
                        BlockExecutionError::FatalBlockExecutorError(code_invariant_error(msg)),
                    ));
                },
                ExecutionStatus::SpeculativeExecutionAbortError(msg) => {
                    if let Some(commit_hook) = &self.transaction_commit_hook {
                        commit_hook.on_execution_aborted(idx as TxnIndex);
                    }
                    alert!("Sequential execution SpeculativeExecutionAbortError error by transaction {}: {}", idx as TxnIndex, msg);
                    return Err(SequentialBlockExecutionError::ErrorToReturn(
                        BlockExecutionError::FatalBlockExecutorError(code_invariant_error(msg)),
                    ));
                },
                ExecutionStatus::Success(output) | ExecutionStatus::SkipRest(output) => {
                    // Calculating the accumulated gas costs of the committed txns.
                    let fee_statement = output.fee_statement();

                    let approx_output_size = self
                        .config
                        .onchain
                        .block_gas_limit_type
                        .block_output_limit()
                        .map(|_| {
                            output.output_approx_size()
                                + if self
                                    .config
                                    .onchain
                                    .block_gas_limit_type
                                    .include_user_txn_size_in_block_output()
                                {
                                    txn.user_txn_bytes_len()
                                } else {
                                    0
                                } as u64
                        });

                    let sequential_reads = latest_view.take_sequential_reads();
                    let read_write_summary = self
                        .config
                        .onchain
                        .block_gas_limit_type
                        .conflict_penalty_window()
                        .map(|_| {
                            ReadWriteSummary::new(
                                sequential_reads.get_read_summary(),
                                output.get_write_summary(),
                            )
                        });

                    if last_input_output.check_and_append_module_rw_conflict(
                        sequential_reads.module_reads.iter(),
                        output.module_write_set().keys(),
                    ) {
                        block_limit_processor.process_module_rw_conflict();
                    }

                    block_limit_processor.accumulate_fee_statement(
                        fee_statement,
                        read_write_summary,
                        approx_output_size,
                    );

                    output.materialize_agg_v1(&latest_view);
                    assert_eq!(
                        output.aggregator_v1_delta_set().len(),
                        0,
                        "Sequential execution must materialize deltas"
                    );

                    if resource_group_bcs_fallback {
                        // Dynamic change set optimizations are enabled, and resource group serialization
                        // previously failed in bcs serialization for preparing final transaction outputs.
                        // TODO: remove this fallback when txn errors can be created from block executor.

                        let finalize = |group_key| -> BTreeMap<_, _> {
                            unsync_map
                                .finalize_group(&group_key)
                                .map(|(resource_tag, value_with_layout)| {
                                    let value = match value_with_layout {
                                        ValueWithLayout::RawFromStorage(value)
                                        | ValueWithLayout::Exchanged(value, _) => value,
                                    };
                                    (
                                        resource_tag,
                                        value
                                            .extract_raw_bytes()
                                            .expect("Deletions should already be applied"),
                                    )
                                })
                                .collect()
                        };

                        // The IDs are not exchanged but it doesn't change the types (Bytes) or size.
                        let serialization_error = output
                            .group_reads_needing_delayed_field_exchange()
                            .iter()
                            .any(|(group_key, _)| {
                                fail_point!("fail-point-resource-group-serialization", |_| {
                                    true
                                });

                                let finalized_group = finalize(group_key.clone());
                                bcs::to_bytes(&finalized_group).is_err()
                            })
                            || output.resource_group_write_set().into_iter().any(
                                |(group_key, _, group_ops)| {
                                    fail_point!("fail-point-resource-group-serialization", |_| {
                                        true
                                    });

                                    let mut finalized_group = finalize(group_key);
                                    for (value_tag, (group_op, _)) in group_ops {
                                        if group_op.is_deletion() {
                                            finalized_group.remove(&value_tag);
                                        } else {
                                            finalized_group.insert(
                                                value_tag,
                                                group_op
                                                    .extract_raw_bytes()
                                                    .expect("Not a deletion"),
                                            );
                                        }
                                    }
                                    bcs::to_bytes(&finalized_group).is_err()
                                },
                            );

                        if serialization_error {
                            // The corresponding error / alert must already be triggered, the goal in sequential
                            // fallback is to just skip any transactions that would cause such serialization errors.
                            alert!("Discarding transaction because serialization failed in bcs fallback");
                            ret.push(E::Output::discard_output(
                                StatusCode::DELAYED_MATERIALIZATION_CODE_INVARIANT_ERROR,
                            ));
                            continue;
                        }
                    };

                    // Apply the writes.
                    let resource_write_set = output.resource_write_set();
                    Self::apply_output_sequential(
                        &unsync_map,
                        &output,
                        resource_write_set.clone(),
                    )?;

                    // If dynamic change set materialization part (indented for clarity/variable scope):
                    {
                        let finalized_groups = groups_to_finalize!(output,)
                            .map(|((group_key, metadata_op), is_read_needing_exchange)| {
                                let finalized_group =
                                    Ok(unsync_map.finalize_group(&group_key).collect());
                                map_finalized_group::<T>(
                                    group_key,
                                    finalized_group,
                                    metadata_op,
                                    is_read_needing_exchange,
                                )
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        let materialized_finalized_groups =
                            map_id_to_values_in_group_writes(finalized_groups, &latest_view)?;
                        let serialized_groups =
                            serialize_groups::<T>(materialized_finalized_groups).map_err(|_| {
                                SequentialBlockExecutionError::ResourceGroupSerializationError
                            })?;

                        let resource_writes_to_materialize = resource_writes_to_materialize!(
                            resource_write_set,
                            output,
                            unsync_map,
                        )?;
                        // Replace delayed field id with values in resource write set and read set.
                        let materialized_resource_write_set = map_id_to_values_in_write_set(
                            resource_writes_to_materialize,
                            &latest_view,
                        )?;

                        // Replace delayed field id with values in events
                        let materialized_events = map_id_to_values_events(
                            Box::new(output.get_events().into_iter()),
                            &latest_view,
                        )?;

                        output.incorporate_materialized_txn_output(
                            // No aggregator v1 delta writes are needed for sequential execution.
                            // They are already handled because we passed materialize_deltas=true
                            // to execute_transaction.
                            vec![],
                            materialized_resource_write_set
                                .into_iter()
                                .chain(serialized_groups.into_iter())
                                .collect(),
                            materialized_events,
                        )?;
                    }
                    // If dynamic change set is disabled, this can be used to assert nothing needs patching instead:
                    //   output.set_txn_output_for_non_dynamic_change_set();

                    if latest_view.is_incorrect_use() {
                        return Err(
                            code_invariant_error("Incorrect use in sequential execution").into(),
                        );
                    }

                    if let Some(commit_hook) = &self.transaction_commit_hook {
                        commit_hook.on_transaction_committed(idx as TxnIndex, &output);
                    }
                    ret.push(output);
                },
            };
            // When the txn is a SkipRest txn, halt sequential execution.
            if must_skip {
                break;
            }

            if idx < num_txns - 1 && block_limit_processor.should_end_block_sequential() {
                break;
            }
        }

        block_limit_processor
            .finish_sequential_update_counters_and_log_info(ret.len() as u32, num_txns as u32);

        ret.resize_with(num_txns, E::Output::skip_output);

        counters::update_state_counters(unsync_map.stats(), false);

        // TODO add block end info to output.
        // block_limit_processor.is_block_limit_reached();

        Ok(BlockOutput::new(ret))
    }

    pub fn execute_block(
        &self,
        executor_arguments: E::Argument,
        signature_verified_block: &[T],
        base_view: &S,
    ) -> BlockExecutionResult<BlockOutput<E::Output>, E::Error> {
        // Run sequential
        // TODO: restore parallel execution from upstream under a feature gate
        let sequential_result = self.execute_transactions_sequential(
            executor_arguments,
            signature_verified_block,
            base_view,
            false,
        );

        // If sequential gave us result, return it
        let sequential_error = match sequential_result {
            Ok(output) => {
                return Ok(output);
            },
            Err(SequentialBlockExecutionError::ResourceGroupSerializationError) => {
                if !self.config.local.allow_fallback {
                    panic!("Parallel execution failed and fallback is not allowed");
                }

                // TODO[agg_v2](cleanup): check if sequential execution logs anything in the speculative logs,
                // and whether clearing them below is needed at all.
                // All logs from the first pass of sequential execution should be cleared and not reported.
                // Clear by re-initializing the speculative logs.
                init_speculative_logs(signature_verified_block.len());

                let sequential_result = self.execute_transactions_sequential(
                    executor_arguments,
                    signature_verified_block,
                    base_view,
                    true,
                );

                // If sequential gave us result, return it
                match sequential_result {
                    Ok(output) => {
                        return Ok(output);
                    },
                    Err(SequentialBlockExecutionError::ResourceGroupSerializationError) => {
                        BlockExecutionError::FatalBlockExecutorError(code_invariant_error(
                            "resource group serialization during bcs fallback should not happen",
                        ))
                    },
                    Err(SequentialBlockExecutionError::ErrorToReturn(err)) => err,
                }
            },
            Err(SequentialBlockExecutionError::ErrorToReturn(err)) => err,
        };

        if self.config.local.discard_failed_blocks {
            // We cannot execute block, discard everything (including block metadata and validator transactions)
            // (TODO: maybe we should add fallback here to first try BlockMetadataTransaction alone)
            // StateCheckpoint will be added afterwards.
            let error_code = match sequential_error {
                BlockExecutionError::FatalBlockExecutorError(_) => {
                    StatusCode::DELAYED_MATERIALIZATION_CODE_INVARIANT_ERROR
                },
                BlockExecutionError::FatalVMError(_) => {
                    StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR
                },
            };
            let ret = signature_verified_block
                .iter()
                .map(|_| E::Output::discard_output(error_code))
                .collect();
            return Ok(BlockOutput::new(ret));
        }

        Err(sequential_error)
    }
}
