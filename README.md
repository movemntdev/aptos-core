### Build Steps

> Requirement: Ubuntu 20.04

### Configure the Environment

To set up the necessary environment, run the following command:
```
chmod +x ./scripts/dev_setup.sh
./scripts/dev_setup.sh
```

### Build from Source

To build from the source code, execute the following command:
```
cargo build -p subnet
# The built binary will be located at target/debug/subnet
```