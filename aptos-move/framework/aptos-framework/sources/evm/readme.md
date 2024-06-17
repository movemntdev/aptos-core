### Move EVM Runtime

The Move EVM implements the EVM opcode, providing full compatibility with EVM. It allows for direct deployment and execution of Solidity code on Move, such as [Uniswap v3](https://github.com/Uniswap/deploy-v3).

### Implementation Details

The [Move EVM](https://github.com/movemntdev/movement-v2/tree/main/aptos-move/framework/aptos-framework/sources/evm) includes the following four files:

```txt
├── decode.move  # EVM RLP decoding
├── encode.move  # EVM RLP encoding
├── evm.move     # EVM opcode and stack implementation
└── util.move    # Data transformation

```
Each Ethereum address is mapped to a key pair of a move account, owned by the EVM contract. The `evm.move` primarily provides the following interfaces:

1. The `send_tx` method is provided for writing data. It takes the following parameters:

- `sender`: The signer address for the account sending to the EVM. It proxies the transaction as the transaction content will undergo RLP decoding and signature verification in the EVM. Any account holding MOVE tokens can use this.
- `evm_from`: The address of the account used for signing in the EVM.
- `tx`: The original RLP data obtained after signing with a private key in the EVM.
- `gas_bytes`: The amount of gas to be deducted from `evm_from` for this transaction.
- `tx_type`: The transaction type, currently a fixed value of 1.

```move
    public entry fun send_tx(
        sender: &signer,
        evm_from: vector<u8>,
        tx: vector<u8>,
        gas_bytes: vector<u8>,
        tx_type: u64,
    )
```

2. A method similar to `eth_estimateGas` is provided, which omits RLP decoding and signature verification compared to `send_tx`.

```
 public entry fun estimate_tx_gas(
        evm_from: vector<u8>,
        evm_to: vector<u8>,
        data: vector<u8>,
        value_bytes: vector<u8>,
        tx_type: u64,
    )
```

3. Bridge functionality is provided to convert Move's native tokens into EVM's native tokens.

- `sender`: The account used to convert Move tokens into EVM's native tokens.
- `evm_addr`: The Ethereum address format used to receive native tokens in the EVM.
- `amount_bytes`: The quantity of tokens to bridge (with 18 decimal precision).

```
public entry fun deposit(sender: &signer, evm_addr: vector<u8>, amount_bytes: vector<u8>)

```

4. Bridge EVM's native tokens to Move native tokens  
We have set up a contract at `0x000000000000000000000000000000000000000000000000` that provides a function with the following signature:
- to: The address in Move format to receive the tokens.
- amount: The amount of tokens to transfer (with 18 decimal places precision).

```solidity
 function withdraw(bytes memory to , uint amount) external;
```

5. A function to get the corresponding Move format address from an EVM format address.

- `evm_addr`: The EVM format address.

```
public fun get_move_address(evm_addr: vector<u8>)
```

6. A function to read data from an EVM contract.

- `sender`: The EVM format address (from).
- `contract_addr`: The EVM format address (to).
- `data`: The method to read from the contract, such as the encoding of totalSupply().

```
public fun query(sender:vector<u8>, contract_addr: vector<u8>, data: vector<u8>):
```

7. A function to implement the EVM's `getStorageAt` RPC.

-   `addr` The EVM format address.
-   `slot` index

```
public fun get_storage_at(addr: vector<u8>, slot: vector<u8>)
```
8. A function to get basic account information.

First, use `get_move_address` to convert the EVM address to a Move address. Then, get the EVM's account resource through Move. The nonce and balance are usually the main points of interest.
```
  struct Account has key {
        balance: u256,
        nonce: u64,
        is_contract: bool,
        code: vector<u8>,
        storage: Table<u256, vector<u8>>,
    }

```


### Move EVM RPC Implementation
Direct interaction with the MOVE EVM can lead to significant usage costs. Therefore, we provide a fluffy EVM RPC repo. After starting according to the instructions, you can complete the use of MOVE EVM [MOVE EVM RPC](https://github.com/movemntdev/movement-evm-rpc-v2)