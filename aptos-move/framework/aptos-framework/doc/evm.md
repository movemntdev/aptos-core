
<a id="0x1_evm"></a>

# Module `0x1::evm`



-  [Resource `Account`](#0x1_evm_Account)
-  [Struct `Log0Event`](#0x1_evm_Log0Event)
-  [Struct `Log1Event`](#0x1_evm_Log1Event)
-  [Struct `Log2Event`](#0x1_evm_Log2Event)
-  [Struct `Log3Event`](#0x1_evm_Log3Event)
-  [Struct `Log4Event`](#0x1_evm_Log4Event)
-  [Resource `ContractEvent`](#0x1_evm_ContractEvent)
-  [Constants](#@Constants_0)
-  [Function `revert`](#0x1_evm_revert)
-  [Function `decode_raw_tx`](#0x1_evm_decode_raw_tx)
-  [Function `mul_mod`](#0x1_evm_mul_mod)
-  [Function `add`](#0x1_evm_add)
-  [Function `sub`](#0x1_evm_sub)
-  [Function `mul`](#0x1_evm_mul)
-  [Function `exp`](#0x1_evm_exp)
-  [Function `send_tx`](#0x1_evm_send_tx)
-  [Function `estimate_tx_gas`](#0x1_evm_estimate_tx_gas)
-  [Function `deposit`](#0x1_evm_deposit)
-  [Function `get_code`](#0x1_evm_get_code)
-  [Function `get_move_address`](#0x1_evm_get_move_address)
-  [Function `query`](#0x1_evm_query)
-  [Function `get_storage_at`](#0x1_evm_get_storage_at)
-  [Function `handle_exdlecute_result`](#0x1_evm_handle_exdlecute_result)
-  [Function `throw_error`](#0x1_evm_throw_error)
-  [Function `execute`](#0x1_evm_execute)
-  [Function `precompile`](#0x1_evm_precompile)
-  [Function `run`](#0x1_evm_run)
-  [Function `exist_contract`](#0x1_evm_exist_contract)
-  [Function `add_balance`](#0x1_evm_add_balance)
-  [Function `transfer_from_move_addr`](#0x1_evm_transfer_from_move_addr)
-  [Function `transfer_to_evm_addr`](#0x1_evm_transfer_to_evm_addr)
-  [Function `transfer_to_move_addr`](#0x1_evm_transfer_to_move_addr)
-  [Function `create_event_if_not_exist`](#0x1_evm_create_event_if_not_exist)
-  [Function `create2_address`](#0x1_evm_create2_address)
-  [Function `create_account_if_not_exist`](#0x1_evm_create_account_if_not_exist)
-  [Function `verify_nonce`](#0x1_evm_verify_nonce)
-  [Function `verify_signature`](#0x1_evm_verify_signature)


<pre><code><b>use</b> <a href="account.md#0x1_account">0x1::account</a>;
<b>use</b> <a href="aptos_account.md#0x1_aptos_account">0x1::aptos_account</a>;
<b>use</b> <a href="aptos_coin.md#0x1_aptos_coin">0x1::aptos_coin</a>;
<b>use</b> <a href="../../aptos-stdlib/../move-stdlib/doc/hash.md#0x1_aptos_hash">0x1::aptos_hash</a>;
<b>use</b> <a href="block.md#0x1_block">0x1::block</a>;
<b>use</b> <a href="coin.md#0x1_coin">0x1::coin</a>;
<b>use</b> <a href="create_signer.md#0x1_create_signer">0x1::create_signer</a>;
<b>use</b> <a href="../../aptos-stdlib/doc/debug.md#0x1_debug">0x1::debug</a>;
<b>use</b> <a href="event.md#0x1_event">0x1::event</a>;
<b>use</b> <a href="arithmetic.md#0x1_evm_arithmetic">0x1::evm_arithmetic</a>;
<b>use</b> <a href="util.md#0x1_evm_util">0x1::evm_util</a>;
<b>use</b> <a href="../../aptos-stdlib/doc/from_bcs.md#0x1_from_bcs">0x1::from_bcs</a>;
<b>use</b> <a href="../../aptos-stdlib/../move-stdlib/doc/option.md#0x1_option">0x1::option</a>;
<b>use</b> <a href="precompile.md#0x1_precompile">0x1::precompile</a>;
<b>use</b> <a href="../../aptos-stdlib/doc/secp256k1.md#0x1_secp256k1">0x1::secp256k1</a>;
<b>use</b> <a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">0x1::signer</a>;
<b>use</b> <a href="../../aptos-stdlib/doc/simple_map.md#0x1_simple_map">0x1::simple_map</a>;
<b>use</b> <a href="../../aptos-stdlib/../move-stdlib/doc/string.md#0x1_string">0x1::string</a>;
<b>use</b> <a href="../../aptos-stdlib/doc/table.md#0x1_table">0x1::table</a>;
<b>use</b> <a href="timestamp.md#0x1_timestamp">0x1::timestamp</a>;
<b>use</b> <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">0x1::vector</a>;
</code></pre>



<a id="0x1_evm_Account"></a>

## Resource `Account`



<pre><code><b>struct</b> <a href="evm.md#0x1_evm_Account">Account</a> <b>has</b> key
</code></pre>



<details>
<summary>Fields</summary>


<dl>
<dt>
<code>balance: u256</code>
</dt>
<dd>

</dd>
<dt>
<code>nonce: u64</code>
</dt>
<dd>

</dd>
<dt>
<code>is_contract: bool</code>
</dt>
<dd>

</dd>
<dt>
<code><a href="code.md#0x1_code">code</a>: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;</code>
</dt>
<dd>

</dd>
<dt>
<code>storage: <a href="../../aptos-stdlib/doc/table.md#0x1_table_Table">table::Table</a>&lt;u256, <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;&gt;</code>
</dt>
<dd>

</dd>
</dl>


</details>

<a id="0x1_evm_Log0Event"></a>

## Struct `Log0Event`



<pre><code><b>struct</b> <a href="evm.md#0x1_evm_Log0Event">Log0Event</a> <b>has</b> drop, store
</code></pre>



<details>
<summary>Fields</summary>


<dl>
<dt>
<code>contract: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;</code>
</dt>
<dd>

</dd>
<dt>
<code>data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;</code>
</dt>
<dd>

</dd>
</dl>


</details>

<a id="0x1_evm_Log1Event"></a>

## Struct `Log1Event`



<pre><code><b>struct</b> <a href="evm.md#0x1_evm_Log1Event">Log1Event</a> <b>has</b> drop, store
</code></pre>



<details>
<summary>Fields</summary>


<dl>
<dt>
<code>contract: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;</code>
</dt>
<dd>

</dd>
<dt>
<code>data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;</code>
</dt>
<dd>

</dd>
<dt>
<code>topic0: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;</code>
</dt>
<dd>

</dd>
</dl>


</details>

<a id="0x1_evm_Log2Event"></a>

## Struct `Log2Event`



<pre><code><b>struct</b> <a href="evm.md#0x1_evm_Log2Event">Log2Event</a> <b>has</b> drop, store
</code></pre>



<details>
<summary>Fields</summary>


<dl>
<dt>
<code>contract: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;</code>
</dt>
<dd>

</dd>
<dt>
<code>data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;</code>
</dt>
<dd>

</dd>
<dt>
<code>topic0: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;</code>
</dt>
<dd>

</dd>
<dt>
<code>topic1: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;</code>
</dt>
<dd>

</dd>
</dl>


</details>

<a id="0x1_evm_Log3Event"></a>

## Struct `Log3Event`



<pre><code><b>struct</b> <a href="evm.md#0x1_evm_Log3Event">Log3Event</a> <b>has</b> drop, store
</code></pre>



<details>
<summary>Fields</summary>


<dl>
<dt>
<code>contract: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;</code>
</dt>
<dd>

</dd>
<dt>
<code>data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;</code>
</dt>
<dd>

</dd>
<dt>
<code>topic0: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;</code>
</dt>
<dd>

</dd>
<dt>
<code>topic1: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;</code>
</dt>
<dd>

</dd>
<dt>
<code>topic2: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;</code>
</dt>
<dd>

</dd>
</dl>


</details>

<a id="0x1_evm_Log4Event"></a>

## Struct `Log4Event`



<pre><code><b>struct</b> <a href="evm.md#0x1_evm_Log4Event">Log4Event</a> <b>has</b> drop, store
</code></pre>



<details>
<summary>Fields</summary>


<dl>
<dt>
<code>contract: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;</code>
</dt>
<dd>

</dd>
<dt>
<code>data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;</code>
</dt>
<dd>

</dd>
<dt>
<code>topic0: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;</code>
</dt>
<dd>

</dd>
<dt>
<code>topic1: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;</code>
</dt>
<dd>

</dd>
<dt>
<code>topic2: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;</code>
</dt>
<dd>

</dd>
<dt>
<code>topic3: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;</code>
</dt>
<dd>

</dd>
</dl>


</details>

<a id="0x1_evm_ContractEvent"></a>

## Resource `ContractEvent`



<pre><code><b>struct</b> <a href="evm.md#0x1_evm_ContractEvent">ContractEvent</a> <b>has</b> key
</code></pre>



<details>
<summary>Fields</summary>


<dl>
<dt>
<code>log0Event: <a href="event.md#0x1_event_EventHandle">event::EventHandle</a>&lt;<a href="evm.md#0x1_evm_Log0Event">evm::Log0Event</a>&gt;</code>
</dt>
<dd>

</dd>
<dt>
<code>log1Event: <a href="event.md#0x1_event_EventHandle">event::EventHandle</a>&lt;<a href="evm.md#0x1_evm_Log1Event">evm::Log1Event</a>&gt;</code>
</dt>
<dd>

</dd>
<dt>
<code>log2Event: <a href="event.md#0x1_event_EventHandle">event::EventHandle</a>&lt;<a href="evm.md#0x1_evm_Log2Event">evm::Log2Event</a>&gt;</code>
</dt>
<dd>

</dd>
<dt>
<code>log3Event: <a href="event.md#0x1_event_EventHandle">event::EventHandle</a>&lt;<a href="evm.md#0x1_evm_Log3Event">evm::Log3Event</a>&gt;</code>
</dt>
<dd>

</dd>
<dt>
<code>log4Event: <a href="event.md#0x1_event_EventHandle">event::EventHandle</a>&lt;<a href="evm.md#0x1_evm_Log4Event">evm::Log4Event</a>&gt;</code>
</dt>
<dd>

</dd>
</dl>


</details>

<a id="@Constants_0"></a>

## Constants


<a id="0x1_evm_U256_MAX"></a>



<pre><code><b>const</b> <a href="evm.md#0x1_evm_U256_MAX">U256_MAX</a>: u256 = 115792089237316195423570985008687907853269984665640564039457584007913129639935;
</code></pre>



<a id="0x1_evm_ACCOUNT_NOT_EXIST"></a>



<pre><code><b>const</b> <a href="evm.md#0x1_evm_ACCOUNT_NOT_EXIST">ACCOUNT_NOT_EXIST</a>: u64 = 10008;
</code></pre>



<a id="0x1_evm_ADDR_LENGTH"></a>



<pre><code><b>const</b> <a href="evm.md#0x1_evm_ADDR_LENGTH">ADDR_LENGTH</a>: u64 = 10001;
</code></pre>



<a id="0x1_evm_CHAIN_ID"></a>



<pre><code><b>const</b> <a href="evm.md#0x1_evm_CHAIN_ID">CHAIN_ID</a>: u64 = 336;
</code></pre>



<a id="0x1_evm_CHAIN_ID_BYTES"></a>



<pre><code><b>const</b> <a href="evm.md#0x1_evm_CHAIN_ID_BYTES">CHAIN_ID_BYTES</a>: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; = [1, 80];
</code></pre>



<a id="0x1_evm_CONTRACT_DEPLOYED"></a>



<pre><code><b>const</b> <a href="evm.md#0x1_evm_CONTRACT_DEPLOYED">CONTRACT_DEPLOYED</a>: u64 = 10006;
</code></pre>



<a id="0x1_evm_CONTRACT_READ_ONLY"></a>



<pre><code><b>const</b> <a href="evm.md#0x1_evm_CONTRACT_READ_ONLY">CONTRACT_READ_ONLY</a>: u64 = 10005;
</code></pre>



<a id="0x1_evm_CONVERT_BASE"></a>



<pre><code><b>const</b> <a href="evm.md#0x1_evm_CONVERT_BASE">CONVERT_BASE</a>: u256 = 10000000000;
</code></pre>



<a id="0x1_evm_INSUFFIENT_BALANCE"></a>



<pre><code><b>const</b> <a href="evm.md#0x1_evm_INSUFFIENT_BALANCE">INSUFFIENT_BALANCE</a>: u64 = 10003;
</code></pre>



<a id="0x1_evm_INVALID_CHAINID"></a>

invalid chain id in raw tx


<pre><code><b>const</b> <a href="evm.md#0x1_evm_INVALID_CHAINID">INVALID_CHAINID</a>: u64 = 10009;
</code></pre>



<a id="0x1_evm_NONCE"></a>



<pre><code><b>const</b> <a href="evm.md#0x1_evm_NONCE">NONCE</a>: u64 = 10004;
</code></pre>



<a id="0x1_evm_ONE_ADDR"></a>



<pre><code><b>const</b> <a href="evm.md#0x1_evm_ONE_ADDR">ONE_ADDR</a>: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
</code></pre>



<a id="0x1_evm_SIGNATURE"></a>



<pre><code><b>const</b> <a href="evm.md#0x1_evm_SIGNATURE">SIGNATURE</a>: u64 = 10002;
</code></pre>



<a id="0x1_evm_TX_NOT_SUPPORT"></a>



<pre><code><b>const</b> <a href="evm.md#0x1_evm_TX_NOT_SUPPORT">TX_NOT_SUPPORT</a>: u64 = 10007;
</code></pre>



<a id="0x1_evm_ZERO_ADDR"></a>



<pre><code><b>const</b> <a href="evm.md#0x1_evm_ZERO_ADDR">ZERO_ADDR</a>: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
</code></pre>



<a id="0x1_evm_revert"></a>

## Function `revert`



<pre><code><b>fun</b> <a href="evm.md#0x1_evm_revert">revert</a>(message: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>native</b> <b>fun</b> <a href="evm.md#0x1_evm_revert">revert</a>(
    message: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
);
</code></pre>



</details>

<a id="0x1_evm_decode_raw_tx"></a>

## Function `decode_raw_tx`



<pre><code><b>fun</b> <a href="evm.md#0x1_evm_decode_raw_tx">decode_raw_tx</a>(raw_tx: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): (u64, u64, <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, u256, <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>native</b> <b>fun</b> <a href="evm.md#0x1_evm_decode_raw_tx">decode_raw_tx</a>(
    raw_tx: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
): (u64, u64, <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, u256, <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;);
</code></pre>



</details>

<a id="0x1_evm_mul_mod"></a>

## Function `mul_mod`



<pre><code><b>fun</b> <a href="evm.md#0x1_evm_mul_mod">mul_mod</a>(a: u256, b: u256, n: u256): u256
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>native</b> <b>fun</b> <a href="evm.md#0x1_evm_mul_mod">mul_mod</a>(a: u256, b: u256, n: u256): u256;
</code></pre>



</details>

<a id="0x1_evm_add"></a>

## Function `add`



<pre><code><b>fun</b> <a href="evm.md#0x1_evm_add">add</a>(a: u256, b: u256): u256
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>native</b> <b>fun</b> <a href="evm.md#0x1_evm_add">add</a>(a: u256, b: u256): u256;
</code></pre>



</details>

<a id="0x1_evm_sub"></a>

## Function `sub`



<pre><code><b>fun</b> <a href="evm.md#0x1_evm_sub">sub</a>(a: u256, b: u256): u256
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>native</b> <b>fun</b> <a href="evm.md#0x1_evm_sub">sub</a>(a: u256, b: u256): u256;
</code></pre>



</details>

<a id="0x1_evm_mul"></a>

## Function `mul`



<pre><code><b>fun</b> <a href="evm.md#0x1_evm_mul">mul</a>(a: u256, b: u256): u256
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>native</b> <b>fun</b> <a href="evm.md#0x1_evm_mul">mul</a>(a: u256, b: u256): u256;
</code></pre>



</details>

<a id="0x1_evm_exp"></a>

## Function `exp`



<pre><code><b>fun</b> <a href="evm.md#0x1_evm_exp">exp</a>(a: u256, b: u256): u256
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>native</b> <b>fun</b> <a href="evm.md#0x1_evm_exp">exp</a>(a: u256, b: u256): u256;
</code></pre>



</details>

<a id="0x1_evm_send_tx"></a>

## Function `send_tx`



<pre><code><b>public</b> entry <b>fun</b> <a href="evm.md#0x1_evm_send_tx">send_tx</a>(sender: &<a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a>, _evm_from: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, tx: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, gas_bytes: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, _tx_type: u64)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> entry <b>fun</b> <a href="evm.md#0x1_evm_send_tx">send_tx</a>(
    sender: &<a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a>,
    _evm_from: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;,
    tx: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;,
    gas_bytes: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;,
    _tx_type: u64,
) <b>acquires</b> <a href="evm.md#0x1_evm_Account">Account</a>, <a href="evm.md#0x1_evm_ContractEvent">ContractEvent</a> {
    <b>let</b> gas = to_u256(gas_bytes);
    <b>let</b> (<a href="chain_id.md#0x1_chain_id">chain_id</a>, nonce, evm_from, evm_to, value, data) = <a href="evm.md#0x1_evm_decode_raw_tx">decode_raw_tx</a>(tx);
    <b>assert</b>!(<a href="chain_id.md#0x1_chain_id">chain_id</a> == <a href="evm.md#0x1_evm_CHAIN_ID">CHAIN_ID</a> || <a href="chain_id.md#0x1_chain_id">chain_id</a> == 0, <a href="evm.md#0x1_evm_INVALID_CHAINID">INVALID_CHAINID</a>);
    <a href="evm.md#0x1_evm_execute">execute</a>(to_32bit(evm_from), to_32bit(evm_to), nonce, data, value);
    <a href="evm.md#0x1_evm_transfer_to_move_addr">transfer_to_move_addr</a>(to_32bit(evm_from), address_of(sender), gas * <a href="evm.md#0x1_evm_CONVERT_BASE">CONVERT_BASE</a>);
}
</code></pre>



</details>

<a id="0x1_evm_estimate_tx_gas"></a>

## Function `estimate_tx_gas`



<pre><code><b>public</b> entry <b>fun</b> <a href="evm.md#0x1_evm_estimate_tx_gas">estimate_tx_gas</a>(evm_from: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, evm_to: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, value_bytes: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, _tx_type: u64)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> entry <b>fun</b> <a href="evm.md#0x1_evm_estimate_tx_gas">estimate_tx_gas</a>(
    evm_from: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;,
    evm_to: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;,
    data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;,
    value_bytes: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;,
    _tx_type: u64,
) <b>acquires</b> <a href="evm.md#0x1_evm_Account">Account</a>, <a href="evm.md#0x1_evm_ContractEvent">ContractEvent</a> {
    <b>let</b> value = to_u256(value_bytes);
    <b>let</b> address_from = create_resource_address(&@aptos_framework, to_32bit(evm_from));
    <b>assert</b>!(<b>exists</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(address_from), <a href="evm.md#0x1_evm_ACCOUNT_NOT_EXIST">ACCOUNT_NOT_EXIST</a>);
    <b>let</b> nonce = <b>borrow_global</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(create_resource_address(&@aptos_framework, to_32bit(evm_from))).nonce;
    <a href="evm.md#0x1_evm_execute">execute</a>(to_32bit(evm_from), to_32bit(evm_to), nonce, data, value);
}
</code></pre>



</details>

<a id="0x1_evm_deposit"></a>

## Function `deposit`



<pre><code><b>public</b> entry <b>fun</b> <a href="evm.md#0x1_evm_deposit">deposit</a>(sender: &<a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a>, evm_addr: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, amount_bytes: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> entry <b>fun</b> <a href="evm.md#0x1_evm_deposit">deposit</a>(sender: &<a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a>, evm_addr: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, amount_bytes: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;) <b>acquires</b> <a href="evm.md#0x1_evm_Account">Account</a> {
    <b>let</b> amount = to_u256(amount_bytes);
    <b>assert</b>!(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(&evm_addr) == 20, <a href="evm.md#0x1_evm_ADDR_LENGTH">ADDR_LENGTH</a>);
    <a href="evm.md#0x1_evm_transfer_from_move_addr">transfer_from_move_addr</a>(sender, to_32bit(evm_addr), amount);
}
</code></pre>



</details>

<a id="0x1_evm_get_code"></a>

## Function `get_code`



<pre><code>#[view]
<b>public</b> <b>fun</b> <a href="evm.md#0x1_evm_get_code">get_code</a>(contract_addr: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="evm.md#0x1_evm_get_code">get_code</a>(contract_addr: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; <b>acquires</b> <a href="evm.md#0x1_evm_Account">Account</a> {
    <b>let</b> move_addr = create_resource_address(&@aptos_framework, contract_addr);
    <b>if</b>(!<b>exists</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(move_addr)) {
        x""
    } <b>else</b> {
        <b>borrow_global</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(move_addr).<a href="code.md#0x1_code">code</a>
    }
}
</code></pre>



</details>

<a id="0x1_evm_get_move_address"></a>

## Function `get_move_address`



<pre><code>#[view]
<b>public</b> <b>fun</b> <a href="evm.md#0x1_evm_get_move_address">get_move_address</a>(evm_addr: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <b>address</b>
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="evm.md#0x1_evm_get_move_address">get_move_address</a>(evm_addr: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <b>address</b> {
    create_resource_address(&@aptos_framework, to_32bit(evm_addr))
}
</code></pre>



</details>

<a id="0x1_evm_query"></a>

## Function `query`



<pre><code>#[view]
<b>public</b> <b>fun</b> <a href="evm.md#0x1_evm_query">query</a>(sender: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, contract_addr: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="evm.md#0x1_evm_query">query</a>(sender:<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, contract_addr: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; <b>acquires</b> <a href="evm.md#0x1_evm_Account">Account</a>, <a href="evm.md#0x1_evm_ContractEvent">ContractEvent</a> {
    contract_addr = to_32bit(contract_addr);
    <b>let</b> contract_store = <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(create_resource_address(&@aptos_framework, contract_addr));
    sender = to_32bit(sender);
    <b>let</b> (res, bytes) = <a href="evm.md#0x1_evm_run">run</a>(sender, sender, contract_addr, contract_store.<a href="code.md#0x1_code">code</a>, data, <b>true</b>, 0, &<b>mut</b> <a href="../../aptos-stdlib/doc/simple_map.md#0x1_simple_map_new">simple_map::new</a>&lt;u256, u256&gt;());
    <a href="evm.md#0x1_evm_handle_exdlecute_result">handle_exdlecute_result</a>(res, bytes)
}
</code></pre>



</details>

<a id="0x1_evm_get_storage_at"></a>

## Function `get_storage_at`



<pre><code>#[view]
<b>public</b> <b>fun</b> <a href="evm.md#0x1_evm_get_storage_at">get_storage_at</a>(addr: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, slot: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="evm.md#0x1_evm_get_storage_at">get_storage_at</a>(addr: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, slot: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; <b>acquires</b> <a href="evm.md#0x1_evm_Account">Account</a> {
    <b>let</b> move_address = create_resource_address(&@aptos_framework, to_32bit(addr));
    <b>if</b>(<b>exists</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(move_address)) {
        <b>let</b> account_store = <b>borrow_global</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(move_address);
        <b>let</b> slot_u256 = data_to_u256(slot, 0, (<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(&slot) <b>as</b> u256));
        <b>if</b>(<a href="../../aptos-stdlib/doc/table.md#0x1_table_contains">table::contains</a>(&account_store.storage, slot_u256)) {
            *<a href="../../aptos-stdlib/doc/table.md#0x1_table_borrow">table::borrow</a>(&account_store.storage, slot_u256)
        } <b>else</b> {
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>&lt;u8&gt;()
        }
    } <b>else</b> {
        <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>&lt;u8&gt;()
    }

}
</code></pre>



</details>

<a id="0x1_evm_handle_exdlecute_result"></a>

## Function `handle_exdlecute_result`



<pre><code><b>fun</b> <a href="evm.md#0x1_evm_handle_exdlecute_result">handle_exdlecute_result</a>(res: bool, bytes: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="evm.md#0x1_evm_handle_exdlecute_result">handle_exdlecute_result</a>(res: bool, bytes: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; {

    <b>if</b>(!res) {
        <a href="evm.md#0x1_evm_throw_error">throw_error</a>(bytes);
        x""
    } <b>else</b> {
        bytes
    }
}
</code></pre>



</details>

<a id="0x1_evm_throw_error"></a>

## Function `throw_error`



<pre><code><b>fun</b> <a href="evm.md#0x1_evm_throw_error">throw_error</a>(bytes: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="evm.md#0x1_evm_throw_error">throw_error</a>(bytes: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;) {
    <b>let</b> message = <b>if</b>(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(&bytes) == 0) x"" <b>else</b> {
        <b>let</b> len = to_u256(slice(bytes, 36, 32));
        slice(bytes, 68, len)
    };
    <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&message);
    <a href="evm.md#0x1_evm_revert">revert</a>(message);
}
</code></pre>



</details>

<a id="0x1_evm_execute"></a>

## Function `execute`



<pre><code><b>fun</b> <a href="evm.md#0x1_evm_execute">execute</a>(evm_from: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, evm_to: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, nonce: u64, data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, value: u256): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="evm.md#0x1_evm_execute">execute</a>(evm_from: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, evm_to: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, nonce: u64, data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, value: u256): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; <b>acquires</b> <a href="evm.md#0x1_evm_Account">Account</a>, <a href="evm.md#0x1_evm_ContractEvent">ContractEvent</a> {
    <b>let</b> address_from = create_resource_address(&@aptos_framework, evm_from);
    <b>let</b> address_to = create_resource_address(&@aptos_framework, evm_to);
    <a href="evm.md#0x1_evm_create_account_if_not_exist">create_account_if_not_exist</a>(address_from);
    <a href="evm.md#0x1_evm_create_account_if_not_exist">create_account_if_not_exist</a>(address_to);
    <a href="evm.md#0x1_evm_verify_nonce">verify_nonce</a>(address_from, nonce);
    <b>let</b> account_store_to = <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(address_to);
    <b>let</b> transient = &<b>mut</b> <a href="../../aptos-stdlib/doc/simple_map.md#0x1_simple_map_new">simple_map::new</a>&lt;u256, u256&gt;();
    <b>if</b>(evm_to == <a href="evm.md#0x1_evm_ZERO_ADDR">ZERO_ADDR</a>) {
        <b>let</b> evm_contract = get_contract_address(evm_from, nonce);
        <b>let</b> address_contract = create_resource_address(&@aptos_framework, evm_contract);
        <a href="evm.md#0x1_evm_create_account_if_not_exist">create_account_if_not_exist</a>(address_contract);
        <a href="evm.md#0x1_evm_create_event_if_not_exist">create_event_if_not_exist</a>(address_contract);
        <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(address_contract).is_contract = <b>true</b>;
        <b>let</b> (res, <a href="code.md#0x1_code">code</a>) = <a href="evm.md#0x1_evm_run">run</a>(evm_from, evm_from, evm_contract, data, x"", <b>false</b>, value, transient);
        <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(address_contract).<a href="code.md#0x1_code">code</a> = <a href="code.md#0x1_code">code</a>;
        <a href="evm.md#0x1_evm_handle_exdlecute_result">handle_exdlecute_result</a>(res, evm_contract)
    } <b>else</b> <b>if</b>(evm_to == <a href="evm.md#0x1_evm_ONE_ADDR">ONE_ADDR</a>) {
        <b>let</b> amount = data_to_u256(data, 36, 32);
        <b>let</b> <b>to</b> = to_address(slice(data, 100, 32));
        <a href="evm.md#0x1_evm_transfer_to_move_addr">transfer_to_move_addr</a>(evm_from, <b>to</b>, amount);
        x""
    } <b>else</b> {
        <b>if</b>(account_store_to.is_contract) {
            <b>let</b> (res, bytes) = <a href="evm.md#0x1_evm_run">run</a>(evm_from, evm_from, evm_to, account_store_to.<a href="code.md#0x1_code">code</a>, data, <b>false</b>, value, transient);
            <a href="evm.md#0x1_evm_handle_exdlecute_result">handle_exdlecute_result</a>(res, bytes)
        } <b>else</b> {
            <a href="evm.md#0x1_evm_transfer_to_evm_addr">transfer_to_evm_addr</a>(evm_from, evm_to, value);
            x""
        }
    }
}
</code></pre>



</details>

<a id="0x1_evm_precompile"></a>

## Function `precompile`



<pre><code><b>fun</b> <a href="precompile.md#0x1_precompile">precompile</a>(sender: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, <b>to</b>: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, value: u256, calldata: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="precompile.md#0x1_precompile">precompile</a>(sender: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, <b>to</b>: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, value: u256, calldata: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; <b>acquires</b> <a href="evm.md#0x1_evm_Account">Account</a> {
    <a href="evm.md#0x1_evm_transfer_to_evm_addr">transfer_to_evm_addr</a>(sender, <b>to</b>, value);
    run_precompile(<b>to</b>, calldata, <a href="evm.md#0x1_evm_CHAIN_ID">CHAIN_ID</a>)
}
</code></pre>



</details>

<a id="0x1_evm_run"></a>

## Function `run`



<pre><code><b>fun</b> <a href="evm.md#0x1_evm_run">run</a>(sender: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, origin: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, evm_contract_address: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, <a href="code.md#0x1_code">code</a>: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, readOnly: bool, value: u256, transient: &<b>mut</b> <a href="../../aptos-stdlib/doc/simple_map.md#0x1_simple_map_SimpleMap">simple_map::SimpleMap</a>&lt;u256, u256&gt;): (bool, <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="evm.md#0x1_evm_run">run</a>(sender: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, origin: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, evm_contract_address: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, <a href="code.md#0x1_code">code</a>: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, readOnly: bool, value: u256, transient: &<b>mut</b> SimpleMap&lt;u256, u256&gt;): (bool, <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;) <b>acquires</b> <a href="evm.md#0x1_evm_Account">Account</a>, <a href="evm.md#0x1_evm_ContractEvent">ContractEvent</a> {
    <b>if</b> (is_precompile_address(evm_contract_address)) {
        <b>return</b> (<b>true</b>, <a href="precompile.md#0x1_precompile">precompile</a>(sender, evm_contract_address, value, data))
    };

    // Convert the EVM <b>address</b> <b>to</b> a Move resource <b>address</b>.
    <b>let</b> move_contract_address = create_resource_address(&@aptos_framework, evm_contract_address);
    // Transfer the specified value <b>to</b> the EVM <b>address</b>
    <a href="evm.md#0x1_evm_transfer_to_evm_addr">transfer_to_evm_addr</a>(sender, evm_contract_address, value);
    // Initialize an empty stack and memory for the EVM execution.
    <b>let</b> stack = &<b>mut</b> <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>&lt;u256&gt;();
    <b>let</b> memory = &<b>mut</b> <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>&lt;u8&gt;();
    // <b>let</b>
    // Get the length of the bytecode.
    <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(&<a href="code.md#0x1_code">code</a>);
    // Initialize an empty <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a> for the runtime <a href="code.md#0x1_code">code</a>.
    <b>let</b> runtime_code = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>&lt;u8&gt;();
    // Initialize counters for the execution <b>loop</b>.
    <b>let</b> i = 0;
    <b>let</b> ret_size = 0;
    <b>let</b> ret_bytes = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>&lt;u8&gt;();

    // Start the execution <b>loop</b>.
    <b>while</b> (i &lt; len) {
        // Fetch the current opcode from the bytecode.

        <b>let</b> opcode = *<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_borrow">vector::borrow</a>(&<a href="code.md#0x1_code">code</a>, i);
        // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&i);
        // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&opcode);

        // Handle each opcode according <b>to</b> the EVM specification.
        // The following is a simplified <a href="version.md#0x1_version">version</a> of the EVM execution engine,
        // handling only a subset of all possible opcodes.
        // Each branch in this <b>if</b>-<b>else</b> chain corresponds <b>to</b> a specific opcode,
        // and contains the logic for executing that opcode.
        // For example, the `add` opcode pops two elements from the stack,
        // adds them together, and pushes the result back onto the stack.
        // The `mul` opcode does the same but <b>with</b> multiplication, and so on.
        // Some opcodes, like `sstore`, have side effects, such <b>as</b> modifying contract storage.
        // The `jump` and `jumpi` opcodes alter the control flow of the execution.
        // The `call`, `create`, and `create2` opcodes are used for contract interactions.
        // The `log` opcodes are used for emitting events.
        // The function returns the output data of the execution when it encounters the `stop` or `<b>return</b>` opcode.

        // stop
        <b>if</b>(opcode == 0x00) {
            ret_bytes = runtime_code;
            <b>break</b>
        }
        <b>else</b> <b>if</b>(opcode == 0xf3) {
            <b>let</b> pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            ret_bytes = slice(*memory, pos, len);
            <b>break</b>
        }
            //add
        <b>else</b> <b>if</b>(opcode == 0x01) {
            <b>let</b> a = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> b = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>if</b>(a &gt; 0 && b &gt;= (<a href="evm.md#0x1_evm_U256_MAX">U256_MAX</a> - a + 1)) {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, b - (<a href="evm.md#0x1_evm_U256_MAX">U256_MAX</a> - a + 1));
            } <b>else</b> {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, a + b);
            };
            i = i + 1;
        }
            //mul
        <b>else</b> <b>if</b>(opcode == 0x02) {
            <b>let</b> a = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> b = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, <a href="evm.md#0x1_evm_mul">mul</a>(a, b));
            i = i + 1;
        }
            //sub
        <b>else</b> <b>if</b>(opcode == 0x03) {
            <b>let</b> a = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> b = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>if</b>(a &gt;= b) {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, a - b);
            } <b>else</b> {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, <a href="evm.md#0x1_evm_U256_MAX">U256_MAX</a> - b + a + 1);
            };
            i = i + 1;
        }
            //div
        <b>else</b> <b>if</b>(opcode == 0x04) {
            <b>let</b> a = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> b = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, <b>if</b>(b == 0) 0 <b>else</b> a / b);
            i = i + 1;
        }
            //sdiv
        <b>else</b> <b>if</b>(opcode == 0x05) {
            <b>let</b>(sg_a, num_a) = to_int256(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack));
            <b>let</b>(sg_b, num_b) = to_int256(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack));
            <b>let</b> num_c = num_a / num_b;
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, add_sign(num_c, (!sg_a && sg_b) || (sg_a && !sg_b)));
            i = i + 1;
        }
            //mod
        <b>else</b> <b>if</b>(opcode == 0x06) {
            <b>let</b> a = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> b = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, a % b);
            i = i + 1;
        }
            //smod
        <b>else</b> <b>if</b>(opcode == 0x07) {
            <b>let</b>(sg_a, num_a) = to_int256(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack));
            <b>let</b>(_sg_b, num_b) = to_int256(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack));
            <b>let</b> num_c = num_a % num_b;
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, add_sign(num_c, sg_a));
            i = i + 1;
        }
            //addmod
        <b>else</b> <b>if</b>(opcode == 0x08) {
            <b>let</b> a = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> b = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> n = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, (a + b) % n);
            i = i + 1;
        }
            //mulmod
        <b>else</b> <b>if</b>(opcode == 0x09) {
            <b>let</b> a = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> b = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> n = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, <a href="evm.md#0x1_evm_mul_mod">mul_mod</a>(a, b, n));
            i = i + 1;
        }
            //exp
        <b>else</b> <b>if</b>(opcode == 0x0a) {
            <b>let</b> a = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> b = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, <a href="evm.md#0x1_evm_exp">exp</a>(a, b));
            i = i + 1;
        }
            //signextend
        <b>else</b> <b>if</b>(opcode == 0x0b) {
            <b>let</b> b = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> value = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>if</b>(b &gt; 31) {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, value);
            } <b>else</b> {
                <b>let</b> index = ((8 * b + 7) <b>as</b> u8);
                <b>let</b> mask = (1 &lt;&lt; index) - 1;
                <b>if</b>(((value &gt;&gt; index) & 1) == 0) {
                    <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, value & mask);
                } <b>else</b> {
                    <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, value | (<a href="evm.md#0x1_evm_U256_MAX">U256_MAX</a> - mask));
                };
            };
            i = i + 1;
        }
            //lt
        <b>else</b> <b>if</b>(opcode == 0x10) {
            <b>let</b> a = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> b = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>if</b>(a &lt; b) {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 1)
            } <b>else</b> {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 0)
            };
            i = i + 1;
        }
            //gt
        <b>else</b> <b>if</b>(opcode == 0x11) {
            <b>let</b> a = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> b = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>if</b>(a &gt; b) {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 1)
            } <b>else</b> {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 0)
            };
            i = i + 1;
        }
            //slt
        <b>else</b> <b>if</b>(opcode == 0x12) {
            <b>let</b> a = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> b = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b>(neg_a, num_a) = to_int256(a);
            <b>let</b>(neg_b, num_b) = to_int256(b);

            <b>let</b> is_positive_lt = num_a &lt; num_b && !(neg_a || neg_b);
            <b>let</b> is_negative_lt = num_a &gt; num_b && (neg_a && neg_b);
            <b>let</b> has_different_signs = neg_a && !neg_b;

            <b>let</b> value = 0;
            <b>if</b>(is_positive_lt || is_negative_lt || has_different_signs) {
                value = 1
            };
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, value);
            i = i + 1;
        }
            //sgt
        <b>else</b> <b>if</b>(opcode == 0x13) {
            <b>let</b> a = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> b = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b>(neg_a, num_a) = to_int256(a);
            <b>let</b>(neg_b, num_b) = to_int256(b);

            <b>let</b> is_positive_gt = num_a &gt; num_b && !(neg_a || neg_b);
            <b>let</b> is_negative_gt = num_a &lt; num_b && (neg_a && neg_b);
            <b>let</b> has_different_signs = !neg_a && neg_b;
            <b>let</b> value = 0;
            <b>if</b>(is_positive_gt || is_negative_gt || has_different_signs) {
                value = 1
            };
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, value);
            i = i + 1;
        }
            //eq
        <b>else</b> <b>if</b>(opcode == 0x14) {
            <b>let</b> a = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> b = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>if</b>(a == b) {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 1);
            } <b>else</b> {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 0);
            };
            i = i + 1;
        }
            //and
        <b>else</b> <b>if</b>(opcode == 0x16) {
            <b>let</b> a = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> b = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, a & b);
            i = i + 1;
        }
            //or
        <b>else</b> <b>if</b>(opcode == 0x17) {
            <b>let</b> a = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> b = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, a | b);
            i = i + 1;
        }
            //xor
        <b>else</b> <b>if</b>(opcode == 0x18) {
            <b>let</b> a = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> b = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, a ^ b);
            i = i + 1;
        }
            //not
        <b>else</b> <b>if</b>(opcode == 0x19) {
            // 10 1010
            // 6 0101
            <b>let</b> n = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, <a href="evm.md#0x1_evm_U256_MAX">U256_MAX</a> - n);
            i = i + 1;
        }
            //byte
        <b>else</b> <b>if</b>(opcode == 0x1a) {
            <b>let</b> ith = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> x = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>if</b>(ith &gt;= 32) {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 0);
            } <b>else</b> {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, (x &gt;&gt; ((248 - ith * 8) <b>as</b> u8)) & 0xFF);
            };

            i = i + 1;
        }
            //shl
        <b>else</b> <b>if</b>(opcode == 0x1b) {
            <b>let</b> b = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> a = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>if</b>(b &gt;= 256) {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 0);
            } <b>else</b> {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, a &lt;&lt; (b <b>as</b> u8));
            };
            i = i + 1;
        }
            //shr
        <b>else</b> <b>if</b>(opcode == 0x1c) {
            <b>let</b> b = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> a = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>if</b>(b &gt;= 256) {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 0);
            } <b>else</b> {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, a &gt;&gt; (b <b>as</b> u8));
            };

            i = i + 1;
        }
            //sar
        <b>else</b> <b>if</b>(opcode == 0x1d) {
            <b>let</b> b = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> a = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b>(neg, num_a) = to_int256(a);
            <b>let</b> c = 0;
            <b>if</b>(b == 0 || b &gt;= 256) {
                <b>if</b>(neg) {
                    c = <a href="evm.md#0x1_evm_U256_MAX">U256_MAX</a>;
                }
            } <b>else</b> {
                <b>if</b>(neg) {
                    <b>let</b> n = num_a &gt;&gt; (b <b>as</b> u8);
                    c = <b>if</b>(n &gt; 0) <a href="evm.md#0x1_evm_U256_MAX">U256_MAX</a> - n + 1 <b>else</b> 0;
                } <b>else</b> {
                    c = a &gt;&gt; (b <b>as</b> u8);
                }
            };

            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, c);
            i = i + 1;
        }
            //push0
        <b>else</b> <b>if</b>(opcode == 0x5f) {
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 0);
            i = i + 1;
        }
            // push1 -&gt; push32
        <b>else</b> <b>if</b>(opcode &gt;= 0x60 && opcode &lt;= 0x7f)  {
            <b>let</b> n = ((opcode - 0x60) <b>as</b> u64);
            <b>let</b> number = data_to_u256(<a href="code.md#0x1_code">code</a>, ((i + 1) <b>as</b> u256), ((n + 1) <b>as</b> u256));
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, number);
            i = i + n + 2;
        }
            // pop
        <b>else</b> <b>if</b>(opcode == 0x50) {
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            i = i + 1
        }
            //<b>address</b>
        <b>else</b> <b>if</b>(opcode == 0x30) {
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, data_to_u256(evm_contract_address, 0, 32));
            i = i + 1;
        }
            //balance
        <b>else</b> <b>if</b>(opcode == 0x31) {
            <b>let</b> evm_addr = u256_to_data(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack));
            <b>let</b> target_address = create_resource_address(&@aptos_framework, evm_addr);
            <b>if</b>(<b>exists</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(target_address)) {
                <b>let</b> account_store = <b>borrow_global</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(target_address);
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, account_store.balance);
            } <b>else</b> {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 0)
            };
            i = i + 1;
        }
            //origin
        <b>else</b> <b>if</b>(opcode == 0x32) {
            <b>let</b> value = data_to_u256(origin, 0, 32);
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, value);
            i = i + 1;
        }
            //caller
        <b>else</b> <b>if</b>(opcode == 0x33) {
            <b>let</b> value = data_to_u256(sender, 0, 32);
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, value);
            i = i + 1;
        }
            // callvalue
        <b>else</b> <b>if</b>(opcode == 0x34) {
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, value);
            i = i + 1;
        }
            //calldataload
        <b>else</b> <b>if</b>(opcode == 0x35) {
            <b>let</b> pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, data_to_u256(data, pos, 32));
            i = i + 1;
            // <a href="block.md#0x1_block">block</a>.
        }
            //calldatasize
        <b>else</b> <b>if</b>(opcode == 0x36) {
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, (<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(&data) <b>as</b> u256));
            i = i + 1;
        }
            //calldatacopy
        <b>else</b> <b>if</b>(opcode == 0x37) {
            <b>let</b> m_pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> d_pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> end = d_pos + len;
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&utf8(b"calldatacopy"));
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&data);
            <b>while</b> (d_pos &lt; end) {
                // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&d_pos);
                // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&end);
                <b>let</b> bytes = <b>if</b>(end - d_pos &gt;= 32) {
                    slice(data, d_pos, 32)
                } <b>else</b> {
                    slice(data, d_pos, end - d_pos)
                };
                // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&bytes);
                mstore(memory, m_pos, bytes);
                d_pos = d_pos + 32;
                m_pos = m_pos + 32;
            };
            i = i + 1
        }
            //codesize
        <b>else</b> <b>if</b>(opcode == 0x38) {
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, (<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(&<a href="code.md#0x1_code">code</a>) <b>as</b> u256));
            i = i + 1
        }
            //codecopy
        <b>else</b> <b>if</b>(opcode == 0x39) {
            <b>let</b> m_pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> d_pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> end = d_pos + len;
            runtime_code = slice(<a href="code.md#0x1_code">code</a>, d_pos, len);
            <b>while</b> (d_pos &lt; end) {
                <b>let</b> bytes = <b>if</b>(end - d_pos &gt;= 32) {
                    slice(<a href="code.md#0x1_code">code</a>, d_pos, 32)
                } <b>else</b> {
                    slice(<a href="code.md#0x1_code">code</a>, d_pos, end - d_pos)
                };
                mstore(memory, m_pos, bytes);
                d_pos = d_pos + 32;
                m_pos = m_pos + 32;
            };
            i = i + 1
        }
            //extcodesize
        <b>else</b> <b>if</b>(opcode == 0x3b) {
            <b>let</b> bytes = u256_to_data(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack));
            <b>let</b> target_evm = to_32bit(slice(bytes, 12, 20));
            <b>let</b> target_address = create_resource_address(&@aptos_framework, target_evm);
            <b>if</b>(<a href="evm.md#0x1_evm_exist_contract">exist_contract</a>(target_address)) {
                <b>let</b> <a href="code.md#0x1_code">code</a> = <b>borrow_global</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(target_address).<a href="code.md#0x1_code">code</a>;
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, (<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(&<a href="code.md#0x1_code">code</a>) <b>as</b> u256));
            } <b>else</b> {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 0);
            };

            i = i + 1;
        }
            //returndatacopy
        <b>else</b> <b>if</b>(opcode == 0x3e) {
            // mstore()
            <b>let</b> m_pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> d_pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> bytes = slice(ret_bytes, d_pos, len);
            mstore(memory, m_pos, bytes);
            i = i + 1;
        }
            //returndatasize
        <b>else</b> <b>if</b>(opcode == 0x3d) {
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, ret_size);
            i = i + 1;
        }
            //blockhash
        <b>else</b> <b>if</b>(opcode == 0x40) {
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 0);
            i = i + 1;
        }
            //coinbase
        <b>else</b> <b>if</b>(opcode == 0x41) {
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 0);
            i = i + 1;
        }
            //<a href="timestamp.md#0x1_timestamp">timestamp</a>
        <b>else</b> <b>if</b>(opcode == 0x42) {
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, (now_microseconds() <b>as</b> u256) / 1000000);
            i = i + 1;
        }
            //number
        <b>else</b> <b>if</b>(opcode == 0x43) {
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, (<a href="block.md#0x1_block_get_current_block_height">block::get_current_block_height</a>() <b>as</b> u256));
            i = i + 1;
        }
            //difficulty
        <b>else</b> <b>if</b>(opcode == 0x44) {
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 0);
            i = i + 1;
        }
            //gaslimit
        <b>else</b> <b>if</b>(opcode == 0x45) {
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 30000000);
            i = i + 1;
        }
            //chainid
        <b>else</b> <b>if</b>(opcode == 0x46) {
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 1);
            i = i + 1
        }
            //self balance
        <b>else</b> <b>if</b>(opcode == 0x47) {
            <b>let</b> contract_store = <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(move_contract_address);
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, contract_store.balance);
            i = i + 1;
        }
            // mload
        <b>else</b> <b>if</b>(opcode == 0x51) {
            <b>let</b> pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, data_to_u256(slice(*memory, pos, 32), 0, 32));
            i = i + 1;
        }
            // mstore
        <b>else</b> <b>if</b>(opcode == 0x52) {
            <b>let</b> pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> value = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            mstore(memory, pos, u256_to_data(value));
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(memory);
            i = i + 1;

        }
            //mstore8
        <b>else</b> <b>if</b>(opcode == 0x53) {
            <b>let</b> pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> value = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            *<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_borrow_mut">vector::borrow_mut</a>(memory, (pos <b>as</b> u64)) = ((value & 0xff) <b>as</b> u8);
            // mstore(memory, pos, u256_to_data(value & 0xff));
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(memory);
            i = i + 1;

        }
            // sload
        <b>else</b> <b>if</b>(opcode == 0x54) {
            <b>let</b> pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> contract_store = <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(move_contract_address);
            <b>if</b>(<a href="../../aptos-stdlib/doc/table.md#0x1_table_contains">table::contains</a>(&contract_store.storage, pos)) {
                <b>let</b> value = *<a href="../../aptos-stdlib/doc/table.md#0x1_table_borrow">table::borrow</a>(&<b>mut</b> contract_store.storage, pos);
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, data_to_u256(value, 0, 32));
            } <b>else</b> {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 0);
            };
            i = i + 1;
        }
            // sstore
        <b>else</b> <b>if</b>(opcode == 0x55) {
            <b>if</b>(readOnly) {
                <b>assert</b>!(<b>false</b>, <a href="evm.md#0x1_evm_CONTRACT_READ_ONLY">CONTRACT_READ_ONLY</a>);
            };
            <b>let</b> contract_store = <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(move_contract_address);
            <b>let</b> pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> value = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <a href="../../aptos-stdlib/doc/table.md#0x1_table_upsert">table::upsert</a>(&<b>mut</b> contract_store.storage, pos, u256_to_data(value));
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&utf8(b"sstore"));
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&evm_contract_address);
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&pos);
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&value);
            i = i + 1;
        }
            //dup1 -&gt; dup16
        <b>else</b> <b>if</b>(opcode &gt;= 0x80 && opcode &lt;= 0x8f) {
            <b>let</b> size = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(stack);
            <b>let</b> value = *<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_borrow">vector::borrow</a>(stack, size - ((opcode - 0x80 + 1) <b>as</b> u64));
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, value);
            i = i + 1;
        }
            //swap1 -&gt; swap16
        <b>else</b> <b>if</b>(opcode &gt;= 0x90 && opcode &lt;= 0x9f) {
            <b>let</b> size = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(stack);
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_swap">vector::swap</a>(stack, size - 1, size - ((opcode - 0x90 + 2) <b>as</b> u64));
            i = i + 1;
        }
            //iszero
        <b>else</b> <b>if</b>(opcode == 0x15) {
            <b>let</b> value = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>if</b>(value == 0) {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 1)
            } <b>else</b> {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 0)
            };
            i = i + 1;
        }
            //jump
        <b>else</b> <b>if</b>(opcode == 0x56) {
            <b>let</b> dest = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            i = (dest <b>as</b> u64) + 1
        }
            //jumpi
        <b>else</b> <b>if</b>(opcode == 0x57) {
            <b>let</b> dest = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> condition = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>if</b>(condition &gt; 0) {
                i = (dest <b>as</b> u64) + 1
            } <b>else</b> {
                i = i + 1
            }
        }
            //gas
        <b>else</b> <b>if</b>(opcode == 0x5a) {
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 0);
            i = i + 1
        }
            //jump dest (no action, <b>continue</b> execution)
        <b>else</b> <b>if</b>(opcode == 0x5b) {
            i = i + 1
        }
            //TLOAD
        <b>else</b> <b>if</b>(opcode == 0x5c) {
            <b>let</b> key = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>if</b>(<a href="../../aptos-stdlib/doc/simple_map.md#0x1_simple_map_contains_key">simple_map::contains_key</a>(transient, &key)) {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, *<a href="../../aptos-stdlib/doc/simple_map.md#0x1_simple_map_borrow">simple_map::borrow</a>(transient, &key));
            } <b>else</b> {
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 0);
            };

            i = i + 1
        }
            //TSTORE
        <b>else</b> <b>if</b>(opcode == 0x5d) {
            <b>let</b> key = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> value = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <a href="../../aptos-stdlib/doc/simple_map.md#0x1_simple_map_upsert">simple_map::upsert</a>(transient, key, value);
            i = i + 1
        }
            //MCOPY
        <b>else</b> <b>if</b>(opcode == 0x5e) {
            <b>let</b> m_pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> d_pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> bytes = slice(*memory, d_pos, len);
            mstore(memory, m_pos, bytes);
            i = i + 1;
        }
            //sha3
        <b>else</b> <b>if</b>(opcode == 0x20) {
            <b>let</b> pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> bytes = slice(*memory, pos, len);
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&utf8(b"sha3"));
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&bytes);
            <b>let</b> value = data_to_u256(keccak256(bytes), 0, 32);
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&keccak256(bytes));
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, value);
            i = i + 1
        }
            //call 0xf1 static call 0xfa delegate call 0xf4
        <b>else</b> <b>if</b>(opcode == 0xf1 || opcode == 0xfa || opcode == 0xf4) {
            <b>let</b> readOnly = <b>if</b> (opcode == 0xfa) <b>true</b> <b>else</b> <b>false</b>;
            <b>let</b> _gas = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> evm_dest_addr = to_32bit(u256_to_data(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack)));
            <b>let</b> move_dest_addr = create_resource_address(&@aptos_framework, evm_dest_addr);
            <b>let</b> msg_value = <b>if</b> (opcode == 0xf1) <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack) <b>else</b> 0;
            <b>let</b> m_pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> m_len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> ret_pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> ret_len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> ret_end = ret_len + ret_pos;
            <b>let</b> params = slice(*memory, m_pos, m_len);

            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&utf8(b"call 222"));
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&opcode);
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&dest_addr);
            <b>if</b> (is_precompile_address(evm_dest_addr) ||<a href="evm.md#0x1_evm_exist_contract">exist_contract</a>(move_dest_addr)) {
                <b>let</b> dest_code = <a href="evm.md#0x1_evm_get_code">get_code</a>(evm_dest_addr);

                <b>let</b> target = <b>if</b> (opcode == 0xf4) evm_contract_address <b>else</b> evm_dest_addr;
                <b>let</b> from = <b>if</b> (opcode == 0xf4) sender <b>else</b> evm_contract_address;
                <b>let</b>(call_res, bytes) = <a href="evm.md#0x1_evm_run">run</a>(from, sender, target, dest_code, params, readOnly, msg_value, transient);
                ret_size = (<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(&bytes) <b>as</b> u256);
                ret_bytes = bytes;
                <b>let</b> index = 0;

                <b>while</b> (ret_pos &lt; ret_end) {
                    <b>let</b> bytes = <b>if</b> (ret_end - ret_pos &gt;= 32) {
                        slice(bytes, index, 32)
                    } <b>else</b> {
                        slice(bytes, index, ret_end - ret_pos)
                    };
                    mstore(memory, ret_pos, bytes);
                    ret_pos = ret_pos + 32;
                    index = index + 32;
                };
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, <b>if</b>(call_res) 1 <b>else</b> 0);
            } <b>else</b> {
                <a href="evm.md#0x1_evm_transfer_to_evm_addr">transfer_to_evm_addr</a>(evm_contract_address, evm_dest_addr, msg_value);
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 1);
            };
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&opcode);
            i = i + 1
        }
            //create
        <b>else</b> <b>if</b>(opcode == 0xf0) {
            <b>if</b>(readOnly) {
                <b>assert</b>!(<b>false</b>, <a href="evm.md#0x1_evm_CONTRACT_READ_ONLY">CONTRACT_READ_ONLY</a>);
            };
            <b>let</b> msg_value = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> new_codes = slice(*memory, pos, len);
            <b>let</b> contract_store = <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(move_contract_address);
            <b>let</b> nonce = contract_store.nonce;
            // must be 20 bytes

            <b>let</b> new_evm_contract_addr = get_contract_address(evm_contract_address, nonce);
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&utf8(b"create start"));
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&nonce);
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&new_evm_contract_addr);
            <b>let</b> new_move_contract_addr = create_resource_address(&@aptos_framework, new_evm_contract_addr);
            contract_store.nonce = contract_store.nonce + 1;

            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&<b>exists</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(new_move_contract_addr));
            <b>assert</b>!(!<a href="evm.md#0x1_evm_exist_contract">exist_contract</a>(new_move_contract_addr), <a href="evm.md#0x1_evm_CONTRACT_DEPLOYED">CONTRACT_DEPLOYED</a>);
            <a href="evm.md#0x1_evm_create_account_if_not_exist">create_account_if_not_exist</a>(new_move_contract_addr);
            <a href="evm.md#0x1_evm_create_event_if_not_exist">create_event_if_not_exist</a>(new_move_contract_addr);

            <b>let</b> (create_res, bytes) = <a href="evm.md#0x1_evm_run">run</a>(evm_contract_address, sender, new_evm_contract_addr, new_codes, x"", <b>false</b>, msg_value, transient);
            <b>if</b>(create_res) {
                <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(new_move_contract_addr).<a href="code.md#0x1_code">code</a> = bytes;
                <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(new_move_contract_addr).nonce = 1;
                <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(new_move_contract_addr).is_contract = <b>true</b>;
                ret_bytes = new_evm_contract_addr;
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, data_to_u256(new_evm_contract_addr, 0, 32));
            } <b>else</b> {
                ret_bytes = bytes;
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 0);
            };

            <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&utf8(b"create end"));
            ret_size = 32;


            i = i + 1
        }
            //create2
        <b>else</b> <b>if</b>(opcode == 0xf5) {
            <b>if</b>(readOnly) {
                <b>assert</b>!(<b>false</b>, <a href="evm.md#0x1_evm_CONTRACT_READ_ONLY">CONTRACT_READ_ONLY</a>);
            };
            <b>let</b> msg_value = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> salt = u256_to_data(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack));
            <b>let</b> new_codes = slice(*memory, pos, len);
            <b>let</b> p = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>&lt;u8&gt;();
            // <b>let</b> contract_store = ;
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_append">vector::append</a>(&<b>mut</b> p, x"ff");
            // must be 20 bytes
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_append">vector::append</a>(&<b>mut</b> p, slice(evm_contract_address, 12, 20));
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_append">vector::append</a>(&<b>mut</b> p, salt);
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_append">vector::append</a>(&<b>mut</b> p, keccak256(new_codes));
            <b>let</b> new_evm_contract_addr = to_32bit(slice(keccak256(p), 12, 20));
            <b>let</b> new_move_contract_addr = create_resource_address(&@aptos_framework, new_evm_contract_addr);
            <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&utf8(b"create2 start"));
            <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&evm_contract_address);
            <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&sender);
            <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&p);
            <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&new_evm_contract_addr);
            <b>assert</b>!(!<a href="evm.md#0x1_evm_exist_contract">exist_contract</a>(new_move_contract_addr), <a href="evm.md#0x1_evm_CONTRACT_DEPLOYED">CONTRACT_DEPLOYED</a>);
            <a href="evm.md#0x1_evm_create_account_if_not_exist">create_account_if_not_exist</a>(new_move_contract_addr);
            <a href="evm.md#0x1_evm_create_event_if_not_exist">create_event_if_not_exist</a>(new_move_contract_addr);

            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&p);
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&new_codes);
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&new_contract_addr);
            <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(move_contract_address).nonce = <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(move_contract_address).nonce + 1;
            <b>let</b> (create_res, bytes) = <a href="evm.md#0x1_evm_run">run</a>(evm_contract_address, sender, new_evm_contract_addr, new_codes, x"", <b>false</b>, msg_value, transient);
            <b>if</b>(create_res) {
                <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(new_move_contract_addr).nonce = 1;
                <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(new_move_contract_addr).is_contract = <b>true</b>;
                <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(new_move_contract_addr).<a href="code.md#0x1_code">code</a> = bytes;

                ret_bytes = new_evm_contract_addr;
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, data_to_u256(new_evm_contract_addr, 0, 32));
            } <b>else</b> {
                ret_bytes = bytes;
                <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(stack, 0);
            };

            ret_size = 32;
            i = i + 1
        }
            //revert
        <b>else</b> <b>if</b>(opcode == 0xfd) {
            <b>let</b> pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> bytes = slice(*memory, pos, len);
            <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&utf8(b"revert"));
            <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&bytes);
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&pos);
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&len);
            // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(memory);
            // i = i + 1;
            <b>return</b> (<b>false</b>, bytes)
        }
            //log0
        <b>else</b> <b>if</b>(opcode == 0xa0) {
            <b>let</b> pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> data = slice(*memory, pos, len);
            <b>let</b> event_store = <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_ContractEvent">ContractEvent</a>&gt;(move_contract_address);
            <a href="event.md#0x1_event_emit_event">event::emit_event</a>&lt;<a href="evm.md#0x1_evm_Log0Event">Log0Event</a>&gt;(
                &<b>mut</b> event_store.log0Event,
                <a href="evm.md#0x1_evm_Log0Event">Log0Event</a>{
                    contract: evm_contract_address,
                    data,
                },
            );
            i = i + 1
        }
            //log1
        <b>else</b> <b>if</b>(opcode == 0xa1) {
            <b>let</b> pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> data = slice(*memory, pos, len);
            <b>let</b> topic0 = u256_to_data(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack));
            <b>let</b> event_store = <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_ContractEvent">ContractEvent</a>&gt;(move_contract_address);
            <a href="event.md#0x1_event_emit_event">event::emit_event</a>&lt;<a href="evm.md#0x1_evm_Log1Event">Log1Event</a>&gt;(
                &<b>mut</b> event_store.log1Event,
                <a href="evm.md#0x1_evm_Log1Event">Log1Event</a>{
                    contract: evm_contract_address,
                    data,
                    topic0,
                },
            );
            i = i + 1
        }
            //log2
        <b>else</b> <b>if</b>(opcode == 0xa2) {
            <b>let</b> pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> data = slice(*memory, pos, len);
            <b>let</b> topic0 = u256_to_data(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack));
            <b>let</b> topic1 = u256_to_data(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack));
            <b>let</b> event_store = <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_ContractEvent">ContractEvent</a>&gt;(move_contract_address);
            <a href="event.md#0x1_event_emit_event">event::emit_event</a>&lt;<a href="evm.md#0x1_evm_Log2Event">Log2Event</a>&gt;(
                &<b>mut</b> event_store.log2Event,
                <a href="evm.md#0x1_evm_Log2Event">Log2Event</a>{
                    contract: evm_contract_address,
                    data,
                    topic0,
                    topic1
                },
            );
            i = i + 1
        }
            //log3
        <b>else</b> <b>if</b>(opcode == 0xa3) {
            <b>let</b> pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> data = slice(*memory, pos, len);
            <b>let</b> topic0 = u256_to_data(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack));
            <b>let</b> topic1 = u256_to_data(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack));
            <b>let</b> topic2 = u256_to_data(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack));
            <b>let</b> event_store = <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_ContractEvent">ContractEvent</a>&gt;(move_contract_address);
            <a href="event.md#0x1_event_emit_event">event::emit_event</a>&lt;<a href="evm.md#0x1_evm_Log3Event">Log3Event</a>&gt;(
                &<b>mut</b> event_store.log3Event,
                <a href="evm.md#0x1_evm_Log3Event">Log3Event</a>{
                    contract: evm_contract_address,
                    data,
                    topic0,
                    topic1,
                    topic2
                },
            );
            i = i + 1
        }
            //log4
        <b>else</b> <b>if</b>(opcode == 0xa4) {
            <b>let</b> pos = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack);
            <b>let</b> data = slice(*memory, pos, len);
            <b>let</b> topic0 = u256_to_data(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack));
            <b>let</b> topic1 = u256_to_data(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack));
            <b>let</b> topic2 = u256_to_data(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack));
            <b>let</b> topic3 = u256_to_data(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_pop_back">vector::pop_back</a>(stack));
            <b>let</b> event_store = <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_ContractEvent">ContractEvent</a>&gt;(move_contract_address);
            <a href="event.md#0x1_event_emit_event">event::emit_event</a>&lt;<a href="evm.md#0x1_evm_Log4Event">Log4Event</a>&gt;(
                &<b>mut</b> event_store.log4Event,
                <a href="evm.md#0x1_evm_Log4Event">Log4Event</a>{
                    contract: evm_contract_address,
                    data,
                    topic0,
                    topic1,
                    topic2,
                    topic3
                },
            );
            i = i + 1
        }
        <b>else</b> {
            <b>assert</b>!(<b>false</b>, (opcode <b>as</b> u64));
        };
        // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(stack);
        // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(stack));
    };
    // <a href="../../aptos-stdlib/doc/simple_map.md#0x1_simple_map_borrow_mut">simple_map::borrow_mut</a>&lt;<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, T&gt;(&<b>mut</b> <b>global</b>.contracts, &contract_addr).storage = storage;
    (<b>true</b>, ret_bytes)
}
</code></pre>



</details>

<a id="0x1_evm_exist_contract"></a>

## Function `exist_contract`



<pre><code><b>fun</b> <a href="evm.md#0x1_evm_exist_contract">exist_contract</a>(addr: <b>address</b>): bool
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="evm.md#0x1_evm_exist_contract">exist_contract</a>(addr: <b>address</b>): bool <b>acquires</b> <a href="evm.md#0x1_evm_Account">Account</a> {
    <b>exists</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(addr) && (<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(&<b>borrow_global</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(addr).<a href="code.md#0x1_code">code</a>) &gt; 0)
}
</code></pre>



</details>

<a id="0x1_evm_add_balance"></a>

## Function `add_balance`



<pre><code><b>fun</b> <a href="evm.md#0x1_evm_add_balance">add_balance</a>(addr: <b>address</b>, amount: u256)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="evm.md#0x1_evm_add_balance">add_balance</a>(addr: <b>address</b>, amount: u256) <b>acquires</b> <a href="evm.md#0x1_evm_Account">Account</a> {
    <a href="evm.md#0x1_evm_create_account_if_not_exist">create_account_if_not_exist</a>(addr);
    <b>if</b>(amount &gt; 0) {
        <b>let</b> account_store = <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(addr);
        account_store.balance = account_store.balance + amount;
    }
}
</code></pre>



</details>

<a id="0x1_evm_transfer_from_move_addr"></a>

## Function `transfer_from_move_addr`



<pre><code><b>fun</b> <a href="evm.md#0x1_evm_transfer_from_move_addr">transfer_from_move_addr</a>(<a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a>: &<a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a>, evm_to: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, amount: u256)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="evm.md#0x1_evm_transfer_from_move_addr">transfer_from_move_addr</a>(<a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a>: &<a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a>, evm_to: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, amount: u256) <b>acquires</b> <a href="evm.md#0x1_evm_Account">Account</a> {
    <b>if</b>(amount &gt; 0) {
        <b>let</b> <b>move_to</b> = create_resource_address(&@aptos_framework, evm_to);
        <a href="evm.md#0x1_evm_create_account_if_not_exist">create_account_if_not_exist</a>(<b>move_to</b>);
        <a href="coin.md#0x1_coin_transfer">coin::transfer</a>&lt;AptosCoin&gt;(<a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a>, <b>move_to</b>, ((amount / <a href="evm.md#0x1_evm_CONVERT_BASE">CONVERT_BASE</a>)  <b>as</b> u64));

        <b>let</b> account_store_to = <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(<b>move_to</b>);
        account_store_to.balance = account_store_to.balance + amount;
    }
}
</code></pre>



</details>

<a id="0x1_evm_transfer_to_evm_addr"></a>

## Function `transfer_to_evm_addr`



<pre><code><b>fun</b> <a href="evm.md#0x1_evm_transfer_to_evm_addr">transfer_to_evm_addr</a>(evm_from: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, evm_to: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, amount: u256)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="evm.md#0x1_evm_transfer_to_evm_addr">transfer_to_evm_addr</a>(evm_from: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, evm_to: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, amount: u256) <b>acquires</b> <a href="evm.md#0x1_evm_Account">Account</a> {
    <b>if</b>(amount &gt; 0) {
        <b>let</b> <b>move_from</b> = create_resource_address(&@aptos_framework, evm_from);
        <b>let</b> <b>move_to</b> = create_resource_address(&@aptos_framework, evm_to);
        <a href="evm.md#0x1_evm_create_account_if_not_exist">create_account_if_not_exist</a>(<b>move_to</b>);
        <b>let</b> account_store_from = <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(<b>move_from</b>);
        <b>assert</b>!(account_store_from.balance &gt;= amount, <a href="evm.md#0x1_evm_INSUFFIENT_BALANCE">INSUFFIENT_BALANCE</a>);
        account_store_from.balance = account_store_from.balance - amount;

        <b>let</b> account_store_to = <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(<b>move_to</b>);
        account_store_to.balance = account_store_to.balance + amount;

        <b>let</b> <a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a> = <a href="create_signer.md#0x1_create_signer">create_signer</a>(<b>move_from</b>);
        <a href="coin.md#0x1_coin_transfer">coin::transfer</a>&lt;AptosCoin&gt;(&<a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a>, <b>move_to</b>, ((amount / <a href="evm.md#0x1_evm_CONVERT_BASE">CONVERT_BASE</a>)  <b>as</b> u64));
    }
}
</code></pre>



</details>

<a id="0x1_evm_transfer_to_move_addr"></a>

## Function `transfer_to_move_addr`



<pre><code><b>fun</b> <a href="evm.md#0x1_evm_transfer_to_move_addr">transfer_to_move_addr</a>(evm_from: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, <b>move_to</b>: <b>address</b>, amount: u256)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="evm.md#0x1_evm_transfer_to_move_addr">transfer_to_move_addr</a>(evm_from: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, <b>move_to</b>: <b>address</b>, amount: u256) <b>acquires</b> <a href="evm.md#0x1_evm_Account">Account</a> {
    <b>if</b>(amount &gt; 0) {
        <b>let</b> <b>move_from</b> = create_resource_address(&@aptos_framework, evm_from);
        <b>let</b> account_store_from = <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(<b>move_from</b>);
        <b>assert</b>!(account_store_from.balance &gt;= amount, <a href="evm.md#0x1_evm_INSUFFIENT_BALANCE">INSUFFIENT_BALANCE</a>);
        account_store_from.balance = account_store_from.balance - amount;

        <b>let</b> <a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a> = <a href="create_signer.md#0x1_create_signer">create_signer</a>(<b>move_from</b>);
        <a href="coin.md#0x1_coin_transfer">coin::transfer</a>&lt;AptosCoin&gt;(&<a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a>, <b>move_to</b>, ((amount / <a href="evm.md#0x1_evm_CONVERT_BASE">CONVERT_BASE</a>)  <b>as</b> u64));
    }
}
</code></pre>



</details>

<a id="0x1_evm_create_event_if_not_exist"></a>

## Function `create_event_if_not_exist`



<pre><code><b>fun</b> <a href="evm.md#0x1_evm_create_event_if_not_exist">create_event_if_not_exist</a>(addr: <b>address</b>)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="evm.md#0x1_evm_create_event_if_not_exist">create_event_if_not_exist</a>(addr: <b>address</b>) {
    <b>if</b>(!<b>exists</b>&lt;<a href="evm.md#0x1_evm_ContractEvent">ContractEvent</a>&gt;(addr)) {
        <b>let</b> <a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a> = <a href="create_signer.md#0x1_create_signer">create_signer</a>(addr);
        <b>move_to</b>(&<a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a>, <a href="evm.md#0x1_evm_ContractEvent">ContractEvent</a> {
            log0Event: new_event_handle&lt;<a href="evm.md#0x1_evm_Log0Event">Log0Event</a>&gt;(&<a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a>),
            log1Event: new_event_handle&lt;<a href="evm.md#0x1_evm_Log1Event">Log1Event</a>&gt;(&<a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a>),
            log2Event: new_event_handle&lt;<a href="evm.md#0x1_evm_Log2Event">Log2Event</a>&gt;(&<a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a>),
            log3Event: new_event_handle&lt;<a href="evm.md#0x1_evm_Log3Event">Log3Event</a>&gt;(&<a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a>),
            log4Event: new_event_handle&lt;<a href="evm.md#0x1_evm_Log4Event">Log4Event</a>&gt;(&<a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a>),
        })
    }
}
</code></pre>



</details>

<a id="0x1_evm_create2_address"></a>

## Function `create2_address`



<pre><code><b>fun</b> <a href="evm.md#0x1_evm_create2_address">create2_address</a>(sender: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, t1: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, t2: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, fee: u256, <a href="../../aptos-stdlib/../move-stdlib/doc/hash.md#0x1_hash">hash</a>: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="evm.md#0x1_evm_create2_address">create2_address</a>(sender: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, t1: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, t2: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, fee: u256, <a href="../../aptos-stdlib/../move-stdlib/doc/hash.md#0x1_hash">hash</a>: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; {
    <b>let</b> salt = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>&lt;u8&gt;();
    <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_append">vector::append</a>(&<b>mut</b> salt, t1);
    <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_append">vector::append</a>(&<b>mut</b> salt, t2);
    <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_append">vector::append</a>(&<b>mut</b> salt, u256_to_data(fee));
    <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&salt);
    <b>let</b> p = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>&lt;u8&gt;();
    <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_append">vector::append</a>(&<b>mut</b> p, x"ff");
    // must be 20 bytes
    <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_append">vector::append</a>(&<b>mut</b> p, slice(sender, 12, 20));
    <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_append">vector::append</a>(&<b>mut</b> p, keccak256(salt));
    <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_append">vector::append</a>(&<b>mut</b> p, <a href="../../aptos-stdlib/../move-stdlib/doc/hash.md#0x1_hash">hash</a>);
    to_32bit(slice(keccak256(p), 12, 20))
}
</code></pre>



</details>

<a id="0x1_evm_create_account_if_not_exist"></a>

## Function `create_account_if_not_exist`



<pre><code><b>fun</b> <a href="evm.md#0x1_evm_create_account_if_not_exist">create_account_if_not_exist</a>(addr: <b>address</b>)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="evm.md#0x1_evm_create_account_if_not_exist">create_account_if_not_exist</a>(addr: <b>address</b>) {
    <b>if</b>(!<b>exists</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(addr)) {
        <b>if</b>(!exists_at(addr)) {
            create_account(addr);
        };
        <b>let</b> <a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a> = <a href="create_signer.md#0x1_create_signer">create_signer</a>(addr);
        <a href="coin.md#0x1_coin_register">coin::register</a>&lt;AptosCoin&gt;(&<a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a>);
        <b>move_to</b>(&<a href="../../aptos-stdlib/../move-stdlib/doc/signer.md#0x1_signer">signer</a>, <a href="evm.md#0x1_evm_Account">Account</a> {
            <a href="code.md#0x1_code">code</a>: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>(),
            storage: <a href="../../aptos-stdlib/doc/table.md#0x1_table_new">table::new</a>&lt;u256, <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;&gt;(),
            balance: 0,
            is_contract: <b>false</b>,
            nonce: 0
        })
    };
}
</code></pre>



</details>

<a id="0x1_evm_verify_nonce"></a>

## Function `verify_nonce`



<pre><code><b>fun</b> <a href="evm.md#0x1_evm_verify_nonce">verify_nonce</a>(addr: <b>address</b>, nonce: u64)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="evm.md#0x1_evm_verify_nonce">verify_nonce</a>(addr: <b>address</b>, nonce: u64) <b>acquires</b> <a href="evm.md#0x1_evm_Account">Account</a> {
    <b>let</b> coin_store_from = <b>borrow_global_mut</b>&lt;<a href="evm.md#0x1_evm_Account">Account</a>&gt;(addr);
    <b>assert</b>!(coin_store_from.nonce == nonce, <a href="evm.md#0x1_evm_NONCE">NONCE</a>);
    coin_store_from.nonce = coin_store_from.nonce + 1;
}
</code></pre>



</details>

<a id="0x1_evm_verify_signature"></a>

## Function `verify_signature`



<pre><code><b>fun</b> <a href="evm.md#0x1_evm_verify_signature">verify_signature</a>(from: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, message_hash: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, r: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, s: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, v: u64)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="evm.md#0x1_evm_verify_signature">verify_signature</a>(from: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, message_hash: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, r: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, s: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, v: u64) {
    <b>let</b> input_bytes = r;
    <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_append">vector::append</a>(&<b>mut</b> input_bytes, s);
    <b>let</b> signature = ecdsa_signature_from_bytes(input_bytes);
    <b>let</b> recovery_id = <b>if</b>(v &gt; 28) ((v - (<a href="evm.md#0x1_evm_CHAIN_ID">CHAIN_ID</a> * 2) - 35) <b>as</b> u8) <b>else</b> ((v - 27) <b>as</b> u8);
    <b>let</b> pk_recover = ecdsa_recover(message_hash, recovery_id, &signature);
    <b>let</b> pk = keccak256(ecdsa_raw_public_key_to_bytes(borrow(&pk_recover)));
    <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&slice(pk, 12, 20));
    <b>assert</b>!(slice(pk, 12, 20) == from, <a href="evm.md#0x1_evm_SIGNATURE">SIGNATURE</a>);
}
</code></pre>



</details>


[move-book]: https://aptos.dev/move/book/SUMMARY
