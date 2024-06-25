
<a id="0x1_precompile"></a>

# Module `0x1::precompile`



-  [Constants](#@Constants_0)
-  [Function `run_precompile`](#0x1_precompile_run_precompile)
-  [Function `is_precompile_address`](#0x1_precompile_is_precompile_address)


<pre><code><b>use</b> <a href="../../aptos-stdlib/../move-stdlib/doc/hash.md#0x1_aptos_hash">0x1::aptos_hash</a>;
<b>use</b> <a href="../../aptos-stdlib/doc/debug.md#0x1_debug">0x1::debug</a>;
<b>use</b> <a href="util.md#0x1_evm_util">0x1::evm_util</a>;
<b>use</b> <a href="../../aptos-stdlib/../move-stdlib/doc/hash.md#0x1_hash">0x1::hash</a>;
<b>use</b> <a href="../../aptos-stdlib/../move-stdlib/doc/option.md#0x1_option">0x1::option</a>;
<b>use</b> <a href="../../aptos-stdlib/doc/secp256k1.md#0x1_secp256k1">0x1::secp256k1</a>;
</code></pre>



<a id="@Constants_0"></a>

## Constants


<a id="0x1_precompile_BLAKE2F"></a>



<pre><code><b>const</b> <a href="precompile.md#0x1_precompile_BLAKE2F">BLAKE2F</a>: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9];
</code></pre>



<a id="0x1_precompile_CALL_DATA_LENGTH"></a>

invalid precomile calldata length


<pre><code><b>const</b> <a href="precompile.md#0x1_precompile_CALL_DATA_LENGTH">CALL_DATA_LENGTH</a>: u64 = 50002;
</code></pre>



<a id="0x1_precompile_ECADD"></a>



<pre><code><b>const</b> <a href="precompile.md#0x1_precompile_ECADD">ECADD</a>: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6];
</code></pre>



<a id="0x1_precompile_ECMUL"></a>



<pre><code><b>const</b> <a href="precompile.md#0x1_precompile_ECMUL">ECMUL</a>: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7];
</code></pre>



<a id="0x1_precompile_ECPAIRING"></a>



<pre><code><b>const</b> <a href="precompile.md#0x1_precompile_ECPAIRING">ECPAIRING</a>: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8];
</code></pre>



<a id="0x1_precompile_IDENTITY"></a>



<pre><code><b>const</b> <a href="precompile.md#0x1_precompile_IDENTITY">IDENTITY</a>: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4];
</code></pre>



<a id="0x1_precompile_MODEXP"></a>



<pre><code><b>const</b> <a href="precompile.md#0x1_precompile_MODEXP">MODEXP</a>: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5];
</code></pre>



<a id="0x1_precompile_MOD_PARAMS_SISE"></a>

mod exp len params invalid


<pre><code><b>const</b> <a href="precompile.md#0x1_precompile_MOD_PARAMS_SISE">MOD_PARAMS_SISE</a>: u64 = 50003;
</code></pre>



<a id="0x1_precompile_RCRECOVER"></a>



<pre><code><b>const</b> <a href="precompile.md#0x1_precompile_RCRECOVER">RCRECOVER</a>: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
</code></pre>



<a id="0x1_precompile_RIPEMD"></a>



<pre><code><b>const</b> <a href="precompile.md#0x1_precompile_RIPEMD">RIPEMD</a>: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3];
</code></pre>



<a id="0x1_precompile_SHA256"></a>



<pre><code><b>const</b> <a href="precompile.md#0x1_precompile_SHA256">SHA256</a>: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2];
</code></pre>



<a id="0x1_precompile_UNSUPPORT"></a>

unsupport precomile address


<pre><code><b>const</b> <a href="precompile.md#0x1_precompile_UNSUPPORT">UNSUPPORT</a>: u64 = 50001;
</code></pre>



<a id="0x1_precompile_run_precompile"></a>

## Function `run_precompile`



<pre><code>#[view]
<b>public</b> <b>fun</b> <a href="precompile.md#0x1_precompile_run_precompile">run_precompile</a>(addr: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, calldata: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, <a href="chain_id.md#0x1_chain_id">chain_id</a>: u64): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="precompile.md#0x1_precompile_run_precompile">run_precompile</a>(addr: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, calldata: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, <a href="chain_id.md#0x1_chain_id">chain_id</a>: u64): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; {
    <b>if</b>(addr == <a href="precompile.md#0x1_precompile_RCRECOVER">RCRECOVER</a>) {
        <b>assert</b>!(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(&calldata) == 128, <a href="precompile.md#0x1_precompile_CALL_DATA_LENGTH">CALL_DATA_LENGTH</a>);
        <b>let</b> message_hash = slice(calldata, 0, 32);
        <b>let</b> v = (to_u256(slice(calldata, 32, 32)) <b>as</b> u64);
        <b>let</b> signature = ecdsa_signature_from_bytes(slice(calldata, 64, 64));

        <b>let</b> recovery_id = <b>if</b>(v &gt; 28) ((v - (<a href="chain_id.md#0x1_chain_id">chain_id</a> * 2) - 35) <b>as</b> u8) <b>else</b> ((v - 27) <b>as</b> u8);
        <b>let</b> pk_recover = ecdsa_recover(message_hash, recovery_id, &signature);
        <b>let</b> pk = keccak256(ecdsa_raw_public_key_to_bytes(borrow(&pk_recover)));
        <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&slice(pk, 12, 20));
        to_32bit(slice(pk, 12, 20))
    } <b>else</b> <b>if</b>(addr == <a href="precompile.md#0x1_precompile_SHA256">SHA256</a>) {
        sha2_256(calldata)
    } <b>else</b> <b>if</b>(addr == <a href="precompile.md#0x1_precompile_RIPEMD">RIPEMD</a>) {
        <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&to_32bit(ripemd160(calldata)));
        to_32bit(ripemd160(calldata))
    } <b>else</b> <b>if</b>(addr == <a href="precompile.md#0x1_precompile_IDENTITY">IDENTITY</a>) {
        calldata
    } <b>else</b> {
        <b>assert</b>!(<b>false</b>, (to_u256(addr) <b>as</b> u64));
        x""
    }
}
</code></pre>



</details>

<a id="0x1_precompile_is_precompile_address"></a>

## Function `is_precompile_address`



<pre><code>#[view]
<b>public</b> <b>fun</b> <a href="precompile.md#0x1_precompile_is_precompile_address">is_precompile_address</a>(addr: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): bool
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="precompile.md#0x1_precompile_is_precompile_address">is_precompile_address</a>(addr: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): bool {
    <b>let</b> num = to_u256(addr);
    num &gt;= 0x01 && num &lt;= 0x0a
}
</code></pre>



</details>


[move-book]: https://aptos.dev/move/book/SUMMARY
