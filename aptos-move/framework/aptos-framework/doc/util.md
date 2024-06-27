
<a id="0x1_util"></a>

# Module `0x1::util`

Utility functions used by the framework modules.


-  [Function `from_bytes`](#0x1_util_from_bytes)
-  [Function `address_from_bytes`](#0x1_util_address_from_bytes)
-  [Specification](#@Specification_0)
    -  [Function `from_bytes`](#@Specification_0_from_bytes)
    -  [High-level Requirements](#high-level-req)
    -  [Module-level Specification](#module-level-spec)
    -  [Function `address_from_bytes`](#@Specification_0_address_from_bytes)


<pre><code></code></pre>



<a id="0x1_util_from_bytes"></a>

## Function `from_bytes`

Native function to deserialize a type T.

Note that this function does not put any constraint on <code>T</code>. If code uses this function to
deserialized a linear value, its their responsibility that the data they deserialize is
owned.


<pre><code><b>public</b>(<b>friend</b>) <b>fun</b> <a href="util.md#0x1_util_from_bytes">from_bytes</a>&lt;T&gt;(bytes: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): T
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b>(<b>friend</b>) <b>native</b> <b>fun</b> <a href="util.md#0x1_util_from_bytes">from_bytes</a>&lt;T&gt;(bytes: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): T;
</code></pre>



</details>

<a id="0x1_util_address_from_bytes"></a>

## Function `address_from_bytes`



<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_util_address_from_bytes">address_from_bytes</a>(bytes: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <b>address</b>
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_util_address_from_bytes">address_from_bytes</a>(bytes: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <b>address</b> {
    <a href="util.md#0x1_util_from_bytes">from_bytes</a>(bytes)
}
</code></pre>



</details>

<a id="@Specification_0"></a>

## Specification


<a id="@Specification_0_from_bytes"></a>

### Function `from_bytes`


<pre><code><b>public</b>(<b>friend</b>) <b>fun</b> <a href="util.md#0x1_util_from_bytes">from_bytes</a>&lt;T&gt;(bytes: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): T
</code></pre>





<a id="high-level-req"></a>

### High-level Requirements

<table>
<tr>
<th>No.</th><th>Requirement</th><th>Criticality</th><th>Implementation</th><th>Enforcement</th>
</tr>

<tr>
<td>1</td>
<td>The address input bytes should be exactly 32 bytes long.</td>
<td>Low</td>
<td>The address_from_bytes function should assert if the length of the input bytes is 32.</td>
<td>Verified via <a href="#high-level-req-1">address_from_bytes</a>.</td>
</tr>

</table>




<a id="module-level-spec"></a>

### Module-level Specification


<pre><code><b>pragma</b> opaque;
<b>aborts_if</b> [abstract] <b>false</b>;
<b>ensures</b> [abstract] result == <a href="util.md#0x1_util_spec_from_bytes">spec_from_bytes</a>&lt;T&gt;(bytes);
</code></pre>




<a id="0x1_util_spec_from_bytes"></a>


<pre><code><b>fun</b> <a href="util.md#0x1_util_spec_from_bytes">spec_from_bytes</a>&lt;T&gt;(bytes: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): T;
</code></pre>



<a id="@Specification_0_address_from_bytes"></a>

### Function `address_from_bytes`


<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_util_address_from_bytes">address_from_bytes</a>(bytes: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <b>address</b>
</code></pre>




<pre><code>// This enforces <a id="high-level-req-1" href="#high-level-req">high-level requirement 1</a>:
<b>aborts_if</b> [abstract] len(bytes) != 32;
</code></pre>



<a id="0x1_evm_util"></a>

# Module `0x1::evm_util`



-  [Constants](#@Constants_0)
-  [Function `slice`](#0x1_evm_util_slice)
-  [Function `to_32bit`](#0x1_evm_util_to_32bit)
-  [Function `get_contract_address`](#0x1_evm_util_get_contract_address)
-  [Function `power`](#0x1_evm_util_power)
-  [Function `to_int256`](#0x1_evm_util_to_int256)
-  [Function `add_sign`](#0x1_evm_util_add_sign)
-  [Function `to_u256`](#0x1_evm_util_to_u256)
-  [Function `data_to_u256`](#0x1_evm_util_data_to_u256)
-  [Function `u256_to_data`](#0x1_evm_util_u256_to_data)
-  [Function `mstore`](#0x1_evm_util_mstore)
-  [Function `get_message_hash`](#0x1_evm_util_get_message_hash)
-  [Function `u256_to_trimed_data`](#0x1_evm_util_u256_to_trimed_data)
-  [Function `trim`](#0x1_evm_util_trim)
-  [Function `hex_length`](#0x1_evm_util_hex_length)
-  [Function `encode_data`](#0x1_evm_util_encode_data)


<pre><code><b>use</b> <a href="../../aptos-stdlib/../move-stdlib/doc/hash.md#0x1_aptos_hash">0x1::aptos_hash</a>;
<b>use</b> <a href="encode.md#0x1_rlp_encode">0x1::rlp_encode</a>;
<b>use</b> <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">0x1::vector</a>;
</code></pre>



<a id="@Constants_0"></a>

## Constants


<a id="0x1_evm_util_TX_FORMAT"></a>



<pre><code><b>const</b> <a href="util.md#0x1_evm_util_TX_FORMAT">TX_FORMAT</a>: u64 = 20001;
</code></pre>



<a id="0x1_evm_util_U255_MAX"></a>



<pre><code><b>const</b> <a href="util.md#0x1_evm_util_U255_MAX">U255_MAX</a>: u256 = 57896044618658097711785492504343953926634992332820282019728792003956564819967;
</code></pre>



<a id="0x1_evm_util_U256_MAX"></a>



<pre><code><b>const</b> <a href="util.md#0x1_evm_util_U256_MAX">U256_MAX</a>: u256 = 115792089237316195423570985008687907853269984665640564039457584007913129639935;
</code></pre>



<a id="0x1_evm_util_ZERO_EVM_ADDR"></a>



<pre><code><b>const</b> <a href="util.md#0x1_evm_util_ZERO_EVM_ADDR">ZERO_EVM_ADDR</a>: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; = [];
</code></pre>



<a id="0x1_evm_util_slice"></a>

## Function `slice`



<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_slice">slice</a>(data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, pos: u256, size: u256): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_slice">slice</a>(data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, pos: u256, size: u256): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; {
    <b>let</b> s = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>&lt;u8&gt;();
    <b>let</b> i = 0;
    <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(&data);
    <b>while</b> (i &lt; size) {
        <b>let</b> p = ((pos + i) <b>as</b> u64);
        <b>if</b>(p &gt;= len) {
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(&<b>mut</b> s, 0);
        } <b>else</b> {
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(&<b>mut</b> s, *<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_borrow">vector::borrow</a>(&data, (pos + i <b>as</b> u64)));
        };

        i = i + 1;
    };
    s
}
</code></pre>



</details>

<a id="0x1_evm_util_to_32bit"></a>

## Function `to_32bit`



<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_to_32bit">to_32bit</a>(data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_to_32bit">to_32bit</a>(data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; {
    <b>let</b> bytes = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>&lt;u8&gt;();
    <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(&data);
    // <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&len);
    <b>while</b>(len &lt; 32) {
        <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(&<b>mut</b> bytes, 0);
        len = len + 1
    };
    <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_append">vector::append</a>(&<b>mut</b> bytes, data);
    bytes
}
</code></pre>



</details>

<a id="0x1_evm_util_get_contract_address"></a>

## Function `get_contract_address`



<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_get_contract_address">get_contract_address</a>(addr: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, nonce: u64): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_get_contract_address">get_contract_address</a>(addr: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, nonce: u64): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; {
    <b>let</b> nonce_bytes = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>&lt;u8&gt;();
    <b>let</b> l = 0;
    <b>while</b>(nonce &gt; 0) {
        l = l + 1;
        <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(&<b>mut</b> nonce_bytes, ((nonce % 0x100) <b>as</b> u8));
        nonce = nonce / 0x100;
    };
    <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_reverse">vector::reverse</a>(&<b>mut</b> nonce_bytes);
    <b>let</b> salt = encode_bytes_list(<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>[<a href="util.md#0x1_evm_util_slice">slice</a>(addr, 12, 20), nonce_bytes]);
    <a href="util.md#0x1_evm_util_to_32bit">to_32bit</a>(<a href="util.md#0x1_evm_util_slice">slice</a>(keccak256(salt), 12, 20))
}
</code></pre>



</details>

<a id="0x1_evm_util_power"></a>

## Function `power`



<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_power">power</a>(base: u256, exponent: u256): u256
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_power">power</a>(base: u256, exponent: u256): u256 {
    <b>let</b> result = 1;

    <b>let</b> i = 0;
    <b>while</b> (i &lt; exponent) {
        result = result * base;
        i = i + 1;
    };

    result
}
</code></pre>



</details>

<a id="0x1_evm_util_to_int256"></a>

## Function `to_int256`



<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_to_int256">to_int256</a>(num: u256): (bool, u256)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_to_int256">to_int256</a>(num: u256): (bool, u256) {
    <b>let</b> neg = <b>false</b>;
    <b>if</b>(num &gt; <a href="util.md#0x1_evm_util_U255_MAX">U255_MAX</a>) {
        neg = <b>true</b>;
        num = <a href="util.md#0x1_evm_util_U256_MAX">U256_MAX</a> - num + 1;
    };
    (neg, num)
}
</code></pre>



</details>

<a id="0x1_evm_util_add_sign"></a>

## Function `add_sign`



<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_add_sign">add_sign</a>(value: u256, sign: bool): u256
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_add_sign">add_sign</a>(value: u256, sign: bool): u256 {
    <b>if</b>(sign) {
        <a href="util.md#0x1_evm_util_U256_MAX">U256_MAX</a> - value + 1
    } <b>else</b> {
        value
    }
}
</code></pre>



</details>

<a id="0x1_evm_util_to_u256"></a>

## Function `to_u256`



<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_to_u256">to_u256</a>(data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): u256
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_to_u256">to_u256</a>(data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): u256 {
    <b>let</b> res = 0;
    <b>let</b> i = 0;
    <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(&data);
    <b>while</b> (i &lt; len) {
        <b>let</b> value = *<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_borrow">vector::borrow</a>(&data, i);
        res = (res &lt;&lt; 8) + (value <b>as</b> u256);
        i = i + 1;
    };
    res
}
</code></pre>



</details>

<a id="0x1_evm_util_data_to_u256"></a>

## Function `data_to_u256`



<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_data_to_u256">data_to_u256</a>(data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, p: u256, size: u256): u256
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_data_to_u256">data_to_u256</a>(data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, p: u256, size: u256): u256 {
    <b>let</b> res = 0;
    <b>let</b> i = 0;
    <b>let</b> len = (<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(&data) <b>as</b> u256);
    <b>assert</b>!(size &lt;= 32, 1);
    <b>while</b> (i &lt; size) {
        <b>if</b>(p + i &lt; len) {
            <b>let</b> value = *<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_borrow">vector::borrow</a>(&data, ((p + i) <b>as</b> u64));
            res = (res &lt;&lt; 8) + (value <b>as</b> u256);
        } <b>else</b> {
            res = res &lt;&lt; 8
        };

        i = i + 1;
    };

    res
}
</code></pre>



</details>

<a id="0x1_evm_util_u256_to_data"></a>

## Function `u256_to_data`



<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_u256_to_data">u256_to_data</a>(num256: u256): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_u256_to_data">u256_to_data</a>(num256: u256): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; {
    <b>let</b> res = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>&lt;u8&gt;();
    <b>let</b> i = 32;
    <b>while</b>(i &gt; 0) {
        i = i - 1;
        <b>let</b> shifted_value = num256 &gt;&gt; (i * 8);
        <b>let</b> byte = ((shifted_value & 0xff) <b>as</b> u8);
        <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(&<b>mut</b> res, byte);
    };
    res
}
</code></pre>



</details>

<a id="0x1_evm_util_mstore"></a>

## Function `mstore`



<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_mstore">mstore</a>(memory: &<b>mut</b> <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, pos: u256, data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_mstore">mstore</a>(memory: &<b>mut</b> <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, pos: u256, data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;) {
    <b>let</b> len_m = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(memory);
    <b>let</b> len_d = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(&data);
    <b>let</b> p = (pos <b>as</b> u64);
    <b>while</b>(len_m &lt; p) {
        <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(memory, 0);
        len_m = len_m + 1
    };

    <b>let</b> i = 0;
    <b>while</b> (i &lt; len_d) {
        <b>if</b>(len_m &lt;= p + i) {
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(memory, *<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_borrow">vector::borrow</a>(&data, i));
            len_m = len_m + 1;
        } <b>else</b> {
            *<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_borrow_mut">vector::borrow_mut</a>(memory, p + i) = *<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_borrow">vector::borrow</a>(&data, i);
        };

        i = i + 1
    };
}
</code></pre>



</details>

<a id="0x1_evm_util_get_message_hash"></a>

## Function `get_message_hash`



<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_get_message_hash">get_message_hash</a>(input: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_get_message_hash">get_message_hash</a>(input: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; {
    <b>let</b> i = 0;
    <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(&input);
    <b>let</b> content = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>&lt;u8&gt;();
    <b>while</b>(i &lt; len) {
        <b>let</b> item = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_borrow">vector::borrow</a>(&input, i);
        <b>let</b> item_len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(item);
        <b>let</b> encoded = <b>if</b>(item_len == 1 && *<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_borrow">vector::borrow</a>(item, 0) &lt; 0x80) *item <b>else</b> <a href="util.md#0x1_evm_util_encode_data">encode_data</a>(item, 0x80);
        <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_append">vector::append</a>(&<b>mut</b> content, encoded);
        i = i + 1;
    };

    <a href="util.md#0x1_evm_util_encode_data">encode_data</a>(&content, 0xc0)
}
</code></pre>



</details>

<a id="0x1_evm_util_u256_to_trimed_data"></a>

## Function `u256_to_trimed_data`



<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_u256_to_trimed_data">u256_to_trimed_data</a>(num: u256): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_u256_to_trimed_data">u256_to_trimed_data</a>(num: u256): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; {
    <a href="util.md#0x1_evm_util_trim">trim</a>(<a href="util.md#0x1_evm_util_u256_to_data">u256_to_data</a>(num))
}
</code></pre>



</details>

<a id="0x1_evm_util_trim"></a>

## Function `trim`



<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_trim">trim</a>(data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="util.md#0x1_evm_util_trim">trim</a>(data: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; {
    <b>let</b> i = 0;
    <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(&data);
    <b>while</b> (i &lt; len) {
        <b>let</b> ith = *<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_borrow">vector::borrow</a>(&data, i);
        <b>if</b>(ith != 0) {
            <b>break</b>
        };
        i = i + 1
    };
    <a href="util.md#0x1_evm_util_slice">slice</a>(data, (i <b>as</b> u256), ((len - i) <b>as</b> u256))
}
</code></pre>



</details>

<a id="0x1_evm_util_hex_length"></a>

## Function `hex_length`



<pre><code><b>fun</b> <a href="util.md#0x1_evm_util_hex_length">hex_length</a>(len: u64): (u8, <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="util.md#0x1_evm_util_hex_length">hex_length</a>(len: u64): (u8, <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;) {
    <b>let</b> res = 0;
    <b>let</b> bytes = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>&lt;u8&gt;();
    <b>while</b>(len &gt; 0) {
        res = res + 1;
        <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(&<b>mut</b> bytes, ((len % 256) <b>as</b> u8));
        len = len / 256;
    };
    <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_reverse">vector::reverse</a>(&<b>mut</b> bytes);
    (res, bytes)
}
</code></pre>



</details>

<a id="0x1_evm_util_encode_data"></a>

## Function `encode_data`



<pre><code><b>fun</b> <a href="util.md#0x1_evm_util_encode_data">encode_data</a>(data: &<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, offset: u8): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="util.md#0x1_evm_util_encode_data">encode_data</a>(data: &<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, offset: u8): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; {
    <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(data);
    <b>let</b> res = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>&lt;u8&gt;();
    <b>if</b>(len &lt; 56) {
        <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(&<b>mut</b> res, (len <b>as</b> u8) + offset);
    } <b>else</b> {
        <b>let</b>(hex_len, len_bytes) = <a href="util.md#0x1_evm_util_hex_length">hex_length</a>(len);
        <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(&<b>mut</b> res, hex_len + offset + 55);
        <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_append">vector::append</a>(&<b>mut</b> res, len_bytes);
    };
    <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_append">vector::append</a>(&<b>mut</b> res, *data);
    res
}
</code></pre>



</details>


[move-book]: https://aptos.dev/move/book/SUMMARY
