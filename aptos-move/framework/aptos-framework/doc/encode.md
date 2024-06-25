
<a id="0x1_rlp_encode"></a>

# Module `0x1::rlp_encode`



-  [Constants](#@Constants_0)
-  [Function `encode_bytes_list`](#0x1_rlp_encode_encode_bytes_list)
-  [Function `encode_bytes`](#0x1_rlp_encode_encode_bytes)
-  [Function `encode_length`](#0x1_rlp_encode_encode_length)
-  [Function `to_binary`](#0x1_rlp_encode_to_binary)
-  [Function `to_byte`](#0x1_rlp_encode_to_byte)


<pre><code><b>use</b> <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">0x1::vector</a>;
</code></pre>



<a id="@Constants_0"></a>

## Constants


<a id="0x1_rlp_encode_CONST_256_EXP_8"></a>



<pre><code><b>const</b> <a href="encode.md#0x1_rlp_encode_CONST_256_EXP_8">CONST_256_EXP_8</a>: u128 = 18446744073709551616;
</code></pre>



<a id="0x1_rlp_encode_ERR_TOO_LONG_BYTE_ARRAY"></a>



<pre><code><b>const</b> <a href="encode.md#0x1_rlp_encode_ERR_TOO_LONG_BYTE_ARRAY">ERR_TOO_LONG_BYTE_ARRAY</a>: u64 = 0;
</code></pre>



<a id="0x1_rlp_encode_encode_bytes_list"></a>

## Function `encode_bytes_list`



<pre><code><b>public</b> <b>fun</b> <a href="encode.md#0x1_rlp_encode_encode_bytes_list">encode_bytes_list</a>(inputs: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="encode.md#0x1_rlp_encode_encode_bytes_list">encode_bytes_list</a>(inputs: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; {
    <b>let</b> output = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>();

    <b>let</b> i = 0;
    <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(&inputs);
    <b>while</b>(i &lt; len) {
        <b>let</b> next = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_borrow">vector::borrow</a>(&inputs, i);
        <b>let</b> next = <a href="encode.md#0x1_rlp_encode_encode_bytes">encode_bytes</a>(*next);
        <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_append">vector::append</a>(&<b>mut</b> output, next);
        i = i + 1;
    };

    <b>let</b> left = <a href="encode.md#0x1_rlp_encode_encode_length">encode_length</a>(&output, 0xc0);
    <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_append">vector::append</a>(&<b>mut</b> left, output);
    <b>return</b> left
}
</code></pre>



</details>

<a id="0x1_rlp_encode_encode_bytes"></a>

## Function `encode_bytes`



<pre><code><b>public</b> <b>fun</b> <a href="encode.md#0x1_rlp_encode_encode_bytes">encode_bytes</a>(input: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="encode.md#0x1_rlp_encode_encode_bytes">encode_bytes</a>(input: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; {
    <b>if</b> (<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(&input) == 1 && *<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_borrow">vector::borrow</a>(&input, 0) &lt; 0x80) {
        <b>return</b> input
    } <b>else</b> {
        <b>let</b> left = <a href="encode.md#0x1_rlp_encode_encode_length">encode_length</a>(&input, 0x80);
        <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_append">vector::append</a>(&<b>mut</b> left, input);
        <b>return</b> left
    }
}
</code></pre>



</details>

<a id="0x1_rlp_encode_encode_length"></a>

## Function `encode_length`



<pre><code><b>fun</b> <a href="encode.md#0x1_rlp_encode_encode_length">encode_length</a>(input: &<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, offset: u8): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="encode.md#0x1_rlp_encode_encode_length">encode_length</a>(input: &<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, offset: u8): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; {
    <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(input);
    <b>if</b> (len &lt; 56) {
        <b>return</b> <a href="encode.md#0x1_rlp_encode_to_byte">to_byte</a>((len <b>as</b> u8) + offset)
    };
    <b>assert</b>!((len <b>as</b> u128) &lt; <a href="encode.md#0x1_rlp_encode_CONST_256_EXP_8">CONST_256_EXP_8</a>, <a href="encode.md#0x1_rlp_encode_ERR_TOO_LONG_BYTE_ARRAY">ERR_TOO_LONG_BYTE_ARRAY</a>);
    <b>let</b> bl = <a href="encode.md#0x1_rlp_encode_to_binary">to_binary</a>(len);
    <b>let</b> len_bl = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(&bl);
    <b>let</b> left = <a href="encode.md#0x1_rlp_encode_to_byte">to_byte</a>((len_bl <b>as</b> u8) + offset + 55);
    <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_append">vector::append</a>(&<b>mut</b> left, bl);
    <b>return</b> left
}
</code></pre>



</details>

<a id="0x1_rlp_encode_to_binary"></a>

## Function `to_binary`



<pre><code><b>fun</b> <a href="encode.md#0x1_rlp_encode_to_binary">to_binary</a>(x: u64): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="encode.md#0x1_rlp_encode_to_binary">to_binary</a>(x: u64): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; {
    <b>if</b> (x == 0) {
        <b>return</b> <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>()
    } <b>else</b> {
        <b>let</b> left = <a href="encode.md#0x1_rlp_encode_to_binary">to_binary</a>(x / 256);
        <b>let</b> mod = x % 256;
        <b>let</b> right = <a href="encode.md#0x1_rlp_encode_to_byte">to_byte</a>((mod <b>as</b> u8));
        <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_append">vector::append</a>(&<b>mut</b> left, right);
        <b>return</b> left
    }
}
</code></pre>



</details>

<a id="0x1_rlp_encode_to_byte"></a>

## Function `to_byte`



<pre><code><b>fun</b> <a href="encode.md#0x1_rlp_encode_to_byte">to_byte</a>(val: u8): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="encode.md#0x1_rlp_encode_to_byte">to_byte</a>(val: u8): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; {
    <b>let</b> v = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>&lt;u8&gt;();
    <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(&<b>mut</b> v, val);
    v
}
</code></pre>



</details>


[move-book]: https://aptos.dev/move/book/SUMMARY
