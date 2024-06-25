
<a id="0x1_rlp_decode"></a>

# Module `0x1::rlp_decode`



-  [Constants](#@Constants_0)
-  [Function `decode_bytes`](#0x1_rlp_decode_decode_bytes)
-  [Function `append_u8a_to`](#0x1_rlp_decode_append_u8a_to)
-  [Function `decode_bytes_list`](#0x1_rlp_decode_decode_bytes_list)
-  [Function `decode_length`](#0x1_rlp_decode_decode_length)
-  [Function `slice`](#0x1_rlp_decode_slice)
-  [Function `to_integer`](#0x1_rlp_decode_to_integer)
-  [Function `to_integer_within`](#0x1_rlp_decode_to_integer_within)


<pre><code></code></pre>



<a id="@Constants_0"></a>

## Constants


<a id="0x1_rlp_decode_ERR_EMPTY"></a>



<pre><code><b>const</b> <a href="decode.md#0x1_rlp_decode_ERR_EMPTY">ERR_EMPTY</a>: u64 = 0;
</code></pre>



<a id="0x1_rlp_decode_ERR_INVALID"></a>



<pre><code><b>const</b> <a href="decode.md#0x1_rlp_decode_ERR_INVALID">ERR_INVALID</a>: u64 = 1;
</code></pre>



<a id="0x1_rlp_decode_ERR_NOT_BYTES"></a>



<pre><code><b>const</b> <a href="decode.md#0x1_rlp_decode_ERR_NOT_BYTES">ERR_NOT_BYTES</a>: u64 = 2;
</code></pre>



<a id="0x1_rlp_decode_ERR_NOT_BYTES_LIST"></a>



<pre><code><b>const</b> <a href="decode.md#0x1_rlp_decode_ERR_NOT_BYTES_LIST">ERR_NOT_BYTES_LIST</a>: u64 = 4;
</code></pre>



<a id="0x1_rlp_decode_ERR_NOT_LIST"></a>



<pre><code><b>const</b> <a href="decode.md#0x1_rlp_decode_ERR_NOT_LIST">ERR_NOT_LIST</a>: u64 = 3;
</code></pre>



<a id="0x1_rlp_decode_TYPE_BYTES"></a>



<pre><code><b>const</b> <a href="decode.md#0x1_rlp_decode_TYPE_BYTES">TYPE_BYTES</a>: u8 = 0;
</code></pre>



<a id="0x1_rlp_decode_TYPE_LIST"></a>



<pre><code><b>const</b> <a href="decode.md#0x1_rlp_decode_TYPE_LIST">TYPE_LIST</a>: u8 = 1;
</code></pre>



<a id="0x1_rlp_decode_decode_bytes"></a>

## Function `decode_bytes`



<pre><code><b>public</b> <b>fun</b> <a href="decode.md#0x1_rlp_decode_decode_bytes">decode_bytes</a>(rlp: &<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="decode.md#0x1_rlp_decode_decode_bytes">decode_bytes</a>(rlp: &<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; {
    <b>let</b> output: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>();
    <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(rlp);
    <b>if</b> (len == 0) {
        <b>return</b> output
    };

    <b>let</b> (offset, size, type) = <a href="decode.md#0x1_rlp_decode_decode_length">decode_length</a>(rlp, 0);
    <b>if</b> (type == <a href="decode.md#0x1_rlp_decode_TYPE_BYTES">TYPE_BYTES</a>) {
        <a href="decode.md#0x1_rlp_decode_append_u8a_to">append_u8a_to</a>(&<b>mut</b> output, rlp, offset, size);
    } <b>else</b> {
        <b>assert</b>!(<b>false</b>, <a href="decode.md#0x1_rlp_decode_ERR_NOT_BYTES">ERR_NOT_BYTES</a>);
    };
    output
}
</code></pre>



</details>

<a id="0x1_rlp_decode_append_u8a_to"></a>

## Function `append_u8a_to`



<pre><code><b>fun</b> <a href="decode.md#0x1_rlp_decode_append_u8a_to">append_u8a_to</a>(dest: &<b>mut</b> <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, src: &<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, offset: u64, size: u64)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="decode.md#0x1_rlp_decode_append_u8a_to">append_u8a_to</a>(dest: &<b>mut</b> <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, src: &<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, offset: u64, size: u64) {
    <b>let</b> i = 0;
    <b>while</b>(i &lt; size) {
        <b>let</b> b = *<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_borrow">vector::borrow</a>(src, offset + i);
        <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(dest, b);
        i = i + 1;
    };
}
</code></pre>



</details>

<a id="0x1_rlp_decode_decode_bytes_list"></a>

## Function `decode_bytes_list`



<pre><code><b>public</b> <b>fun</b> <a href="decode.md#0x1_rlp_decode_decode_bytes_list">decode_bytes_list</a>(rlp: &<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="decode.md#0x1_rlp_decode_decode_bytes_list">decode_bytes_list</a>(rlp: &<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;&gt; {
    <b>let</b> output: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;&gt; = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>();
    <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(rlp);
    <b>if</b> (len == 0) {
        <b>return</b> output
    };

    <b>let</b> i = 0;
    <b>while</b> (i &lt; len) {
        <b>let</b> (offset, size, type) = <a href="decode.md#0x1_rlp_decode_decode_length">decode_length</a>(rlp, i);

        <b>if</b> (type == <a href="decode.md#0x1_rlp_decode_TYPE_BYTES">TYPE_BYTES</a>) {
            <b>let</b> next = <a href="decode.md#0x1_rlp_decode_decode_bytes">decode_bytes</a>(&<a href="decode.md#0x1_rlp_decode_slice">slice</a>(rlp, i, size + offset - i));
            i = offset + size;
            <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(&<b>mut</b> output, next);
        } <b>else</b> <b>if</b> (type == <a href="decode.md#0x1_rlp_decode_TYPE_LIST">TYPE_LIST</a>) {
            i = offset
        } <b>else</b> {
            <b>assert</b>!(<b>false</b>, <a href="decode.md#0x1_rlp_decode_ERR_NOT_BYTES_LIST">ERR_NOT_BYTES_LIST</a>);
        };
    };
    output
}
</code></pre>



</details>

<a id="0x1_rlp_decode_decode_length"></a>

## Function `decode_length`



<pre><code><b>fun</b> <a href="decode.md#0x1_rlp_decode_decode_length">decode_length</a>(rlp: &<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, offset: u64): (u64, u64, u8)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="decode.md#0x1_rlp_decode_decode_length">decode_length</a>(rlp: &<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, offset: u64): (u64, u64, u8) {
    <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(rlp) - offset;
    <b>if</b> (len == 0) {
        <b>assert</b>!(<b>false</b>, <a href="decode.md#0x1_rlp_decode_ERR_EMPTY">ERR_EMPTY</a>);
    };
    <b>let</b> prefix = *<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_borrow">vector::borrow</a>(rlp, offset);

    <b>if</b> (prefix &lt;= 0x7f) {
        <b>return</b> (offset, 1, <a href="decode.md#0x1_rlp_decode_TYPE_BYTES">TYPE_BYTES</a>)
    };

    <b>if</b>(prefix &lt;= 0xb7 && prefix &gt; 0x7f) {
        <b>return</b> (offset + 1, ((prefix - 0x80) <b>as</b> u64), <a href="decode.md#0x1_rlp_decode_TYPE_BYTES">TYPE_BYTES</a>)
    };

    <b>if</b>(prefix &gt; 0xb7 && prefix &lt;= 0xbf) {
        <b>let</b> len_len = ((prefix - 0xb7) <b>as</b> u64);
        <b>let</b> bytes_len = <a href="decode.md#0x1_rlp_decode_to_integer_within">to_integer_within</a>(rlp, offset + 1, len_len);
        <b>return</b> (offset + 1 + len_len, bytes_len, <a href="decode.md#0x1_rlp_decode_TYPE_BYTES">TYPE_BYTES</a>)
    };

    <b>if</b>(prefix &gt; 0xbf && prefix &lt;= 0xf7) {
        <b>return</b> (offset + 1, ((prefix - 0xc0) <b>as</b> u64), <a href="decode.md#0x1_rlp_decode_TYPE_LIST">TYPE_LIST</a>)
    };

    <b>if</b>(prefix &gt; 0xf7 && prefix &lt;= 0xff) {
        <b>let</b> len_len = ((prefix - 0xf7) <b>as</b> u64);
        <b>let</b> list_len = <a href="decode.md#0x1_rlp_decode_to_integer_within">to_integer_within</a>(rlp, offset + 1, len_len);
        <b>return</b> (offset + 1 + len_len, list_len, <a href="decode.md#0x1_rlp_decode_TYPE_LIST">TYPE_LIST</a>)
    };

    <b>assert</b>!(<b>false</b>, <a href="decode.md#0x1_rlp_decode_ERR_INVALID">ERR_INVALID</a>);
    (0,0,0)
}
</code></pre>



</details>

<a id="0x1_rlp_decode_slice"></a>

## Function `slice`



<pre><code><b>fun</b> <a href="decode.md#0x1_rlp_decode_slice">slice</a>(vec: &<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, offset: u64, size: u64): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="decode.md#0x1_rlp_decode_slice">slice</a>(vec: &<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, offset: u64, size: u64): <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; {
    <b>let</b> ret: <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt; = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_empty">vector::empty</a>();
    <b>let</b> i = 0;
    <b>while</b>(i &lt; size) {
        <b>let</b> b = *<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_borrow">vector::borrow</a>(vec, offset + i);
        <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_push_back">vector::push_back</a>(&<b>mut</b> ret, b);
        i = i + 1;
    };
    <b>return</b> ret
}
</code></pre>



</details>

<a id="0x1_rlp_decode_to_integer"></a>

## Function `to_integer`



<pre><code><b>fun</b> <a href="decode.md#0x1_rlp_decode_to_integer">to_integer</a>(bytes: &<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): u64
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="decode.md#0x1_rlp_decode_to_integer">to_integer</a>(bytes: &<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;): u64 {
    <b>let</b> len = <a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_length">vector::length</a>(bytes);
    <b>if</b> (len == 0) {
        <b>assert</b>!(<b>false</b>, <a href="decode.md#0x1_rlp_decode_ERR_EMPTY">ERR_EMPTY</a>);
        <b>return</b> 0 // never evaluated
    } <b>else</b> <b>if</b> (len == 1) {
        <b>let</b> b = *<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_borrow">vector::borrow</a>(bytes, 0);
        <b>return</b> (b <b>as</b> u64)
    } <b>else</b> {
        <b>let</b> last = *<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_borrow">vector::borrow</a>(bytes, len - 1);
        <b>let</b> left = <a href="decode.md#0x1_rlp_decode_to_integer">to_integer</a>(&<a href="decode.md#0x1_rlp_decode_slice">slice</a>(bytes, 0, len - 1));
        <b>return</b> (last <b>as</b> u64) + left * 256
    }
}
</code></pre>



</details>

<a id="0x1_rlp_decode_to_integer_within"></a>

## Function `to_integer_within`



<pre><code><b>fun</b> <a href="decode.md#0x1_rlp_decode_to_integer_within">to_integer_within</a>(bytes: &<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, offset: u64, size: u64): u64
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>fun</b> <a href="decode.md#0x1_rlp_decode_to_integer_within">to_integer_within</a>(bytes: &<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector">vector</a>&lt;u8&gt;, offset: u64, size: u64): u64 {
    <b>if</b> (size == 0) {
        <b>assert</b>!(<b>false</b>, <a href="decode.md#0x1_rlp_decode_ERR_EMPTY">ERR_EMPTY</a>);
        <b>return</b> 0 // never evaluated
    } <b>else</b> <b>if</b> (size == 1) {
        <b>let</b> b = *<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_borrow">vector::borrow</a>(bytes, offset);
        <b>return</b> (b <b>as</b> u64)
    } <b>else</b> {
        <b>let</b> last = *<a href="../../aptos-stdlib/../move-stdlib/doc/vector.md#0x1_vector_borrow">vector::borrow</a>(bytes, offset + size - 1);
        <b>let</b> left = <a href="decode.md#0x1_rlp_decode_to_integer_within">to_integer_within</a>(bytes, offset, size - 1);
        <b>return</b> (last <b>as</b> u64) + left * 256
    }
}
</code></pre>



</details>


[move-book]: https://aptos.dev/move/book/SUMMARY
