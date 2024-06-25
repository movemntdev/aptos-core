
<a id="0x1_evm_arithmetic"></a>

# Module `0x1::evm_arithmetic`



-  [Constants](#@Constants_0)
-  [Function `add_sign`](#0x1_evm_arithmetic_add_sign)
-  [Function `get_sign`](#0x1_evm_arithmetic_get_sign)
-  [Function `add`](#0x1_evm_arithmetic_add)
-  [Function `smod`](#0x1_evm_arithmetic_smod)
-  [Function `sdiv`](#0x1_evm_arithmetic_sdiv)


<pre><code><b>use</b> <a href="../../aptos-stdlib/doc/debug.md#0x1_debug">0x1::debug</a>;
</code></pre>



<a id="@Constants_0"></a>

## Constants


<a id="0x1_evm_arithmetic_U255_MAX"></a>



<pre><code><b>const</b> <a href="arithmetic.md#0x1_evm_arithmetic_U255_MAX">U255_MAX</a>: u256 = 57896044618658097711785492504343953926634992332820282019728792003956564819967;
</code></pre>



<a id="0x1_evm_arithmetic_U256_MAX"></a>



<pre><code><b>const</b> <a href="arithmetic.md#0x1_evm_arithmetic_U256_MAX">U256_MAX</a>: u256 = 115792089237316195423570985008687907853269984665640564039457584007913129639935;
</code></pre>



<a id="0x1_evm_arithmetic_add_sign"></a>

## Function `add_sign`



<pre><code><b>public</b> <b>fun</b> <a href="arithmetic.md#0x1_evm_arithmetic_add_sign">add_sign</a>(value: u256, sign: bool): u256
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="arithmetic.md#0x1_evm_arithmetic_add_sign">add_sign</a>(value: u256, sign: bool): u256 {
    <b>if</b>(sign && value &gt; 0) {
        <a href="arithmetic.md#0x1_evm_arithmetic_U256_MAX">U256_MAX</a> - value + 1
    } <b>else</b> {
        value
    }
}
</code></pre>



</details>

<a id="0x1_evm_arithmetic_get_sign"></a>

## Function `get_sign`



<pre><code><b>public</b> <b>fun</b> <a href="arithmetic.md#0x1_evm_arithmetic_get_sign">get_sign</a>(num: u256): (bool, u256)
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="arithmetic.md#0x1_evm_arithmetic_get_sign">get_sign</a>(num: u256): (bool, u256) {
    <b>let</b> neg = <b>false</b>;
    <b>if</b>(num &gt; <a href="arithmetic.md#0x1_evm_arithmetic_U255_MAX">U255_MAX</a>) {
        neg = <b>true</b>;
        num = <a href="arithmetic.md#0x1_evm_arithmetic_U256_MAX">U256_MAX</a> - num + 1;
    };
    (neg, num)
}
</code></pre>



</details>

<a id="0x1_evm_arithmetic_add"></a>

## Function `add`



<pre><code><b>public</b> <b>fun</b> <a href="arithmetic.md#0x1_evm_arithmetic_add">add</a>(a: u256, b: u256): u256
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="arithmetic.md#0x1_evm_arithmetic_add">add</a>(a: u256, b: u256): u256 {
    <b>if</b>(a &gt; 0 && b &gt;= (<a href="arithmetic.md#0x1_evm_arithmetic_U256_MAX">U256_MAX</a> - a + 1)) {
        b - (<a href="arithmetic.md#0x1_evm_arithmetic_U256_MAX">U256_MAX</a> - a + 1)
    } <b>else</b> {
        a + b
    }
}
</code></pre>



</details>

<a id="0x1_evm_arithmetic_smod"></a>

## Function `smod`



<pre><code><b>public</b> <b>fun</b> <a href="arithmetic.md#0x1_evm_arithmetic_smod">smod</a>(a: u256, b: u256): u256
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="arithmetic.md#0x1_evm_arithmetic_smod">smod</a>(a: u256, b: u256): u256 {
    <b>let</b>(sg_a, num_a) = <a href="arithmetic.md#0x1_evm_arithmetic_get_sign">get_sign</a>(a);
    <b>let</b>(_sg_b, num_b) = <a href="arithmetic.md#0x1_evm_arithmetic_get_sign">get_sign</a>(b);
    <b>let</b> num_c = num_a % num_b;
    <a href="arithmetic.md#0x1_evm_arithmetic_add_sign">add_sign</a>(num_c, sg_a)
}
</code></pre>



</details>

<a id="0x1_evm_arithmetic_sdiv"></a>

## Function `sdiv`



<pre><code><b>public</b> <b>fun</b> <a href="arithmetic.md#0x1_evm_arithmetic_sdiv">sdiv</a>(a: u256, b: u256): u256
</code></pre>



<details>
<summary>Implementation</summary>


<pre><code><b>public</b> <b>fun</b> <a href="arithmetic.md#0x1_evm_arithmetic_sdiv">sdiv</a>(a: u256, b: u256): u256 {
    <b>let</b>(sg_a, num_a) = <a href="arithmetic.md#0x1_evm_arithmetic_get_sign">get_sign</a>(a);
    <b>let</b>(sg_b, num_b) = <a href="arithmetic.md#0x1_evm_arithmetic_get_sign">get_sign</a>(b);
    <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&sg_a);
    <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&num_a);
    <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&sg_b);
    <a href="../../aptos-stdlib/doc/debug.md#0x1_debug_print">debug::print</a>(&num_b);
    <b>let</b> num_c = num_a / num_b;
    <a href="arithmetic.md#0x1_evm_arithmetic_add_sign">add_sign</a>(num_c, (!sg_a && sg_b) || (sg_a && !sg_b))
}
</code></pre>



</details>


[move-book]: https://aptos.dev/move/book/SUMMARY
