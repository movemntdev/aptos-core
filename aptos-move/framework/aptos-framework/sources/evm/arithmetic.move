module aptos_framework::evm_arithmetic {
    use aptos_std::debug;

    const U256_MAX: u256 = 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    const U255_MAX: u256 = 57896044618658097711785492504343953926634992332820282019728792003956564819967;

    public fun add_sign(value: u256, sign: bool): u256 {
        if(sign && value > 0) {
            U256_MAX - value + 1
        } else {
            value
        }
    }

    public fun get_sign(num: u256): (bool, u256) {
        let neg = false;
        if(num > U255_MAX) {
            neg = true;
            num = U256_MAX - num + 1;
        };
        (neg, num)
    }

    public fun add(a: u256, b: u256): u256 {
        if(a > 0 && b >= (U256_MAX - a + 1)) {
            b - (U256_MAX - a + 1)
        } else {
            a + b
        }
    }

    public fun smod(a: u256, b: u256): u256 {
        let(sg_a, num_a) = get_sign(a);
        let(_sg_b, num_b) = get_sign(b);
        let num_c = num_a % num_b;
        add_sign(num_c, sg_a)
    }

    public fun sdiv(a: u256, b: u256): u256 {
        let(sg_a, num_a) = get_sign(a);
        let(sg_b, num_b) = get_sign(b);
        debug::print(&sg_a);
        debug::print(&num_a);
        debug::print(&sg_b);
        debug::print(&num_b);
        let num_c = num_a / num_b;
        add_sign(num_c, (!sg_a && sg_b) || (sg_a && !sg_b))
    }

}