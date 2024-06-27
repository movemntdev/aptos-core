module aptos_framework::evm_util {
    use std::vector;
    use aptos_std::aptos_hash::keccak256;
    use aptos_framework::rlp_encode::encode_bytes_list;

    const U256_MAX: u256 = 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    const U255_MAX: u256 = 57896044618658097711785492504343953926634992332820282019728792003956564819967;
    const ZERO_EVM_ADDR: vector<u8> = x"";

    const TX_FORMAT: u64 = 20001;

    public fun slice(data: vector<u8>, pos: u256, size: u256): vector<u8> {
        let s = vector::empty<u8>();
        let i = 0;
        let len = vector::length(&data);
        while (i < size) {
            let p = ((pos + i) as u64);
            if(p >= len) {
                vector::push_back(&mut s, 0);
            } else {
                vector::push_back(&mut s, *vector::borrow(&data, (pos + i as u64)));
            };

            i = i + 1;
        };
        s
    }

    public fun to_32bit(data: vector<u8>): vector<u8> {
        let bytes = vector::empty<u8>();
        let len = vector::length(&data);
        // debug::print(&len);
        while(len < 32) {
            vector::push_back(&mut bytes, 0);
            len = len + 1
        };
        vector::append(&mut bytes, data);
        bytes
    }

    public fun get_contract_address(addr: vector<u8>, nonce: u64): vector<u8> {
        let nonce_bytes = vector::empty<u8>();
        let l = 0;
        while(nonce > 0) {
            l = l + 1;
            vector::push_back(&mut nonce_bytes, ((nonce % 0x100) as u8));
            nonce = nonce / 0x100;
        };
        vector::reverse(&mut nonce_bytes);
        let salt = encode_bytes_list(vector[slice(addr, 12, 20), nonce_bytes]);
        to_32bit(slice(keccak256(salt), 12, 20))
    }

    public fun power(base: u256, exponent: u256): u256 {
        let result = 1;

        let i = 0;
        while (i < exponent) {
            result = result * base;
            i = i + 1;
        };

        result
    }

    public fun to_int256(num: u256): (bool, u256) {
        let neg = false;
        if(num > U255_MAX) {
            neg = true;
            num = U256_MAX - num + 1;
        };
        (neg, num)
    }

    public fun add_sign(value: u256, sign: bool): u256 {
        if(sign) {
            U256_MAX - value + 1
        } else {
            value
        }
    }

    public fun to_u256(data: vector<u8>): u256 {
        let res = 0;
        let i = 0;
        let len = vector::length(&data);
        while (i < len) {
            let value = *vector::borrow(&data, i);
            res = (res << 8) + (value as u256);
            i = i + 1;
        };
        res
    }

    public fun data_to_u256(data: vector<u8>, p: u256, size: u256): u256 {
        let res = 0;
        let i = 0;
        let len = (vector::length(&data) as u256);
        assert!(size <= 32, 1);
        while (i < size) {
            if(p + i < len) {
                let value = *vector::borrow(&data, ((p + i) as u64));
                res = (res << 8) + (value as u256);
            } else {
                res = res << 8
            };

            i = i + 1;
        };

        res
    }

    public fun u256_to_data(num256: u256): vector<u8> {
        let res = vector::empty<u8>();
        let i = 32;
        while(i > 0) {
            i = i - 1;
            let shifted_value = num256 >> (i * 8);
            let byte = ((shifted_value & 0xff) as u8);
            vector::push_back(&mut res, byte);
        };
        res
    }

    public fun mstore(memory: &mut vector<u8>, pos: u256, data: vector<u8>) {
        let len_m = vector::length(memory);
        let len_d = vector::length(&data);
        let p = (pos as u64);
        while(len_m < p) {
            vector::push_back(memory, 0);
            len_m = len_m + 1
        };

        let i = 0;
        while (i < len_d) {
            if(len_m <= p + i) {
                vector::push_back(memory, *vector::borrow(&data, i));
                len_m = len_m + 1;
            } else {
                *vector::borrow_mut(memory, p + i) = *vector::borrow(&data, i);
            };

            i = i + 1
        };
    }

    public fun get_message_hash(input: vector<vector<u8>>): vector<u8> {
        let i = 0;
        let len = vector::length(&input);
        let content = vector::empty<u8>();
        while(i < len) {
            let item = vector::borrow(&input, i);
            let item_len = vector::length(item);
            let encoded = if(item_len == 1 && *vector::borrow(item, 0) < 0x80) *item else encode_data(item, 0x80);
            vector::append(&mut content, encoded);
            i = i + 1;
        };

        encode_data(&content, 0xc0)
    }

    public fun u256_to_trimed_data(num: u256): vector<u8> {
        trim(u256_to_data(num))
    }

    public fun trim(data: vector<u8>): vector<u8> {
        let i = 0;
        let len = vector::length(&data);
        while (i < len) {
            let ith = *vector::borrow(&data, i);
            if(ith != 0) {
                break
            };
            i = i + 1
        };
        slice(data, (i as u256), ((len - i) as u256))
    }



    // public fun decode_legacy_tx(data: vector<u8>): (u64, u256, u256, vector<u8>, u256, vector<u8>, u64, vector<u8>, vector<u8>) {
    // public fun decode_legacy_tx(data: vector<u8>) {
    //     let first_byte = *vector::borrow(&data, 0);
    //     let len = (vector::length(&data) as u256);
    //     if(first_byte > 0xf7) {
    //         let l = ((first_byte - 0xf7) as u256);
    //         let ll = to_u64(slice(data, 1, l));
    //         assert!(ll > 56, TX_FORMAT);
    //         let inner_bytes = slice(data, l + 1, len - l - 1);
    //         while()
    //     }
    // }

    fun hex_length(len: u64): (u8, vector<u8>) {
        let res = 0;
        let bytes = vector::empty<u8>();
        while(len > 0) {
            res = res + 1;
            vector::push_back(&mut bytes, ((len % 256) as u8));
            len = len / 256;
        };
        vector::reverse(&mut bytes);
        (res, bytes)
    }

    fun encode_data(data: &vector<u8>, offset: u8): vector<u8> {
        let len = vector::length(data);
        let res = vector::empty<u8>();
        if(len < 56) {
            vector::push_back(&mut res, (len as u8) + offset);
        } else {
            let(hex_len, len_bytes) = hex_length(len);
            vector::push_back(&mut res, hex_len + offset + 55);
            vector::append(&mut res, len_bytes);
        };
        vector::append(&mut res, *data);
        res
    }
}

