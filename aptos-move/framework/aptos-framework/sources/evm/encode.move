// https://ethereum.org/en/developers/docs/data-structures-and-encoding/rlp/
module aptos_framework::rlp_encode {
    use std::vector;

    const CONST_256_EXP_8: u128 = 18446744073709551616;

    const ERR_TOO_LONG_BYTE_ARRAY: u64 = 0;

    public fun encode_bytes_list(inputs: vector<vector<u8>>): vector<u8> {
        let output = vector::empty();

        let i = 0;
        let len = vector::length(&inputs);
        while(i < len) {
            let next = vector::borrow(&inputs, i);
            let next = encode_bytes(*next);
            vector::append(&mut output, next);
            i = i + 1;
        };

        let left = encode_length(&output, 0xc0);
        vector::append(&mut left, output);
        return left
    }

    public fun encode_bytes(input: vector<u8>): vector<u8> {
        if (vector::length(&input) == 1 && *vector::borrow(&input, 0) < 0x80) {
            return input
        } else {
            let left = encode_length(&input, 0x80);
            vector::append(&mut left, input);
            return left
        }
    }

    fun encode_length(input: &vector<u8>, offset: u8): vector<u8> {
        let len = vector::length(input);
        if (len < 56) {
            return to_byte((len as u8) + offset)
        };
        assert!((len as u128) < CONST_256_EXP_8, ERR_TOO_LONG_BYTE_ARRAY);
        let bl = to_binary(len);
        let len_bl = vector::length(&bl);
        let left = to_byte((len_bl as u8) + offset + 55);
        vector::append(&mut left, bl);
        return left
    }

    fun to_binary(x: u64): vector<u8> {
        if (x == 0) {
            return vector::empty()
        } else {
            let left = to_binary(x / 256);
            let mod = x % 256;
            let right = to_byte((mod as u8));
            vector::append(&mut left, right);
            return left
        }
    }

    fun to_byte(val: u8): vector<u8> {
        let v = vector::empty<u8>();
        vector::push_back(&mut v, val);
        v
    }
}

