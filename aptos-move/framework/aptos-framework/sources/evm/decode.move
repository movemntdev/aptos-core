// https://ethereum.org/en/developers/docs/data-structures-and-encoding/rlp/
module aptos_framework::rlp_decode {
    use std::vector;

    const ERR_EMPTY: u64 = 0;
    const ERR_INVALID: u64 = 1;
    const ERR_NOT_BYTES: u64 = 2;
    const ERR_NOT_LIST: u64 = 3;
    const ERR_NOT_BYTES_LIST: u64 = 4;

    const TYPE_BYTES: u8 = 0;
    const TYPE_LIST: u8 = 1;

    public fun decode_bytes(rlp: &vector<u8>): vector<u8> {
        let output: vector<u8> = vector::empty();
        let len = vector::length(rlp);
        if (len == 0) {
            return output
        };

        let (offset, size, type) = decode_length(rlp, 0);
        if (type == TYPE_BYTES) {
            append_u8a_to(&mut output, rlp, offset, size);
        } else {
            assert!(false, ERR_NOT_BYTES);
        };
        output
    }

    fun append_u8a_to(dest: &mut vector<u8>, src: &vector<u8>, offset: u64, size: u64) {
        let i = 0;
        while(i < size) {
            let b = *vector::borrow(src, offset + i);
            vector::push_back(dest, b);
            i = i + 1;
        };
    }

    // TODO
    public fun decode_bytes_list(rlp: &vector<u8>): vector<vector<u8>> {
        let output: vector<vector<u8>> = vector::empty();
        let len = vector::length(rlp);
        if (len == 0) {
            return output
        };

        let i = 0;
        while (i < len) {
            let (offset, size, type) = decode_length(rlp, i);

            if (type == TYPE_BYTES) {
                let next = decode_bytes(&slice(rlp, i, size + offset - i));
                i = offset + size;
                vector::push_back(&mut output, next);
            } else if (type == TYPE_LIST) {
                i = offset
            } else {
                assert!(false, ERR_NOT_BYTES_LIST);
            };
        };
        output
    }

    // return: (offset, len, type)
    // type
    // - 0: bytes
    // - 1: bytes_list
    fun decode_length(rlp: &vector<u8>, offset: u64): (u64, u64, u8) {
        let len = vector::length(rlp) - offset;
        if (len == 0) {
            assert!(false, ERR_EMPTY);
        };
        let prefix = *vector::borrow(rlp, offset);

        if (prefix <= 0x7f) {
            return (offset, 1, TYPE_BYTES)
        };

        if(prefix <= 0xb7 && prefix > 0x7f) {
            return (offset + 1, ((prefix - 0x80) as u64), TYPE_BYTES)
        };

        if(prefix > 0xb7 && prefix <= 0xbf) {
            let len_len = ((prefix - 0xb7) as u64);
            let bytes_len = to_integer_within(rlp, offset + 1, len_len);
            return (offset + 1 + len_len, bytes_len, TYPE_BYTES)
        };

        if(prefix > 0xbf && prefix <= 0xf7) {
            return (offset + 1, ((prefix - 0xc0) as u64), TYPE_LIST)
        };

        if(prefix > 0xf7 && prefix <= 0xff) {
            let len_len = ((prefix - 0xf7) as u64);
            let list_len = to_integer_within(rlp, offset + 1, len_len);
            return (offset + 1 + len_len, list_len, TYPE_LIST)
        };

        assert!(false, ERR_INVALID);
        (0,0,0)
    }

    fun slice(vec: &vector<u8>, offset: u64, size: u64): vector<u8> {
        let ret: vector<u8> = vector::empty();
        let i = 0;
        while(i < size) {
            let b = *vector::borrow(vec, offset + i);
            vector::push_back(&mut ret, b);
            i = i + 1;
        };
        return ret
    }

    fun to_integer(bytes: &vector<u8>): u64 {
        let len = vector::length(bytes);
        if (len == 0) {
            assert!(false, ERR_EMPTY);
            return 0 // never evaluated
        } else if (len == 1) {
            let b = *vector::borrow(bytes, 0);
            return (b as u64)
        } else {
            let last = *vector::borrow(bytes, len - 1);
            let left = to_integer(&slice(bytes, 0, len - 1));
            return (last as u64) + left * 256
        }
    }

    fun to_integer_within(bytes: &vector<u8>, offset: u64, size: u64): u64 {
        if (size == 0) {
            assert!(false, ERR_EMPTY);
            return 0 // never evaluated
        } else if (size == 1) {
            let b = *vector::borrow(bytes, offset);
            return (b as u64)
        } else {
            let last = *vector::borrow(bytes, offset + size - 1);
            let left = to_integer_within(bytes, offset, size - 1);
            return (last as u64) + left * 256
        }
    }
}