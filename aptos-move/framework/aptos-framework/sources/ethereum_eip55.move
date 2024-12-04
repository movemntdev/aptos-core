/// Provides EIP-55 for Ethereum addresses
///
/// [EIP-55](https://eips.ethereum.org/EIPS/eip-55) increases the confidence that
/// an address is not random.
module aptos_framework::eip55 {
    use std::vector;
    use aptos_std::aptos_hash::keccak256;

    #[test_only]
    use std::debug; 
    #[test_only]
    use std::string::utf8;

    /// Error codes
    const ENOT_ETH_ADDRESS_LENGTH: u64 = 0x1;
    const ENOT_EIP55_ADDRESS: u64 = 0x2;

    /// Length of an Ethereum address in hex chars (u8)
    const ETH_ADDRESS_LENGTH: u64 = 40;

    /// Distance between lowercase and uppercase letter
    /// If c is char in uppercase, c + 0x20 is the lowercase equivalent
    const UPPER_TO_LOWER: u8 = 0x20;

    /// Constants for ASCII character codes
    const ASCII_A: u8 = 0x41;
    const ASCII_F: u8 = 0x46;
    const ASCII_Z: u8 = 0x5A;
    const ASCII_A_LOWERCASE: u8 = 0x61;
    const ASCII_F_LOWERCASE: u8 = 0x66;
    const ASCII_Z_LOWERCASE: u8 = 0x7A;

    const ASCII_0 : u8 = 0x30;
    const ASCII_9 : u8 = 0x39;

    /// Represents an Ethereum address 
    /// Provides structured handling, storage, and validation of Ethereum addresses.
    struct EthereumAddress has store, copy, drop {
        inner: vector<u8>
    }

    /// Validates an Ethereum address against EIP-55 checksum rules and returns a new `EthereumAddress`.
    ///
    /// @param ethereum_address A 40-byte vector of unsigned 8-bit integers (hexadecimal format).
    /// @return A validated `EthereumAddress` struct.
    /// @abort If the address does not conform to EIP-55 standards.
    public fun ethereum_address(ethereum_address: vector<u8>): EthereumAddress {
        assert_eip55(&ethereum_address);
        EthereumAddress { inner: ethereum_address }
    }

    // Helpers 

    /// Whether a value u8 represnets an hexadecimal digit 0-9, a-f or A-F.
    fun is_hex_digit(l: u8): bool {
           (l >= ASCII_A && l <= ASCII_F)
        || (l >= ASCII_0 && l <= ASCII_9)
        || (l >= ASCII_A_LOWERCASE && l <= ASCII_F_LOWERCASE)
    }

    /// Whether a vector of u8 represents a valid hexadecimal string.
    fun is_hex_digit_vector(xs: &vector<u8>): bool {
        let i = 0;
        while ({
            spec {
                invariant i <= vector::length(xs);
                invariant forall k: u64 where k < i: is_hex_digit(xs[k]);
            };
            i < vector::length(xs)
        }) {
            if (!is_hex_digit(*vector::borrow(xs, i))) {
                // spec {
                //     assert exists k: u64 where k <= i:
                //         !is_hex_digit(xs[k]);
                // };
                return false
            };
            i = i + 1;
        };
        spec {
            assert forall k: u64 where k < len(xs) : is_hex_digit(xs[k]);
        };
        return true
    }

    /// Converts a letter to its lowercase equivalent if it is an ASCII letter.
    /// 
    /// This is implemented as a shift of +32 in ASCII encoding.
    fun to_lowercase_ascii_letter(l: u8): u8 {
        if (l >= ASCII_A && l <= ASCII_Z) {
            l + UPPER_TO_LOWER
        } else { l }
    }

    /// Converts a letter to its uppercase equivalent if it is an ASCII letter.
    /// 
    /// This is implemented as a shift of -32 in ASCII encoding.
    fun to_uppercase_ascii_letter(l: u8): u8 {
        if (l >= ASCII_A_LOWERCASE && l <= ASCII_Z_LOWERCASE) {
            l - UPPER_TO_LOWER
        } else { l }
    }

    /// Converts uppercase ASCII characters in a vector to their lowercase equivalents.
    ///
    /// @param input A reference to a vector of ASCII characters.
    /// @return A new vector with lowercase equivalents of the input characters.
    /// @note Only affects ASCII letters; non-alphabetic characters are unchanged.
    public fun to_lowercase(xs: &vector<u8>): vector<u8> {
        let i = 0;
        let lowercase_bytes = vector::empty();
        while ({
            spec {
                invariant len(lowercase_bytes) == i;
                invariant i <= len(xs);
                invariant forall k: u64 where k < i:
                    !is_uppercase_ascii_letter(xs[k]) ==>
                        lowercase_bytes[k] == xs[k];
                invariant forall k: u64 where k < i:
                    same_ascii_letters(lowercase_bytes[k], xs[k]);
            };
            i < vector::length(xs)
        }) {
            let element = *vector::borrow(xs, i);
            let lower_byte = to_lowercase_ascii_letter(element);
            i = i + 1;
            vector::push_back<u8>(&mut lowercase_bytes, lower_byte);
        };
        spec {
            assert len(lowercase_bytes) == len(xs);
            assert lowercase_congruent(lowercase_bytes, xs);
        };
        lowercase_bytes
    }

    #[test]
    fun test_to_lowercase() {
        let upper = b"TeST";
        let lower = b"test";
        assert!(to_lowercase(&upper) == lower, 0);

        assert!(to_lowercase(&b"ABCDEFGHIJKLMNOPQRSTUVWXYZ") == b"abcdefghijklmnopqrstuvwxyz",0);
    }

    /// Converts an Ethereum address to EIP-55 checksummed format.
    ///
    /// @param ethereum_address A 40-character vector representing the Ethereum address in hexadecimal format.
    /// @return The EIP-55 checksummed version of the input address.
    /// @abort If the input address does not have exactly 40 characters.
    /// @note Assumes input address is valid and in lowercase hexadecimal format.
    public fun to_eip55_checksumed_address(a: &vector<u8>): EthereumAddress 
    // vector<u8> 
    {
        assert!(vector::length(a) == ETH_ADDRESS_LENGTH, ENOT_ETH_ADDRESS_LENGTH);
        assert!(is_hex_digit_vector(a), ENOT_EIP55_ADDRESS);
        let lowercase = to_lowercase(a);
        let hash = keccak256(lowercase);
        let output = vector::empty<u8>();
        let index = 0;
        while ({
            spec {
                invariant len(output) == index;
                invariant index <= ETH_ADDRESS_LENGTH;
                invariant forall k: u64 where k < index:
                    same_ascii_letters(output[k], lowercase[k]);
            };
            index < ETH_ADDRESS_LENGTH
            }) {
            // character at position index in the ethereum address
            let item = *vector::borrow(a, index);
            // The hash is a 64-byte vector, and every byte contributes two letters
            // The corresponding character in the hash is in the element at position index / 2
            let hash_item = *vector::borrow(&hash, index / 2);
            let hash_ascii_char = if ((index % 2) == 0) {
                // If index is even, we take the leftmost 4 bits of the byte at index / 2
                hash_item / 16
            } else {
                // If index is odd, we take the rightmost 4 bits of the byte at index / 2
                hash_item % 16
            };
            // If the hash character is greater or equal to 8, we convert the character to uppercase
            if (hash_ascii_char >= 8) {
                    vector::push_back(&mut output, to_uppercase_ascii_letter(item));
            } else {
                    vector::push_back(&mut output, item);
            };
            index = index + 1;
        };
        EthereumAddress { inner:  output }
    }

    /// this function is never used
    // public fun get_inner(eth_address: &EthereumAddress): vector<u8> {
    //     eth_address.inner
    // }

    public fun is_eip55_compliant(a: &vector<u8>): bool {
        assert!(vector::length(a) == ETH_ADDRESS_LENGTH, ENOT_ETH_ADDRESS_LENGTH);
        assert!(is_hex_digit_vector(a), ENOT_EIP55_ADDRESS);
        let eip55 = to_eip55_checksumed_address(a);
        a == &eip55.inner
    }

    /// Checks if an Ethereum address conforms to the EIP-55 checksum standard.
    ///
    /// @param a A reference to a 40-character vector of an Ethereum address in hexadecimal format.
    /// @abort If the address does not match its EIP-55 checksummed version.
    /// @note Assumes the address is correctly formatted as a 40-character hexadecimal string.
    public fun assert_eip55(a: &vector<u8>) {
        let eip55 = to_eip55_checksumed_address(a);
        assert!(a == &eip55.inner, ENOT_EIP55_ADDRESS);
    }

    #[test_only]
    public fun valid_eip55(): vector<u8> {
        b"32Be343B94f860124dC4fEe278FDCBD38C102D88"
    }

    #[test_only]
    public fun invalid_eip55(): vector<u8> {
        b"32be343b94f860124dc4fee278fdcbd38c102d88"
    }

    #[test]
    fun test_valid_eip55_checksum() {
        assert_eip55(&valid_eip55());
    }

    #[test]
    fun foo() {
        let a = b"32Be343B94f860124dC4fEe278FDCBD38C102D88";
        let b = to_lowercase(&a);
        let c = to_eip55_checksumed_address(&b);
        debug::print(&utf8(c.inner));
        assert_eip55(&c.inner);
        // assert!(a == c, 0);
    }

    #[test]
    #[expected_failure(abort_code = ENOT_EIP55_ADDRESS, location = Self)]
    fun test_invalid_eip55_checksum() {
        assert_eip55(&invalid_eip55());
    }

    #[test]
    #[expected_failure(abort_code = ENOT_ETH_ADDRESS_LENGTH, location = Self)]
    fun test_simple_invalid_eip55_checksum() {
        assert_eip55(&b"0");
    }
}
