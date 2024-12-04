
/// Specification for the Ethereum module
spec aptos_framework::eip55 {

    spec EthereumAddress {
        invariant len(inner) == ETH_ADDRESS_LENGTH;
    }

    /// Expected properties:
    /// 1. never aborts
    /// 2. preserves length
    /// 3. do not modify non ascii characters
    spec to_lowercase(xs: &vector<u8>): vector<u8> {
        //   never aborts
        aborts_if false;
        //  returns same length
        ensures len(result) == len(xs);
        //  result is ascii-equivalent to xs
        ensures lowercase_congruent(result, xs);
    }

    /// Expected properties:
    /// 1. never aborts
    /// 2. preserves length and ascii characters
    spec to_lowercase_ascii_letter(l: u8): u8 {
        aborts_if false;
        ensures same_ascii_letters(l, result);
    }

    /// Expected properties:
    /// 1. aborts if not a valid length 
    /// 2. result has same preserves length
    /// 3. result is ascii-equivalent to input
    spec to_eip55_checksumed_address(a: &vector<u8>): EthereumAddress {
        aborts_if len(a) != ETH_ADDRESS_LENGTH;
        aborts_if !(forall k: u64 where k < len(a): is_hex_digit(a[k]));
        ensures  lowercase_congruent(a, result.inner);
    }

    spec is_hex_digit_vector(xs: &vector<u8>): bool {
        aborts_if false;
        // ensures (forall k: u64 where k < len(xs): is_hex_digit(xs[k])) ==> (result == true);
        ensures result == true <==> (forall k: u64 where k < len(xs): is_hex_digit(xs[k])); 
    }
    // spec fun to_lowercase(xs: vector<u8>): vector<u8> {
    //     // aborts_if false;
    //     // ensures len(result) == len(xs);
    //     // ensures lowercase_congruent(result, xs);
    //     xs
    // }

    /// Expected properties:
    /// 
    spec assert_eip55(a: &vector<u8>) {
        // requires len(a) == ETH_ADDRESS_LENGTH;
        // requires forall k: u64 where k < len(a): is_ascii_letter(a[k]);
        pragma aborts_if_is_partial = true;
        aborts_if len(a) != ETH_ADDRESS_LENGTH;
        aborts_if !(forall k: u64 where k < len(a): is_hex_digit(a[k])); 
        aborts_if exists k: u64 where k < len(a): !is_hex_digit(a[k]); 
        // let lowercase_version = to_lowercase(ethereum_address);
        // let hash = keccak256(ethereum_address);
        // aborts_if !lowercase_congruent(ethereum_address, to_eip55_checksumed_address(ethereum_address));
    }

    // spec fun 

    // spec fun lemma_eip55_compliant(ethereum_address: &vector<u8>, hash: &vector<u8>): bool {
    //     // assert!(hash == keccak256(to_lowercase(ethereum_address)));
    //     lowercase_congruent(ethereum_address, to_eip55_checksumed_address(ethereum_address))
    //     // aborts_if false;
    //     // ensures ethereum_address == to_eip55_checksumed_address(ethereum_address);
    // }
    
    spec is_eip55_compliant(a: &vector<u8>): bool {
        pragma aborts_if_is_partial = true;
        aborts_if len(a) != ETH_ADDRESS_LENGTH;
        // a == to_eip55_checksumed_address(a)   
    }

    spec fun is_ok(ethereum_address: vector<u8>): bool {
        (len(ethereum_address) == ETH_ADDRESS_LENGTH) 
        && (forall k: u64 where k < len(ethereum_address): is_hex_digit(ethereum_address[k]))
    }

    /// this function is never used
    // spec get_inner(eth_address: &EthereumAddress): vector<u8> {
    //     aborts_if false;
    //     ensures len(result) == ETH_ADDRESS_LENGTH;
    // }

    /// Helpers specifications functions
    
    /// Whether two chars are the same letter, ignoring case.
    spec fun same_ascii_letters(l: u8, m: u8): bool {
        to_lowercase_ascii_letter(l) == to_lowercase_ascii_letter(m)
    }

    /// Whether a character is a lowercase ASCII letter.
    spec fun is_lowercase_ascii_letter(l: u8): bool {
        l >= ASCII_A_LOWERCASE && l <= ASCII_Z_LOWERCASE
    }

    /// Whether a character is an uppercase ASCII letter.
    spec fun is_uppercase_ascii_letter(l: u8): bool {
        l >= ASCII_A && l <= ASCII_Z
    }

    /// Whether a character is an ASCII letter.
    spec fun is_ascii_letter(l: u8): bool {
        is_lowercase_ascii_letter(l) || is_uppercase_ascii_letter(l)
    }

   
    /// Whether two vectors of ASCII characters have the same letters, ignoring case.
    spec fun lowercase_congruent(v1: vector<u8>, v2: vector<u8>): bool {
        len(v1) == len(v2)
        && (forall k: u64 where k < len(v1): same_ascii_letters(v1[k], v2[k]))
    }
}
