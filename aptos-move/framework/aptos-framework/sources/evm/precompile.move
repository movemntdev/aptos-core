module aptos_framework::precompile {
    use std::vector;
    use aptos_framework::evm_util::{slice, to_u256, to_32bit};
    use aptos_std::secp256k1::{ecdsa_recover, ecdsa_signature_from_bytes, ecdsa_raw_public_key_to_bytes};
    use aptos_std::aptos_hash::{keccak256, ripemd160};
    use std::option::borrow;
    use aptos_std::debug;
    use std::hash::sha2_256;

    /// unsupport precomile address
    const UNSUPPORT: u64 = 50001;
    /// invalid precomile calldata length
    const CALL_DATA_LENGTH: u64 = 50002;
    /// mod exp len params invalid
    const MOD_PARAMS_SISE: u64 = 50003;

    // precompile address list
    const RCRECOVER: vector<u8> = x"0000000000000000000000000000000000000000000000000000000000000001";
    const SHA256: vector<u8> = x"0000000000000000000000000000000000000000000000000000000000000002";
    const RIPEMD: vector<u8> = x"0000000000000000000000000000000000000000000000000000000000000003";
    const IDENTITY: vector<u8> = x"0000000000000000000000000000000000000000000000000000000000000004";
    const MODEXP: vector<u8> = x"0000000000000000000000000000000000000000000000000000000000000005";
    const ECADD: vector<u8> = x"0000000000000000000000000000000000000000000000000000000000000006";
    const ECMUL: vector<u8> = x"0000000000000000000000000000000000000000000000000000000000000007";
    const ECPAIRING: vector<u8> = x"0000000000000000000000000000000000000000000000000000000000000008";
    const BLAKE2F: vector<u8> = x"0000000000000000000000000000000000000000000000000000000000000009";

    #[view]
    public fun run_precompile(addr: vector<u8>, calldata: vector<u8>, chain_id: u64): vector<u8> {
        if(addr == RCRECOVER) {
            assert!(vector::length(&calldata) == 128, CALL_DATA_LENGTH);
            let message_hash = slice(calldata, 0, 32);
            let v = (to_u256(slice(calldata, 32, 32)) as u64);
            let signature = ecdsa_signature_from_bytes(slice(calldata, 64, 64));

            let recovery_id = if(v > 28) ((v - (chain_id * 2) - 35) as u8) else ((v - 27) as u8);
            let pk_recover = ecdsa_recover(message_hash, recovery_id, &signature);
            let pk = keccak256(ecdsa_raw_public_key_to_bytes(borrow(&pk_recover)));
            debug::print(&slice(pk, 12, 20));
            to_32bit(slice(pk, 12, 20))
        } else if(addr == SHA256) {
            sha2_256(calldata)
        } else if(addr == RIPEMD) {
            debug::print(&to_32bit(ripemd160(calldata)));
            to_32bit(ripemd160(calldata))
        } else if(addr == IDENTITY) {
            calldata
        } else {
            assert!(false, (to_u256(addr) as u64));
            x""
        }
    }

    #[view]
    public fun is_precompile_address(addr: vector<u8>): bool {
        let num = to_u256(addr);
        num >= 0x01 && num <= 0x0a
    }

}