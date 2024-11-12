
/// Specification for the Ethereum module
spec aptos_framework::ethereum {

    //  never aborts
    spec ethereum_address_length(): u64 {
        aborts_if false;
    }

    /// Expected properrties:
    /// 1. never aborts
    /// 2. preserves length
    /// 3. do not modify non ascii characters
    spec to_lowercase(input: &vector<u8>): vector<u8> {
        //   never aborts
        aborts_if false;
        //  returns same length
        ensures len(result) == len(input);
        //  result is ascii-equivalent to input
        ensures lowercase_congruent(result, input);
    }

    /// Expected properties:
    /// 1. never aborts
    /// 2. preserves length and ascii characters
    spec to_lowercase_ascii_letter(l: u8): u8 {
        aborts_if false;
        ensures same_ascii_letters(l, result);
    }


    spec to_eip55_checksumed_address(ethereum_address: &vector<u8>): vector<u8> {
        aborts_if len(ethereum_address) != ETH_ADDRESS_LENGTH;
    }

    /// Helpers specifcations functions
    
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

    /// Whetehr two chars are the same letter, ignoring case.
    spec fun same_ascii_letters(l: u8, m: u8): bool {
        to_lowercase_ascii_letter(l) == to_lowercase_ascii_letter(m)
    }

    /// Whether two vectors of ASCII characters have the same letters, ignoring case.
    spec fun lowercase_congruent(v1: vector<u8>, v2: vector<u8>): bool {
        len(v1) == len(v2)
        && (forall k: u64 where k < len(v1): same_ascii_letters(v1[k], v2[k]))
    }
}

spec aptos_framework::atomic_bridge_store {
    spec initialize {
        let addr = signer::address_of(aptos_framework);
        ensures exists<Nonce>(addr);
        ensures exists<SmartTableWrapper<vector<u8>, BridgeTransferDetails<address, EthereumAddress>>>(addr);
        ensures exists<SmartTableWrapper<vector<u8>, BridgeTransferDetails<EthereumAddress, address>>>(addr);
    }

    spec schema TimeLockAbortsIf {
        time_lock: u64;
        aborts_if time_lock < MIN_TIME_LOCK;
        aborts_if !exists<CurrentTimeMicroseconds>(@aptos_framework);
        aborts_if time_lock > MAX_U64 - timestamp::spec_now_seconds();
    }

    spec create_time_lock {
        include TimeLockAbortsIf;
        ensures result == timestamp::spec_now_seconds() + time_lock;
        /// If the sum of `now()` and `lock` does not overflow, the result is the sum of `now()` and `lock`.
        ensures (timestamp::spec_now_seconds() + time_lock <= 0xFFFFFFFFFFFFFFFF) ==> result == timestamp::spec_now_seconds() + time_lock;
    }

    spec create_details<Initiator: store, Recipient: store>(initiator: Initiator, recipient: Recipient, amount: u64, hash_lock: vector<u8>, time_lock: u64)
    : BridgeTransferDetails<Initiator, Recipient> {
        include TimeLockAbortsIf;
        aborts_if amount == 0;
        aborts_if len(hash_lock) != 32;
        ensures result == BridgeTransferDetails<Initiator, Recipient> {
                addresses: AddressPair<Initiator, Recipient> {
                initiator,
                recipient
            },
            amount,
            hash_lock,
            time_lock: timestamp::spec_now_seconds() + time_lock,
            state: PENDING_TRANSACTION,
        };
    }

    spec schema AddAbortsIf<T> {
        bridge_transfer_id: vector<u8>;
        table: SmartTable<vector<u8>, T>;

        aborts_if len(bridge_transfer_id) != 32;
        aborts_if smart_table::spec_contains(table, bridge_transfer_id);
    }

    spec add<Initiator: store, Recipient: store>(bridge_transfer_id: vector<u8>, details: BridgeTransferDetails<Initiator, Recipient>) {
        let table = global<SmartTableWrapper<vector<u8>, BridgeTransferDetails<Initiator, Recipient>>>(@aptos_framework).inner;
        include AddAbortsIf<BridgeTransferDetails<Initiator, Recipient>>;

        aborts_if !exists<SmartTableWrapper<vector<u8>, BridgeTransferDetails<Initiator, Recipient>>>(@aptos_framework);
        aborts_if smart_table::spec_contains(table, bridge_transfer_id);

        ensures smart_table::spec_contains(global<SmartTableWrapper<vector<u8>, BridgeTransferDetails<Initiator, Recipient>>>(@aptos_framework).inner, bridge_transfer_id);

        ensures smart_table::spec_len(global<SmartTableWrapper<vector<u8>, BridgeTransferDetails<Initiator, Recipient>>>(@aptos_framework).inner) ==
            old(smart_table::spec_len(global<SmartTableWrapper<vector<u8>, BridgeTransferDetails<Initiator, Recipient>>>(@aptos_framework).inner)) + 1;
    }

    spec schema HashLockAbortsIf {
        hash_lock: vector<u8>;
        aborts_if len(hash_lock) != 32;
    }

    spec schema BridgetTransferDetailsAbortsIf<Initiator, Recipient> {
        hash_lock: vector<u8>;
        details: BridgeTransferDetails<Initiator, Recipient>;
        include HashLockAbortsIf;

        aborts_if timestamp::spec_now_seconds() > details.time_lock;
        aborts_if !exists<CurrentTimeMicroseconds>(@aptos_framework);
        aborts_if details.state != PENDING_TRANSACTION;
        aborts_if details.hash_lock != hash_lock;
    }

    spec complete_details<Initiator: store, Recipient: store + copy>(hash_lock: vector<u8>, details: &mut BridgeTransferDetails<Initiator, Recipient>) : (Recipient, u64) {
        include BridgetTransferDetailsAbortsIf<Initiator, Recipient>;
    }

    spec complete_transfer<Initiator: store, Recipient: copy + store>(bridge_transfer_id: vector<u8>, hash_lock: vector<u8>) : (Recipient, u64) {
        let table = global<SmartTableWrapper<vector<u8>, BridgeTransferDetails<Initiator, Recipient>>>(@aptos_framework).inner;
        aborts_if !exists<SmartTableWrapper<vector<u8>, BridgeTransferDetails<Initiator, Recipient>>>(@aptos_framework);
        aborts_if !smart_table::spec_contains(table, bridge_transfer_id);
        let details = smart_table::spec_get(table, bridge_transfer_id);
        include BridgetTransferDetailsAbortsIf<Initiator, Recipient>;
    }

    spec schema AbortBridgetTransferDetailsAbortsIf<Initiator, Recipient> {
        details: BridgeTransferDetails<Initiator, Recipient>;

        aborts_if details.state != PENDING_TRANSACTION;
        aborts_if !(timestamp::spec_now_seconds() > details.time_lock);
        aborts_if !exists<CurrentTimeMicroseconds>(@aptos_framework);
        ensures details.state == CANCELLED_TRANSACTION;
    }

    spec cancel_details<Initiator: store + copy, Recipient: store> (details: &mut BridgeTransferDetails<Initiator, Recipient>) : (Initiator, u64) {
        include AbortBridgetTransferDetailsAbortsIf<Initiator, Recipient>;
    }

    spec create_hashlock {
        aborts_if len(pre_image) == 0;
    }

    spec complete {
        requires details.state == PENDING_TRANSACTION;
        ensures details.state == COMPLETED_TRANSACTION;
    }

    spec cancel {
        requires details.state == PENDING_TRANSACTION;
        ensures details.state == CANCELLED_TRANSACTION;
    }
}

spec aptos_framework::atomic_bridge_configuration {
    spec initialize(aptos_framework: &signer) {
        aborts_if !system_addresses::is_aptos_framework_address(signer::address_of(aptos_framework));
        aborts_if exists<BridgeConfig>(signer::address_of(aptos_framework));

        ensures global<BridgeConfig>(signer::address_of(aptos_framework)).bridge_operator == signer::address_of(aptos_framework);
    }

    spec update_bridge_operator(aptos_framework: &signer, new_operator: address) {
        aborts_if !system_addresses::is_aptos_framework_address(signer::address_of(aptos_framework));
        aborts_if !exists<BridgeConfig>(signer::address_of(aptos_framework));
        aborts_if global<BridgeConfig>(signer::address_of(aptos_framework)).bridge_operator == new_operator;

        ensures global<BridgeConfig>(signer::address_of(aptos_framework)).bridge_operator == new_operator;
    }
}