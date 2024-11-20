module aptos_framework::native_bridge {

    use aptos_framework::account;
    use aptos_framework::native_bridge_core;
    use aptos_framework::native_bridge_configuration;
    use aptos_framework::native_bridge_configuration::assert_is_caller_relayer;
    use aptos_framework::native_bridge_store;
    use aptos_std::smart_table;
    use aptos_framework::ethereum;
    use aptos_framework::ethereum::EthereumAddress;
    use aptos_framework::event::{Self, EventHandle}; 
    use aptos_framework::signer;
    use aptos_framework::system_addresses;
    #[test_only]
    use aptos_framework::aptos_account;
    #[test_only]
    use aptos_framework::aptos_coin::AptosCoin;
    #[test_only]
    use aptos_framework::native_bridge_store::{valid_hash_lock, assert_valid_bridge_transfer_id, plain_secret};
    #[test_only]
    use aptos_framework::coin;
    #[test_only]
    use aptos_framework::ethereum::valid_eip55;
    #[test_only]
    use aptos_framework::timestamp;
    use std::bcs;
    use std::vector;
    use aptos_std::aptos_hash::keccak256;

    const ETRANSFER_ALREADY_PROCESSED: u64 = 1;
    const EINVALID_BRIDGE_TRANSFER_ID: u64 = 2;
    const EEVENT_NOT_FOUND : u64 = 3;

    #[event]
    /// An event triggered upon initiating a bridge transfer
    struct BridgeTransferInitiatedEvent has store, drop {
        bridge_transfer_id: vector<u8>,
        initiator: address,
        recipient: vector<u8>,
        amount: u64,
        nonce: u64,
    }

    #[event]
    /// An event triggered upon completing a bridge transfer
    struct BridgeTransferCompletedEvent has store, drop {
        bridge_transfer_id: vector<u8>,
        initiator: vector<u8>,
        recipient: address,
        amount: u64,
        nonce: u64,
    }

    /// This struct will store the event handles for bridge events.
    struct BridgeEvents has key, store {
        bridge_transfer_initiated_events: EventHandle<BridgeTransferInitiatedEvent>,
        bridge_transfer_completed_events: EventHandle<BridgeTransferCompletedEvent>,
    }

    struct Nonce has key {
        value: u64
    }

    /// Increment and get the current nonce  
    fun increment_and_get_nonce(): u64 acquires Nonce {  
        let nonce_ref = borrow_global_mut<Nonce>(@aptos_framework);  
        nonce_ref.value = nonce_ref.value + 1;  
        nonce_ref.value  
    }  

    /// Initializes the module and stores the `EventHandle`s in the resource.
    public fun initialize(aptos_framework: &signer) {
        system_addresses::assert_aptos_framework(aptos_framework);

        // Ensure the nonce is not already initialized
        assert!(
            !exists<Nonce>(signer::address_of(aptos_framework)),
            2
        );

        // Create the Nonce resource with an initial value of 1
        move_to<Nonce>(aptos_framework, Nonce { value: 0 });

        move_to(aptos_framework, BridgeEvents {
            bridge_transfer_initiated_events: account::new_event_handle<BridgeTransferInitiatedEvent>(aptos_framework),
            bridge_transfer_completed_events: account::new_event_handle<BridgeTransferCompletedEvent>(aptos_framework),
        });
    }

    /// Initiate a bridge transfer of MOVE from Movement to the base layer  
    /// Anyone can initiate a bridge transfer from the source chain  
    /// The amount is burnt from the initiator and the module-level nonce is incremented  
    /// @param initiator The initiator's Ethereum address as a vector of bytes.  
    /// @param recipient The address of the recipient on the Aptos blockchain.  
    /// @param amount The amount of assets to be locked.  
    public entry fun initiate_bridge_transfer(  
        initiator: &signer,  
        recipient: vector<u8>,  
        amount: u64  
    ) acquires BridgeEvents, Nonce {  
        let initiator_address = signer::address_of(initiator);  
        let ethereum_address = ethereum::ethereum_address_no_eip55(recipient);  
    
        // Increment and retrieve the nonce  
        let nonce = increment_and_get_nonce();  
    
        // Create bridge transfer details  
        let details = native_bridge_store::create_details(  
            initiator_address,  
            ethereum_address, 
            amount,  
            nonce  
        );  
    
        // Generate a unique bridge transfer ID  
        // Todo: pass the nonce in here and modify the function to take a nonce. Or only use the nonce in native_bridge_store
        let bridge_transfer_id = native_bridge_store::bridge_transfer_id(&details);  
    
        // Add the transfer details to storage  
        native_bridge_store::add(bridge_transfer_id, details);
    
        // Push details to be able to lookup by nonce
        native_bridge_store::set_nonce_to_bridge_transfer_id(nonce, bridge_transfer_id);

        // Burn the amount from the initiator  
        native_bridge_core::burn(initiator_address, amount);  
    
        let bridge_events = borrow_global_mut<BridgeEvents>(@aptos_framework);

        // Emit an event with nonce  
        event::emit_event(  
             &mut bridge_events.bridge_transfer_initiated_events,
            BridgeTransferInitiatedEvent {  
                bridge_transfer_id,  
                initiator: initiator_address,  
                recipient,  
                amount,  
                nonce,  
            }  
        );  
    }

    /// Completes a bridge transfer by the initiator.
    ///  
    /// @param caller The signer representing the bridge relayer.  
    /// @param initiator The initiator's Ethereum address as a vector of bytes.  
    /// @param bridge_transfer_id The unique identifier for the bridge transfer.  
    /// @param recipient The address of the recipient on the Aptos blockchain.  
    /// @param amount The amount of assets to be locked.  
    /// @param nonce The unique nonce for the transfer.    
    /// @abort If the caller is not the bridge relayer or the transfer has already been processed.  
    public entry fun complete_bridge_transfer(  
        caller: &signer,  
        bridge_transfer_id: vector<u8>,
        initiator: vector<u8>,  
        recipient: address,  
        amount: u64,  
        nonce: u64  
    ) acquires BridgeEvents {  
        // Ensure the caller is the bridge relayer
        native_bridge_configuration::assert_is_caller_relayer(caller);  

        // Check if the bridge transfer ID is already associated with an incoming nonce
        let incoming_nonce_exists = native_bridge_store::is_incoming_nonce_set(bridge_transfer_id);
        assert!(!incoming_nonce_exists, ETRANSFER_ALREADY_PROCESSED); // Abort if the transfer is already processed

        let ethereum_address = ethereum::ethereum_address_no_eip55(initiator);

        // Validate the bridge_transfer_id by reconstructing the hash
        let combined_bytes = vector::empty<u8>();
        vector::append(&mut combined_bytes, bcs::to_bytes(&initiator));
        vector::append(&mut combined_bytes, bcs::to_bytes(&recipient));
        vector::append(&mut combined_bytes, bcs::to_bytes(&amount));
        vector::append(&mut combined_bytes, bcs::to_bytes(&nonce));
        assert!(keccak256(combined_bytes) == bridge_transfer_id, EINVALID_BRIDGE_TRANSFER_ID);

        // Mint to the recipient
        native_bridge_core::mint(recipient, amount);

        // Record the transfer as completed by associating the bridge_transfer_id with the incoming nonce
        native_bridge_store::set_bridge_transfer_id_to_incoming_nonce(bridge_transfer_id, nonce);

        // Emit the event
        let bridge_events = borrow_global_mut<BridgeEvents>(@aptos_framework);
        event::emit_event(  
            &mut bridge_events.bridge_transfer_completed_events,
            BridgeTransferCompletedEvent {  
                bridge_transfer_id,  
                initiator,  
                recipient,  
                amount,  
                nonce,  
            },  
        );  
    } 

    #[test(aptos_framework = @aptos_framework, sender = @0xdaff)]
    fun test_initiate_bridge_transfer_happy_path(
        sender: &signer,
        aptos_framework: &signer,
    ) acquires BridgeEvents, Nonce {
        let sender_address = signer::address_of(sender);
        native_bridge_core::initialize_for_test(aptos_framework);
        initialize(aptos_framework);
        aptos_account::create_account(sender_address);
        let amount = 1000;

        // Mint coins to the sender to ensure they have sufficient balance
        let account_balance = amount + 1;
        // Mint some coins
        native_bridge_core::mint(sender_address, account_balance);

        // Specify the recipient and transfer amount
        let recipient = valid_eip55();

        // Perform the bridge transfer
        initiate_bridge_transfer(
            sender,
            recipient,
            amount
        );

        let bridge_events = borrow_global<BridgeEvents>(@aptos_framework);
        let initiated_events = event::emitted_events_by_handle(
            &bridge_events.bridge_transfer_initiated_events
        );
        assert!(vector::length(&initiated_events) == 1, EEVENT_NOT_FOUND);
    }

    #[test(aptos_framework = @aptos_framework, sender = @0xdaff)]
    #[expected_failure(abort_code = 0x10006, location = 0x1::coin)] //EINSUFFICIENT_BALANCE
    fun test_initiate_bridge_transfer_insufficient_balance(
        sender: &signer,
        aptos_framework: &signer,
    ) acquires BridgeEvents, Nonce {
        let sender_address = signer::address_of(sender);
        native_bridge_core::initialize_for_test(aptos_framework);
        initialize(aptos_framework);
        aptos_account::create_account(sender_address);

        let recipient = valid_eip55();
        let amount = 1000;

        initiate_bridge_transfer(
            sender,
            recipient,
            amount
        );
    }

    #[test(aptos_framework = @aptos_framework)]
    fun test_complete_bridge_transfer(aptos_framework: &signer) acquires BridgeEvents {
        native_bridge_core::initialize_for_test(aptos_framework);
        initialize(aptos_framework);
        let initiator = valid_eip55();
        let recipient = @0xcafe;
        let amount = 1;
        let nonce = 5;

        // Create a bridge transfer ID algorithmically
        let combined_bytes = vector::empty<u8>();
        vector::append(&mut combined_bytes, bcs::to_bytes(&initiator));
        vector::append(&mut combined_bytes, bcs::to_bytes(&recipient));
        vector::append(&mut combined_bytes, bcs::to_bytes(&amount));
        vector::append(&mut combined_bytes, bcs::to_bytes(&nonce));
        let bridge_transfer_id = keccak256(combined_bytes);

        // Create an account for our recipient
        aptos_account::create_account(recipient);

        complete_bridge_transfer(
            aptos_framework,
            bridge_transfer_id,
            initiator,
            recipient,
            amount,
            nonce
        );

        let bridge_events = borrow_global<BridgeEvents>(signer::address_of(aptos_framework));
        let complete_events = event::emitted_events_by_handle(&bridge_events.bridge_transfer_completed_events);

        // Assert that the event was emitted
        let expected_event = BridgeTransferCompletedEvent {
            bridge_transfer_id,
            initiator,
            recipient,
            amount,
            nonce,
        };

        assert!(std::vector::contains(&complete_events, &expected_event), 0);
    }

    #[test(aptos_framework = @aptos_framework, sender = @0xdaff)]
    // #[expected_failure(abort_code = 0x1, location = 0x1::native_bridge_configuration)] // EINVALID_BRIDGE_relayer
    fun test_complete_bridge_transfer_by_sender(
        sender: &signer,
        aptos_framework: &signer
    ) acquires BridgeEvents, Nonce {
        let sender_address = signer::address_of(sender);
        // Create an account for our recipient
        native_bridge_core::initialize_for_test(aptos_framework);
        initialize(aptos_framework);
        aptos_account::create_account(sender_address);

        let recipient = valid_eip55();
        let amount = 1000;
        let account_balance = amount + 1;

        // Mint some coins
        native_bridge_core::mint(sender_address, account_balance);

        assert!(coin::balance<AptosCoin>(sender_address) == account_balance, 0);

        initiate_bridge_transfer(
            sender,
            recipient,
            amount
        );

        let bridge_events = borrow_global<BridgeEvents>(@aptos_framework);
        let bridge_transfer_initiated_events = event::emitted_events_by_handle(
            &bridge_events.bridge_transfer_initiated_events
        );   
        let bridge_transfer_initiated_event = vector::borrow(&bridge_transfer_initiated_events, 0);

        let bridge_transfer_id = bridge_transfer_initiated_event.bridge_transfer_id;
        
    }

    #[test(aptos_framework = @aptos_framework, sender = @0xdaff)]
    #[expected_failure(abort_code = EINVALID_BRIDGE_TRANSFER_ID, location = Self)] // ENOT_FOUND
    fun test_complete_bridge_with_erroneous_bridge_id_by_relayer(
        sender: &signer,
        aptos_framework: &signer
    ) acquires BridgeEvents {
        let sender_address = signer::address_of(sender);
        // Create an account for our recipient
        native_bridge_core::initialize_for_test(aptos_framework);
        aptos_account::create_account(sender_address);

        let bridge_transfer_id = b"guessing the id";

        // As relayer I send a complete request and it should fail
        complete_bridge_transfer(
            aptos_framework,
            bridge_transfer_id,
            valid_eip55(),
            sender_address,
            1000,
            1
        );
    }
}

module aptos_framework::native_bridge_store {
    use std::bcs;
    use std::features;
    use std::vector;
    use aptos_std::aptos_hash::keccak256;
    use aptos_std::smart_table;
    use aptos_std::smart_table::SmartTable;
    use aptos_framework::ethereum::EthereumAddress;
    use aptos_framework::system_addresses;
    use aptos_framework::timestamp;
    use std::signer;
    use aptos_framework::timestamp::CurrentTimeMicroseconds;

    friend aptos_framework::native_bridge;

    #[test_only]
    use std::hash::sha3_256;
    #[test_only]
    use aptos_framework::ethereum;
    #[test_only]
    use aptos_framework::native_bridge_configuration;

    /// Error codes
    const EINVALID_PRE_IMAGE : u64 = 0x1;
    const ENONCE_NOT_FOUND : u64 = 0x2;
    const EZERO_AMOUNT : u64 = 0x3;
    const EINVALID_BRIDGE_TRANSFER_ID : u64 = 0x4;
    const ENATIVE_BRIDGE_NOT_ENABLED : u64 = 0x5;
    const EINCORRECT_NONCE : u64 = 0x6;
    const EID_NOT_FOUND : u64 = 0x7;

    const MAX_U64 : u64 = 0xFFFFFFFFFFFFFFFF;

    struct AddressPair<Initiator: store, Recipient: store> has store, copy {
        initiator: Initiator,
        recipient: Recipient,
    }

    /// A smart table wrapper
    struct SmartTableWrapper<K, V> has key, store {
        inner: SmartTable<K, V>,
    }

    /// Details on the outbound transfer
    struct OutboundTransfer<Initiator: store, Recipient: store> has store, copy {
        addresses: AddressPair<Initiator, Recipient>,
        amount: u64,
        nonce: u64
    }

    /// Details on the inbound transfer
    struct InboundBridgeTransfer<Initiator: store, Recipient: store> has store, copy {
        addresses: AddressPair<Initiator, Recipient>,
        amount: u64,
        nonce: u64
    }

    /// Checks if a bridge transfer ID is associated with an incoming nonce.
    /// @param bridge_transfer_id The bridge transfer ID.
    /// @return `true` if the ID is associated with an incoming nonce, `false` otherwise.
    public(friend) fun is_incoming_nonce_set(bridge_transfer_id: vector<u8>): bool acquires SmartTableWrapper {
        let table = borrow_global<SmartTableWrapper<vector<u8>, u64>>(@aptos_framework);
        smart_table::contains(&table.inner, bridge_transfer_id)
    }

    /// Initializes the initiators tables and nonce.
    ///
    /// @param aptos_framework The signer for Aptos framework.
    public fun initialize(aptos_framework: &signer) {
        system_addresses::assert_aptos_framework(aptos_framework);

        let initiators = SmartTableWrapper<vector<u8>, OutboundTransfer<address, EthereumAddress>> {
            inner: smart_table::new(),
        };

        move_to(aptos_framework, initiators);    

        let nonces_to_bridge_transfer_ids = SmartTableWrapper<u64, vector<u8>> {
            inner: smart_table::new(),
        };

        move_to(aptos_framework, nonces_to_bridge_transfer_ids);

        let ids_to_incoming_nonces = SmartTableWrapper<vector<u8>, u64> {
            inner: smart_table::new(),
        };

        move_to(aptos_framework, ids_to_incoming_nonces);
    }

    /// Returns the current time in seconds.
    ///
    /// @return Current timestamp in seconds.
    fun now() : u64 {
        timestamp::now_seconds()
    }

    /// Creates bridge transfer details with validation.
    ///
    /// @param initiator The initiating party of the transfer.
    /// @param recipient The receiving party of the transfer.
    /// @param amount The amount to be transferred.
    /// @param nonce The unique nonce for the transfer.
    /// @return A `BridgeTransferDetails` object.
    /// @abort If the amount is zero or locks are invalid.
    public(friend) fun create_details<Initiator: store, Recipient: store>(initiator: Initiator, recipient: Recipient, amount: u64, nonce: u64)
        : OutboundTransfer<Initiator, Recipient> {
        assert!(amount > 0, EZERO_AMOUNT);

        OutboundTransfer {
            addresses: AddressPair {
                initiator,
                recipient
            },
            amount,
            nonce,
        }
    }

    /// Record details of an initiated transfer for quick lookup of details, mapping bridge transfer ID to transfer details 
    ///
    /// @param bridge_transfer_id Bridge transfer ID.
    /// @param details The bridge transfer details
    public(friend) fun add<Initiator: store, Recipient: store>(bridge_transfer_id: vector<u8>, details: OutboundTransfer<Initiator, Recipient>) acquires SmartTableWrapper {
        assert!(features::abort_native_bridge_enabled(), ENATIVE_BRIDGE_NOT_ENABLED);

        assert_valid_bridge_transfer_id(&bridge_transfer_id);
        let table = borrow_global_mut<SmartTableWrapper<vector<u8>, OutboundTransfer<Initiator, Recipient>>>(@aptos_framework);
        smart_table::add(&mut table.inner, bridge_transfer_id, details);
    }

    /// Record details of an initiated transfer, mapping nonce to bridge transfer ID
    ///
    /// @param bridge_transfer_id Bridge transfer ID.
    /// @param details The bridge transfer details
    public(friend) fun set_nonce_to_bridge_transfer_id(nonce: u64, bridge_transfer_id: vector<u8>) acquires SmartTableWrapper {
        assert!(features::abort_native_bridge_enabled(), ENATIVE_BRIDGE_NOT_ENABLED);

        assert_valid_bridge_transfer_id(&bridge_transfer_id);
        let table = borrow_global_mut<SmartTableWrapper<u64, vector<u8>>>(@aptos_framework);
        smart_table::add(&mut table.inner, nonce, bridge_transfer_id);
    }

    /// Record details of a completed transfer, mapping bridge transfer ID to incoming nonce
    ///
    /// @param bridge_transfer_id Bridge transfer ID.
    /// @param details The bridge transfer details
    public(friend) fun set_bridge_transfer_id_to_incoming_nonce(bridge_transfer_id: vector<u8>, incoming_nonce: u64) acquires SmartTableWrapper {
        assert!(features::abort_native_bridge_enabled(), ENATIVE_BRIDGE_NOT_ENABLED);

        assert_valid_bridge_transfer_id(&bridge_transfer_id);
        let table = borrow_global_mut<SmartTableWrapper<vector<u8>, u64>>(@aptos_framework);
        smart_table::add(&mut table.inner, bridge_transfer_id, incoming_nonce);
    }

    /// Asserts that the bridge transfer ID is valid.
    ///
    /// @param bridge_transfer_id The bridge transfer ID to validate.
    /// @abort If the ID is invalid.
    public(friend) fun assert_valid_bridge_transfer_id(bridge_transfer_id: &vector<u8>) {
        assert!(vector::length(bridge_transfer_id) == 32, EINVALID_BRIDGE_TRANSFER_ID);
    }

    /// Generates a unique bridge transfer ID based on transfer details and nonce.
    ///
    /// @param details The bridge transfer details.
    /// @return The generated bridge transfer ID.
    public(friend) fun bridge_transfer_id<Initiator: store, Recipient: store>(details: &OutboundTransfer<Initiator, Recipient>) : vector<u8> {
        let combined_bytes = vector::empty<u8>();
        vector::append(&mut combined_bytes, bcs::to_bytes(&details.addresses.initiator));
        vector::append(&mut combined_bytes, bcs::to_bytes(&details.addresses.recipient));
        vector::append(&mut combined_bytes, bcs::to_bytes(&details.amount));
        vector::append(&mut combined_bytes, bcs::to_bytes(&details.nonce));
        keccak256(combined_bytes)
    }

    #[view]
    /// Gets initiator bridge transfer details given a bridge transfer ID
    ///
    /// @param bridge_transfer_id A 32-byte vector of unsigned 8-bit integers.
    /// @return A `OutboundTransfer` struct.
    /// @abort If there is no transfer in the atomic bridge store.
    public fun get_bridge_transfer_details(
        bridge_transfer_id: vector<u8>
    ): OutboundTransfer<address, EthereumAddress> acquires SmartTableWrapper {
        get_bridge_transfer_details_inner(bridge_transfer_id)
    }

    fun get_bridge_transfer_details_inner<Initiator: store + copy, Recipient: store + copy>(bridge_transfer_id: vector<u8>
    ): OutboundTransfer<Initiator, Recipient> acquires SmartTableWrapper {
        let table = borrow_global<SmartTableWrapper<vector<u8>, OutboundTransfer<Initiator, Recipient>>>(@aptos_framework);

        let details_ref = smart_table::borrow(
            &table.inner,
            bridge_transfer_id
        );

        *details_ref
    }
    
    #[view]
    /// Gets `bridge_transfer_id` from `nonce`.
    /// @param nonce The nonce of the bridge transfer.
    /// @return The bridge transfer ID.
    /// @abort If the nonce is not found in the smart table.
    public fun get_bridge_transfer_id_from_nonce(nonce: u64): vector<u8> acquires SmartTableWrapper {
        let table = borrow_global<SmartTableWrapper<u64, vector<u8>>>(@aptos_framework);
        
        // Check if the nonce exists in the table
        assert!(smart_table::contains(&table.inner, nonce), ENONCE_NOT_FOUND);

        // If it exists, return the associated bridge_transfer_id
        *smart_table::borrow(&table.inner, nonce)
    }

    #[view]
    /// Gets incoming `nonce` from `bridge_transfer_id`
    /// @param bridge_transfer_id The ID bridge transfer.
    /// @return the nonce
    /// @abort If the nonce is not found in the smart table.
    public fun get_incoming_nonce_from_bridge_transfer_id(bridge_transfer_id: vector<u8>): u64 acquires SmartTableWrapper {
        let table = borrow_global<SmartTableWrapper<vector<u8>, u64>>(@aptos_framework);

         // Check if the nonce exists in the table
        assert!(smart_table::contains(&table.inner, bridge_transfer_id), ENONCE_NOT_FOUND);

        // If it exists, return the associated nonce
        *smart_table::borrow(&table.inner, bridge_transfer_id)
    }

    #[test_only]
    public fun valid_bridge_transfer_id() : vector<u8> {
        sha3_256(b"atomic bridge")
    }

    #[test_only]
    public fun plain_secret() : vector<u8> {
        b"too secret!"
    }

    #[test_only]
    public fun valid_hash_lock() : vector<u8> {
        keccak256(plain_secret())
    }


    #[test(aptos_framework = @aptos_framework)]
    public fun test_get_bridge_transfer_details_initiator(aptos_framework: &signer) acquires SmartTableWrapper {
        timestamp::set_time_has_started_for_testing(aptos_framework);
        features::change_feature_flags_for_testing(
            aptos_framework,
            vector[features::get_native_bridge_feature()],
            vector[]
        );
        native_bridge_configuration::initialize(aptos_framework);
        initialize(aptos_framework);

        let initiator = signer::address_of(aptos_framework);
        let recipient = ethereum::ethereum_address(ethereum::valid_eip55());
        let amount = 1000;
        let nonce = 5;
        let bridge_transfer_id = valid_bridge_transfer_id();

        let details = create_details(
            initiator, 
            recipient, 
            amount, 
            nonce
        );

        add(bridge_transfer_id, details);

        let retrieved_details = get_bridge_transfer_details(bridge_transfer_id);

        let OutboundTransfer {
            addresses: AddressPair {
                initiator: retrieved_initiator,
                recipient: retrieved_recipient
            },
            amount: retrieved_amount,
            nonce: retrieved_nonce
        } = retrieved_details;

        assert!(retrieved_initiator == initiator, 0);
        assert!(retrieved_recipient == recipient, 1);
        assert!(retrieved_amount == amount, 2);
        assert!(retrieved_nonce == nonce, 3);
    }

    #[test(aptos_framework = @aptos_framework)]
    public fun test_get_bridge_transfer_details_counterparty(aptos_framework: &signer) acquires SmartTableWrapper {
        timestamp::set_time_has_started_for_testing(aptos_framework);
        features::change_feature_flags_for_testing(
            aptos_framework,
            vector[features::get_native_bridge_feature()],
            vector[]
        );
        initialize(aptos_framework);

        let initiator = signer::address_of(aptos_framework);
        let recipient = ethereum::ethereum_address(ethereum::valid_eip55());
        let amount = 500;
        let nonce = 5;

        // Create a bridge transfer ID algorithmically
        let combined_bytes = vector::empty<u8>();
        vector::append(&mut combined_bytes, bcs::to_bytes(&initiator));
        vector::append(&mut combined_bytes, bcs::to_bytes(&recipient));
        vector::append(&mut combined_bytes, bcs::to_bytes(&amount));
        vector::append(&mut combined_bytes, bcs::to_bytes(&nonce));
        let bridge_transfer_id = keccak256(combined_bytes);

        let details = create_details(
            initiator, 
            recipient, 
            amount, 
            nonce
        );

        add(bridge_transfer_id, details);

        let retrieved_details = get_bridge_transfer_details(bridge_transfer_id);

        let OutboundTransfer {
            addresses: AddressPair {
                initiator: retrieved_initiator,
                recipient: retrieved_recipient
            },
            amount: retrieved_amount,
            nonce: retrieved_nonce
        } = retrieved_details;

        assert!(retrieved_initiator == initiator, 0);
        assert!(retrieved_recipient == recipient, 1);
        assert!(retrieved_amount == amount, 2);
        assert!(retrieved_nonce == 5, EINCORRECT_NONCE);
    }
}

module aptos_framework::native_bridge_configuration {
    use std::signer;
    use aptos_framework::event;
    use aptos_framework::system_addresses;

    friend aptos_framework::native_bridge;

    /// Error code for invalid bridge relayer
    const EINVALID_BRIDGE_RELAYER: u64 = 0x1;

    /// Counterparty time lock duration is 24 hours in seconds
    const COUNTERPARTY_TIME_LOCK_DUARTION: u64 = 24 * 60 * 60;
    /// Initiator time lock duration is 48 hours in seconds
    const INITIATOR_TIME_LOCK_DUARTION: u64 = 48 * 60 * 60;

    struct BridgeConfig has key {
        bridge_relayer: address,
        initiator_time_lock: u64,
        counterparty_time_lock: u64,
    }

    #[event]
    /// Event emitted when the bridge relayer is updated.
    struct BridgeConfigRelayerUpdated has store, drop {
        old_relayer: address,
        new_relayer: address,
    }

    #[event]
    /// Event emitted when the initiator time lock has been updated.
    struct InitiatorTimeLockUpdated has store, drop {
        time_lock: u64,
    }

    #[event]
    /// Event emitted when the initiator time lock has been updated.
    struct CounterpartyTimeLockUpdated has store, drop {
        time_lock: u64,
    }

    /// Initializes the bridge configuration with Aptos framework as the bridge relayer.
    ///
    /// @param aptos_framework The signer representing the Aptos framework.
    public fun initialize(aptos_framework: &signer) {
        system_addresses::assert_aptos_framework(aptos_framework);
        let bridge_config = BridgeConfig {
            bridge_relayer: signer::address_of(aptos_framework),
            initiator_time_lock: INITIATOR_TIME_LOCK_DUARTION,
            counterparty_time_lock: COUNTERPARTY_TIME_LOCK_DUARTION,
        };
        move_to(aptos_framework, bridge_config);
    }

    /// Updates the bridge relayer, requiring governance validation.
    ///
    /// @param aptos_framework The signer representing the Aptos framework.
    /// @param new_relayer The new address to be set as the bridge relayer.
    /// @abort If the current relayer is the same as the new relayer.
    public fun update_bridge_relayer(aptos_framework: &signer, new_relayer: address
    )   acquires BridgeConfig {
        system_addresses::assert_aptos_framework(aptos_framework);
        let bridge_config = borrow_global_mut<BridgeConfig>(@aptos_framework);
        let old_relayer = bridge_config.bridge_relayer;
        assert!(old_relayer != new_relayer, EINVALID_BRIDGE_RELAYER);

        bridge_config.bridge_relayer = new_relayer;

        event::emit(
            BridgeConfigRelayerUpdated {
                old_relayer,
                new_relayer,
            },
        );
    }

    #[view]
    /// Retrieves the address of the current bridge relayer.
    ///
    /// @return The address of the current bridge relayer.
    public fun bridge_relayer(): address acquires BridgeConfig {
        borrow_global_mut<BridgeConfig>(@aptos_framework).bridge_relayer
    }

    /// Asserts that the caller is the current bridge relayer.
    ///
    /// @param caller The signer whose authority is being checked.
    /// @abort If the caller is not the current bridge relayer.
    public(friend) fun assert_is_caller_relayer(caller: &signer
    ) acquires BridgeConfig {
        assert!(borrow_global<BridgeConfig>(@aptos_framework).bridge_relayer == signer::address_of(caller), EINVALID_BRIDGE_RELAYER);
    }

    #[test(aptos_framework = @aptos_framework)]
    /// Tests initialization of the bridge configuration.
    fun test_initialization(aptos_framework: &signer) {
        initialize(aptos_framework);
        assert!(exists<BridgeConfig>(@aptos_framework), 0);
    }

    #[test(aptos_framework = @aptos_framework, new_relayer = @0xcafe)]
    /// Tests updating the bridge relayer and emitting the corresponding event.
    fun test_update_bridge_relayer(aptos_framework: &signer, new_relayer: address
    ) acquires BridgeConfig {
        initialize(aptos_framework);
        update_bridge_relayer(aptos_framework, new_relayer);

        assert!(
            event::was_event_emitted<BridgeConfigRelayerUpdated>(
                &BridgeConfigRelayerUpdated {
                    old_relayer: @aptos_framework,
                    new_relayer,
                }
            ), 0);

        assert!(bridge_relayer() == new_relayer, 0);
    }

    #[test(aptos_framework = @aptos_framework, bad = @0xbad, new_relayer = @0xcafe)]
    #[expected_failure(abort_code = 0x50003, location = 0x1::system_addresses)]
    /// Tests that updating the bridge relayer with an invalid signer fails.
    fun test_failing_update_bridge_relayer(aptos_framework: &signer, bad: &signer, new_relayer: address
    ) acquires BridgeConfig {
        initialize(aptos_framework);
        update_bridge_relayer(bad, new_relayer);
    }

    #[test(aptos_framework = @aptos_framework)]
    /// Tests that the correct relayer is validated successfully.
    fun test_is_valid_relayer(aptos_framework: &signer) acquires BridgeConfig {
        initialize(aptos_framework);
        assert_is_caller_relayer(aptos_framework);
    }

    #[test(aptos_framework = @aptos_framework, bad = @0xbad)]
    #[expected_failure(abort_code = 0x1, location = 0x1::native_bridge_configuration)]
    /// Tests that an incorrect relayer is not validated and results in an abort.
    fun test_is_not_valid_relayer(aptos_framework: &signer, bad: &signer) acquires BridgeConfig {
        initialize(aptos_framework);
        assert_is_caller_relayer(bad);
    }

}

module aptos_framework::native_bridge_core {
    use std::features;
    use aptos_framework::aptos_coin::AptosCoin;
    use aptos_framework::native_bridge_configuration;
    use aptos_framework::native_bridge_store;
    use aptos_framework::coin;
    use aptos_framework::coin::{BurnCapability, MintCapability};
    use aptos_framework::fungible_asset::{BurnRef, MintRef};
    use aptos_framework::system_addresses;
    #[test_only]
    use aptos_framework::account;
    #[test_only]
    use aptos_framework::aptos_coin;
    #[test_only]
    use aptos_framework::timestamp;

    friend aptos_framework::native_bridge;
    friend aptos_framework::genesis;

    const ENATIVE_BRIDGE_NOT_ENABLED : u64 = 0x1;

    struct AptosCoinBurnCapability has key {
        burn_cap: BurnCapability<AptosCoin>,
    }

    struct AptosCoinMintCapability has key {
        mint_cap: MintCapability<AptosCoin>,
    }

    struct AptosFABurnCapabilities has key {
        burn_ref: BurnRef,
    }

    struct AptosFAMintCapabilities has key {
        burn_ref: MintRef,
    }

    /// Initializes the atomic bridge by setting up necessary configurations.
    ///
    /// @param aptos_framework The signer representing the Aptos framework.
    public fun initialize(aptos_framework: &signer) {
        native_bridge_configuration::initialize(aptos_framework);
        native_bridge_store::initialize(aptos_framework);
    }

    #[test_only]
    /// Initializes the atomic bridge for testing purposes, including setting up accounts and timestamps.
    ///
    /// @param aptos_framework The signer representing the Aptos framework.
    public fun initialize_for_test(aptos_framework: &signer) {
        timestamp::set_time_has_started_for_testing(aptos_framework);
        account::create_account_for_test(@aptos_framework);
        features::change_feature_flags_for_testing(
            aptos_framework,
            vector[features::get_native_bridge_feature()],
            vector[]
        );
        initialize(aptos_framework);

        let (burn_cap, mint_cap) = aptos_coin::initialize_for_test(aptos_framework);

        store_aptos_coin_mint_cap(aptos_framework, mint_cap);
        store_aptos_coin_burn_cap(aptos_framework, burn_cap);
    }

    /// Stores the burn capability for AptosCoin, converting to a fungible asset reference if the feature is enabled.
    ///
    /// @param aptos_framework The signer representing the Aptos framework.
    /// @param burn_cap The burn capability for AptosCoin.
    public fun store_aptos_coin_burn_cap(aptos_framework: &signer, burn_cap: BurnCapability<AptosCoin>) {
        system_addresses::assert_aptos_framework(aptos_framework);
        if (features::operations_default_to_fa_apt_store_enabled()) {
            let burn_ref = coin::convert_and_take_paired_burn_ref(burn_cap);
            move_to(aptos_framework, AptosFABurnCapabilities { burn_ref });
        } else {
            move_to(aptos_framework, AptosCoinBurnCapability { burn_cap })
        }
    }

    /// Stores the mint capability for AptosCoin.
    ///
    /// @param aptos_framework The signer representing the Aptos framework.
    /// @param mint_cap The mint capability for AptosCoin.
    public fun store_aptos_coin_mint_cap(aptos_framework: &signer, mint_cap: MintCapability<AptosCoin>) {
        system_addresses::assert_aptos_framework(aptos_framework);
        move_to(aptos_framework, AptosCoinMintCapability { mint_cap })
    }

    /// Mints a specified amount of AptosCoin to a recipient's address.
    ///
    /// @param recipient The address of the recipient to mint coins to.
    /// @param amount The amount of AptosCoin to mint.
    /// @abort If the mint capability is not available.
    public(friend) fun mint(recipient: address, amount: u64) acquires AptosCoinMintCapability {
        assert!(features::abort_native_bridge_enabled(), ENATIVE_BRIDGE_NOT_ENABLED);

        coin::deposit(recipient, coin::mint(
            amount,
            &borrow_global<AptosCoinMintCapability>(@aptos_framework).mint_cap
        ));
    }

    /// Burns a specified amount of AptosCoin from an address.
    ///
    /// @param from The address from which to burn AptosCoin.
    /// @param amount The amount of AptosCoin to burn.
    /// @abort If the burn capability is not available.
    public(friend) fun burn(from: address, amount: u64) acquires AptosCoinBurnCapability {
        assert!(features::abort_native_bridge_enabled(), ENATIVE_BRIDGE_NOT_ENABLED);

        coin::burn_from(
            from,
            amount,
            &borrow_global<AptosCoinBurnCapability>(@aptos_framework).burn_cap,
        );
    }
}