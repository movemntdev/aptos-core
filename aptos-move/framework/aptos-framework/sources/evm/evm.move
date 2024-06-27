module aptos_framework::evm {
    #[test_only]
    use aptos_framework::account;
    // use std::vector;
    use aptos_framework::account::{create_resource_address, exists_at, new_event_handle};
    use std::vector;
    use aptos_framework::coin;
    use aptos_framework::aptos_coin::AptosCoin;
    use aptos_std::aptos_hash::keccak256;
    use aptos_framework::create_signer::create_signer;
    #[test_only]
    use std::string;
    use aptos_framework::aptos_account::create_account;
    use aptos_std::debug;
    use std::signer::address_of;
    use aptos_framework::evm_util::{slice, to_32bit, get_contract_address, to_int256, data_to_u256, u256_to_data, mstore, to_u256};
    use aptos_framework::timestamp::now_microseconds;
    use aptos_framework::block;
    use std::string::utf8;
    use aptos_framework::event::EventHandle;
    use aptos_framework::event;
    use aptos_std::table;
    use aptos_std::table::Table;
    use aptos_std::from_bcs::{to_address};
    use aptos_std::secp256k1::{ecdsa_signature_from_bytes, ecdsa_recover, ecdsa_raw_public_key_to_bytes};
    use std::option::borrow;
    use aptos_framework::precompile::{is_precompile_address, run_precompile};
    // #[test_only]
    // use std::features;
    use aptos_std::simple_map;
    use aptos_std::simple_map::SimpleMap;
    use aptos_framework::evm_arithmetic::add_sign;
    #[test_only]
    use aptos_framework::timestamp;
    // #[test_only]
    // use aptos_framework::evm_arithmetic::{sdiv, add, smod};

    const ADDR_LENGTH: u64 = 10001;
    const SIGNATURE: u64 = 10002;
    const INSUFFIENT_BALANCE: u64 = 10003;
    const NONCE: u64 = 10004;
    const CONTRACT_READ_ONLY: u64 = 10005;
    const CONTRACT_DEPLOYED: u64 = 10006;
    const TX_NOT_SUPPORT: u64 = 10007;
    const ACCOUNT_NOT_EXIST: u64 = 10008;
    /// invalid chain id in raw tx
    const INVALID_CHAINID: u64 = 10009;
    const CONVERT_BASE: u256 = 10000000000;
    const CHAIN_ID: u64 = 0x150;

    const U256_MAX: u256 = 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    const ZERO_ADDR: vector<u8> =      x"0000000000000000000000000000000000000000000000000000000000000000";
    const ONE_ADDR: vector<u8> =       x"0000000000000000000000000000000000000000000000000000000000000001";
    const CHAIN_ID_BYTES: vector<u8> = x"0150";

    // struct Acc

    struct Account has key {
        balance: u256,
        nonce: u64,
        is_contract: bool,
        code: vector<u8>,
        storage: Table<u256, vector<u8>>,
    }

    struct Log0Event has drop, store {
        contract: vector<u8>,
        data: vector<u8>
    }

    struct Log1Event has drop, store {
        contract: vector<u8>,
        data: vector<u8>,
        topic0: vector<u8>
    }

    struct Log2Event has drop, store {
        contract: vector<u8>,
        data: vector<u8>,
        topic0: vector<u8>,
        topic1: vector<u8>
    }

    struct Log3Event has drop, store {
        contract: vector<u8>,
        data: vector<u8>,
        topic0: vector<u8>,
        topic1: vector<u8>,
        topic2: vector<u8>
    }

    struct Log4Event has drop, store {
        contract: vector<u8>,
        data: vector<u8>,
        topic0: vector<u8>,
        topic1: vector<u8>,
        topic2: vector<u8>,
        topic3: vector<u8>
    }

    struct ContractEvent has key {
        log0Event: EventHandle<Log0Event>,
        log1Event: EventHandle<Log1Event>,
        log2Event: EventHandle<Log2Event>,
        log3Event: EventHandle<Log3Event>,
        log4Event: EventHandle<Log4Event>,
    }

    native fun revert(
        message: vector<u8>
    );

    native fun decode_raw_tx(
        raw_tx: vector<u8>
    ): (u64, u64, vector<u8>, vector<u8>, u256, vector<u8>);

    native fun mul_mod(a: u256, b: u256, n: u256): u256;
    native fun add(a: u256, b: u256): u256;
    native fun sub(a: u256, b: u256): u256;
    native fun mul(a: u256, b: u256): u256;
    native fun exp(a: u256, b: u256): u256;

    public entry fun send_tx(
        sender: &signer,
        _evm_from: vector<u8>,
        tx: vector<u8>,
        gas_bytes: vector<u8>,
        _tx_type: u64,
    ) acquires Account, ContractEvent {
        let gas = to_u256(gas_bytes);
        let (chain_id, nonce, evm_from, evm_to, value, data) = decode_raw_tx(tx);
        assert!(chain_id == CHAIN_ID || chain_id == 0, INVALID_CHAINID);
        execute(to_32bit(evm_from), to_32bit(evm_to), nonce, data, value);
        transfer_to_move_addr(to_32bit(evm_from), address_of(sender), gas * CONVERT_BASE);
    }

    public entry fun estimate_tx_gas(
        evm_from: vector<u8>,
        evm_to: vector<u8>,
        data: vector<u8>,
        value_bytes: vector<u8>,
        _tx_type: u64,
    ) acquires Account, ContractEvent {
        let value = to_u256(value_bytes);
        let address_from = create_resource_address(&@aptos_framework, to_32bit(evm_from));
        assert!(exists<Account>(address_from), ACCOUNT_NOT_EXIST);
        let nonce = borrow_global<Account>(create_resource_address(&@aptos_framework, to_32bit(evm_from))).nonce;
        execute(to_32bit(evm_from), to_32bit(evm_to), nonce, data, value);
    }

    public entry fun deposit(sender: &signer, evm_addr: vector<u8>, amount_bytes: vector<u8>) acquires Account {
        let amount = to_u256(amount_bytes);
        assert!(vector::length(&evm_addr) == 20, ADDR_LENGTH);
        transfer_from_move_addr(sender, to_32bit(evm_addr), amount);
    }

    #[view]
    public fun get_code(contract_addr: vector<u8>): vector<u8> acquires Account {
        let move_addr = create_resource_address(&@aptos_framework, contract_addr);
        if(!exists<Account>(move_addr)) {
            x""
        } else {
            borrow_global<Account>(move_addr).code
        }
    }

    #[view]
    public fun get_move_address(evm_addr: vector<u8>): address {
        create_resource_address(&@aptos_framework, to_32bit(evm_addr))
    }

    #[view]
    public fun query(sender:vector<u8>, contract_addr: vector<u8>, data: vector<u8>): vector<u8> acquires Account, ContractEvent {
        contract_addr = to_32bit(contract_addr);
        let contract_store = borrow_global_mut<Account>(create_resource_address(&@aptos_framework, contract_addr));
        sender = to_32bit(sender);
        let (res, bytes) = run(sender, sender, contract_addr, contract_store.code, data, true, 0, &mut simple_map::new<u256, u256>());
        handle_exdlecute_result(res, bytes)
    }

    #[view]
    public fun get_storage_at(addr: vector<u8>, slot: vector<u8>): vector<u8> acquires Account {
        let move_address = create_resource_address(&@aptos_framework, to_32bit(addr));
        if(exists<Account>(move_address)) {
            let account_store = borrow_global<Account>(move_address);
            let slot_u256 = data_to_u256(slot, 0, (vector::length(&slot) as u256));
            if(table::contains(&account_store.storage, slot_u256)) {
                *table::borrow(&account_store.storage, slot_u256)
            } else {
                vector::empty<u8>()
            }
        } else {
            vector::empty<u8>()
        }

    }

    fun handle_exdlecute_result(res: bool, bytes: vector<u8>): vector<u8> {

        if(!res) {
            throw_error(bytes);
            x""
        } else {
            bytes
        }
    }

    fun throw_error(bytes: vector<u8>) {
        let message = if(vector::length(&bytes) == 0) x"" else {
            let len = to_u256(slice(bytes, 36, 32));
            slice(bytes, 68, len)
        };
        debug::print(&message);
        revert(message);
    }

    fun execute(evm_from: vector<u8>, evm_to: vector<u8>, nonce: u64, data: vector<u8>, value: u256): vector<u8> acquires Account, ContractEvent {
        let address_from = create_resource_address(&@aptos_framework, evm_from);
        let address_to = create_resource_address(&@aptos_framework, evm_to);
        create_account_if_not_exist(address_from);
        create_account_if_not_exist(address_to);
        verify_nonce(address_from, nonce);
        let account_store_to = borrow_global_mut<Account>(address_to);
        let transient = &mut simple_map::new<u256, u256>();
        if(evm_to == ZERO_ADDR) {
            let evm_contract = get_contract_address(evm_from, nonce);
            let address_contract = create_resource_address(&@aptos_framework, evm_contract);
            create_account_if_not_exist(address_contract);
            create_event_if_not_exist(address_contract);
            borrow_global_mut<Account>(address_contract).is_contract = true;
            let (res, code) = run(evm_from, evm_from, evm_contract, data, x"", false, value, transient);
            borrow_global_mut<Account>(address_contract).code = code;
            handle_exdlecute_result(res, evm_contract)
        } else if(evm_to == ONE_ADDR) {
            let amount = data_to_u256(data, 36, 32);
            let to = to_address(slice(data, 100, 32));
            transfer_to_move_addr(evm_from, to, amount);
            x""
        } else {
            if(account_store_to.is_contract) {
                let (res, bytes) = run(evm_from, evm_from, evm_to, account_store_to.code, data, false, value, transient);
                handle_exdlecute_result(res, bytes)
            } else {
                transfer_to_evm_addr(evm_from, evm_to, value);
                x""
            }
        }
    }

    // This function is used to execute precompile EVM contracts.
    fun precompile(sender: vector<u8>, to: vector<u8>, value: u256, calldata: vector<u8>): vector<u8> acquires Account {
        transfer_to_evm_addr(sender, to, value);
        run_precompile(to, calldata, CHAIN_ID)
    }

    // fun exec_call(sender: vector<u8>, origin: vector<u8>, evm_contract_address: vector<u8>, code: vector<u8>, data: vector<u8>, readOnly: bool, value: u256, transient: &mut SimpleMap<u256, u256>): (bool, vector<u8>) acquires Account, ContractEvent {(sender: vector<u8>, origin: vector<u8>, evm_contract_address: vector<u8>, code: vector<u8>, data: vector<u8>, readOnly: bool, value: u256, transient: &mut SimpleMap<u256, u256>): (bool, vector<u8>) acquires Account, ContractEvent {
    //
    // }

    // This function is used to execute EVM bytecode.
    // Parameters:
    // - sender: The address of the sender.
    // - origin: The original invoker of the transaction.
    // - evm_contract_address: The EVM address of the contract.
    // - code: The EVM bytecode to be executed.
    // - data: The input data for the execution.
    // - readOnly: A boolean flag indicating whether the execution should be read-only.
    // - value: The value to be transferred during the execution.
    fun run(sender: vector<u8>, origin: vector<u8>, evm_contract_address: vector<u8>, code: vector<u8>, data: vector<u8>, readOnly: bool, value: u256, transient: &mut SimpleMap<u256, u256>): (bool, vector<u8>) acquires Account, ContractEvent {
        if (is_precompile_address(evm_contract_address)) {
            return (true, precompile(sender, evm_contract_address, value, data))
        };

        // Convert the EVM address to a Move resource address.
        let move_contract_address = create_resource_address(&@aptos_framework, evm_contract_address);
        // Transfer the specified value to the EVM address
        transfer_to_evm_addr(sender, evm_contract_address, value);
        // Initialize an empty stack and memory for the EVM execution.
        let stack = &mut vector::empty<u256>();
        let memory = &mut vector::empty<u8>();
        // let
        // Get the length of the bytecode.
        let len = vector::length(&code);
        // Initialize an empty vector for the runtime code.
        let runtime_code = vector::empty<u8>();
        // Initialize counters for the execution loop.
        let i = 0;
        let ret_size = 0;
        let ret_bytes = vector::empty<u8>();

        // Start the execution loop.
        while (i < len) {
            // Fetch the current opcode from the bytecode.

            let opcode = *vector::borrow(&code, i);
            // debug::print(&i);
            // debug::print(&opcode);

            // Handle each opcode according to the EVM specification.
            // The following is a simplified version of the EVM execution engine,
            // handling only a subset of all possible opcodes.
            // Each branch in this if-else chain corresponds to a specific opcode,
            // and contains the logic for executing that opcode.
            // For example, the `add` opcode pops two elements from the stack,
            // adds them together, and pushes the result back onto the stack.
            // The `mul` opcode does the same but with multiplication, and so on.
            // Some opcodes, like `sstore`, have side effects, such as modifying contract storage.
            // The `jump` and `jumpi` opcodes alter the control flow of the execution.
            // The `call`, `create`, and `create2` opcodes are used for contract interactions.
            // The `log` opcodes are used for emitting events.
            // The function returns the output data of the execution when it encounters the `stop` or `return` opcode.

            // stop
            if(opcode == 0x00) {
                ret_bytes = runtime_code;
                break
            }
            else if(opcode == 0xf3) {
                let pos = vector::pop_back(stack);
                let len = vector::pop_back(stack);
                ret_bytes = slice(*memory, pos, len);
                break
            }
                //add
            else if(opcode == 0x01) {
                let a = vector::pop_back(stack);
                let b = vector::pop_back(stack);
                if(a > 0 && b >= (U256_MAX - a + 1)) {
                    vector::push_back(stack, b - (U256_MAX - a + 1));
                } else {
                    vector::push_back(stack, a + b);
                };
                i = i + 1;
            }
                //mul
            else if(opcode == 0x02) {
                let a = vector::pop_back(stack);
                let b = vector::pop_back(stack);
                vector::push_back(stack, mul(a, b));
                i = i + 1;
            }
                //sub
            else if(opcode == 0x03) {
                let a = vector::pop_back(stack);
                let b = vector::pop_back(stack);
                if(a >= b) {
                    vector::push_back(stack, a - b);
                } else {
                    vector::push_back(stack, U256_MAX - b + a + 1);
                };
                i = i + 1;
            }
                //div
            else if(opcode == 0x04) {
                let a = vector::pop_back(stack);
                let b = vector::pop_back(stack);
                vector::push_back(stack, if(b == 0) 0 else a / b);
                i = i + 1;
            }
                //sdiv
            else if(opcode == 0x05) {
                let(sg_a, num_a) = to_int256(vector::pop_back(stack));
                let(sg_b, num_b) = to_int256(vector::pop_back(stack));
                let num_c = num_a / num_b;
                vector::push_back(stack, add_sign(num_c, (!sg_a && sg_b) || (sg_a && !sg_b)));
                i = i + 1;
            }
                //mod
            else if(opcode == 0x06) {
                let a = vector::pop_back(stack);
                let b = vector::pop_back(stack);
                vector::push_back(stack, a % b);
                i = i + 1;
            }
                //smod
            else if(opcode == 0x07) {
                let(sg_a, num_a) = to_int256(vector::pop_back(stack));
                let(_sg_b, num_b) = to_int256(vector::pop_back(stack));
                let num_c = num_a % num_b;
                vector::push_back(stack, add_sign(num_c, sg_a));
                i = i + 1;
            }
                //addmod
            else if(opcode == 0x08) {
                let a = vector::pop_back(stack);
                let b = vector::pop_back(stack);
                let n = vector::pop_back(stack);
                vector::push_back(stack, (a + b) % n);
                i = i + 1;
            }
                //mulmod
            else if(opcode == 0x09) {
                let a = vector::pop_back(stack);
                let b = vector::pop_back(stack);
                let n = vector::pop_back(stack);
                vector::push_back(stack, mul_mod(a, b, n));
                i = i + 1;
            }
                //exp
            else if(opcode == 0x0a) {
                let a = vector::pop_back(stack);
                let b = vector::pop_back(stack);
                vector::push_back(stack, exp(a, b));
                i = i + 1;
            }
                //signextend
            else if(opcode == 0x0b) {
                let b = vector::pop_back(stack);
                let value = vector::pop_back(stack);
                if(b > 31) {
                    vector::push_back(stack, value);
                } else {
                    let index = ((8 * b + 7) as u8);
                    let mask = (1 << index) - 1;
                    if(((value >> index) & 1) == 0) {
                        vector::push_back(stack, value & mask);
                    } else {
                        vector::push_back(stack, value | (U256_MAX - mask));
                    };
                };
                i = i + 1;
            }
                //lt
            else if(opcode == 0x10) {
                let a = vector::pop_back(stack);
                let b = vector::pop_back(stack);
                if(a < b) {
                    vector::push_back(stack, 1)
                } else {
                    vector::push_back(stack, 0)
                };
                i = i + 1;
            }
                //gt
            else if(opcode == 0x11) {
                let a = vector::pop_back(stack);
                let b = vector::pop_back(stack);
                if(a > b) {
                    vector::push_back(stack, 1)
                } else {
                    vector::push_back(stack, 0)
                };
                i = i + 1;
            }
                //slt
            else if(opcode == 0x12) {
                let a = vector::pop_back(stack);
                let b = vector::pop_back(stack);
                let(neg_a, num_a) = to_int256(a);
                let(neg_b, num_b) = to_int256(b);

                let is_positive_lt = num_a < num_b && !(neg_a || neg_b);
                let is_negative_lt = num_a > num_b && (neg_a && neg_b);
                let has_different_signs = neg_a && !neg_b;

                let value = 0;
                if(is_positive_lt || is_negative_lt || has_different_signs) {
                    value = 1
                };
                vector::push_back(stack, value);
                i = i + 1;
            }
                //sgt
            else if(opcode == 0x13) {
                let a = vector::pop_back(stack);
                let b = vector::pop_back(stack);
                let(neg_a, num_a) = to_int256(a);
                let(neg_b, num_b) = to_int256(b);

                let is_positive_gt = num_a > num_b && !(neg_a || neg_b);
                let is_negative_gt = num_a < num_b && (neg_a && neg_b);
                let has_different_signs = !neg_a && neg_b;
                let value = 0;
                if(is_positive_gt || is_negative_gt || has_different_signs) {
                    value = 1
                };
                vector::push_back(stack, value);
                i = i + 1;
            }
                //eq
            else if(opcode == 0x14) {
                let a = vector::pop_back(stack);
                let b = vector::pop_back(stack);
                if(a == b) {
                    vector::push_back(stack, 1);
                } else {
                    vector::push_back(stack, 0);
                };
                i = i + 1;
            }
                //and
            else if(opcode == 0x16) {
                let a = vector::pop_back(stack);
                let b = vector::pop_back(stack);
                vector::push_back(stack, a & b);
                i = i + 1;
            }
                //or
            else if(opcode == 0x17) {
                let a = vector::pop_back(stack);
                let b = vector::pop_back(stack);
                vector::push_back(stack, a | b);
                i = i + 1;
            }
                //xor
            else if(opcode == 0x18) {
                let a = vector::pop_back(stack);
                let b = vector::pop_back(stack);
                vector::push_back(stack, a ^ b);
                i = i + 1;
            }
                //not
            else if(opcode == 0x19) {
                // 10 1010
                // 6 0101
                let n = vector::pop_back(stack);
                vector::push_back(stack, U256_MAX - n);
                i = i + 1;
            }
                //byte
            else if(opcode == 0x1a) {
                let ith = vector::pop_back(stack);
                let x = vector::pop_back(stack);
                if(ith >= 32) {
                    vector::push_back(stack, 0);
                } else {
                    vector::push_back(stack, (x >> ((248 - ith * 8) as u8)) & 0xFF);
                };

                i = i + 1;
            }
                //shl
            else if(opcode == 0x1b) {
                let b = vector::pop_back(stack);
                let a = vector::pop_back(stack);
                if(b >= 256) {
                    vector::push_back(stack, 0);
                } else {
                    vector::push_back(stack, a << (b as u8));
                };
                i = i + 1;
            }
                //shr
            else if(opcode == 0x1c) {
                let b = vector::pop_back(stack);
                let a = vector::pop_back(stack);
                if(b >= 256) {
                    vector::push_back(stack, 0);
                } else {
                    vector::push_back(stack, a >> (b as u8));
                };

                i = i + 1;
            }
                //sar
            else if(opcode == 0x1d) {
                let b = vector::pop_back(stack);
                let a = vector::pop_back(stack);
                let(neg, num_a) = to_int256(a);
                let c = 0;
                if(b == 0 || b >= 256) {
                    if(neg) {
                        c = U256_MAX;
                    }
                } else {
                    if(neg) {
                        let n = num_a >> (b as u8);
                        c = if(n > 0) U256_MAX - n + 1 else 0;
                    } else {
                        c = a >> (b as u8);
                    }
                };

                vector::push_back(stack, c);
                i = i + 1;
            }
                //push0
            else if(opcode == 0x5f) {
                vector::push_back(stack, 0);
                i = i + 1;
            }
                // push1 -> push32
            else if(opcode >= 0x60 && opcode <= 0x7f)  {
                let n = ((opcode - 0x60) as u64);
                let number = data_to_u256(code, ((i + 1) as u256), ((n + 1) as u256));
                vector::push_back(stack, number);
                i = i + n + 2;
            }
                // pop
            else if(opcode == 0x50) {
                vector::pop_back(stack);
                i = i + 1
            }
                //address
            else if(opcode == 0x30) {
                vector::push_back(stack, data_to_u256(evm_contract_address, 0, 32));
                i = i + 1;
            }
                //balance
            else if(opcode == 0x31) {
                let evm_addr = u256_to_data(vector::pop_back(stack));
                let target_address = create_resource_address(&@aptos_framework, evm_addr);
                if(exists<Account>(target_address)) {
                    let account_store = borrow_global<Account>(target_address);
                    vector::push_back(stack, account_store.balance);
                } else {
                    vector::push_back(stack, 0)
                };
                i = i + 1;
            }
                //origin
            else if(opcode == 0x32) {
                let value = data_to_u256(origin, 0, 32);
                vector::push_back(stack, value);
                i = i + 1;
            }
                //caller
            else if(opcode == 0x33) {
                let value = data_to_u256(sender, 0, 32);
                vector::push_back(stack, value);
                i = i + 1;
            }
                // callvalue
            else if(opcode == 0x34) {
                vector::push_back(stack, value);
                i = i + 1;
            }
                //calldataload
            else if(opcode == 0x35) {
                let pos = vector::pop_back(stack);
                vector::push_back(stack, data_to_u256(data, pos, 32));
                i = i + 1;
                // block.
            }
                //calldatasize
            else if(opcode == 0x36) {
                vector::push_back(stack, (vector::length(&data) as u256));
                i = i + 1;
            }
                //calldatacopy
            else if(opcode == 0x37) {
                let m_pos = vector::pop_back(stack);
                let d_pos = vector::pop_back(stack);
                let len = vector::pop_back(stack);
                let end = d_pos + len;
                // debug::print(&utf8(b"calldatacopy"));
                // debug::print(&data);
                while (d_pos < end) {
                    // debug::print(&d_pos);
                    // debug::print(&end);
                    let bytes = if(end - d_pos >= 32) {
                        slice(data, d_pos, 32)
                    } else {
                        slice(data, d_pos, end - d_pos)
                    };
                    // debug::print(&bytes);
                    mstore(memory, m_pos, bytes);
                    d_pos = d_pos + 32;
                    m_pos = m_pos + 32;
                };
                i = i + 1
            }
                //codesize
            else if(opcode == 0x38) {
                vector::push_back(stack, (vector::length(&code) as u256));
                i = i + 1
            }
                //codecopy
            else if(opcode == 0x39) {
                let m_pos = vector::pop_back(stack);
                let d_pos = vector::pop_back(stack);
                let len = vector::pop_back(stack);
                let end = d_pos + len;
                runtime_code = slice(code, d_pos, len);
                while (d_pos < end) {
                    let bytes = if(end - d_pos >= 32) {
                        slice(code, d_pos, 32)
                    } else {
                        slice(code, d_pos, end - d_pos)
                    };
                    mstore(memory, m_pos, bytes);
                    d_pos = d_pos + 32;
                    m_pos = m_pos + 32;
                };
                i = i + 1
            }
                //extcodesize
            else if(opcode == 0x3b) {
                let bytes = u256_to_data(vector::pop_back(stack));
                let target_evm = to_32bit(slice(bytes, 12, 20));
                let target_address = create_resource_address(&@aptos_framework, target_evm);
                if(exist_contract(target_address)) {
                    let code = borrow_global<Account>(target_address).code;
                    vector::push_back(stack, (vector::length(&code) as u256));
                } else {
                    vector::push_back(stack, 0);
                };

                i = i + 1;
            }
                //returndatacopy
            else if(opcode == 0x3e) {
                // mstore()
                let m_pos = vector::pop_back(stack);
                let d_pos = vector::pop_back(stack);
                let len = vector::pop_back(stack);
                let bytes = slice(ret_bytes, d_pos, len);
                mstore(memory, m_pos, bytes);
                i = i + 1;
            }
                //returndatasize
            else if(opcode == 0x3d) {
                vector::push_back(stack, ret_size);
                i = i + 1;
            }
                //blockhash
            else if(opcode == 0x40) {
                vector::push_back(stack, 0);
                i = i + 1;
            }
                //coinbase
            else if(opcode == 0x41) {
                vector::push_back(stack, 0);
                i = i + 1;
            }
                //timestamp
            else if(opcode == 0x42) {
                vector::push_back(stack, (now_microseconds() as u256) / 1000000);
                i = i + 1;
            }
                //number
            else if(opcode == 0x43) {
                vector::push_back(stack, (block::get_current_block_height() as u256));
                i = i + 1;
            }
                //difficulty
            else if(opcode == 0x44) {
                vector::push_back(stack, 0);
                i = i + 1;
            }
                //gaslimit
            else if(opcode == 0x45) {
                vector::push_back(stack, 30000000);
                i = i + 1;
            }
                //chainid
            else if(opcode == 0x46) {
                vector::push_back(stack, 1);
                i = i + 1
            }
                //self balance
            else if(opcode == 0x47) {
                let contract_store = borrow_global_mut<Account>(move_contract_address);
                vector::push_back(stack, contract_store.balance);
                i = i + 1;
            }
                // mload
            else if(opcode == 0x51) {
                let pos = vector::pop_back(stack);
                vector::push_back(stack, data_to_u256(slice(*memory, pos, 32), 0, 32));
                i = i + 1;
            }
                // mstore
            else if(opcode == 0x52) {
                let pos = vector::pop_back(stack);
                let value = vector::pop_back(stack);
                mstore(memory, pos, u256_to_data(value));
                // debug::print(memory);
                i = i + 1;

            }
                //mstore8
            else if(opcode == 0x53) {
                let pos = vector::pop_back(stack);
                let value = vector::pop_back(stack);
                *vector::borrow_mut(memory, (pos as u64)) = ((value & 0xff) as u8);
                // mstore(memory, pos, u256_to_data(value & 0xff));
                // debug::print(memory);
                i = i + 1;

            }
                // sload
            else if(opcode == 0x54) {
                let pos = vector::pop_back(stack);
                let contract_store = borrow_global_mut<Account>(move_contract_address);
                if(table::contains(&contract_store.storage, pos)) {
                    let value = *table::borrow(&mut contract_store.storage, pos);
                    vector::push_back(stack, data_to_u256(value, 0, 32));
                } else {
                    vector::push_back(stack, 0);
                };
                i = i + 1;
            }
                // sstore
            else if(opcode == 0x55) {
                if(readOnly) {
                    assert!(false, CONTRACT_READ_ONLY);
                };
                let contract_store = borrow_global_mut<Account>(move_contract_address);
                let pos = vector::pop_back(stack);
                let value = vector::pop_back(stack);
                table::upsert(&mut contract_store.storage, pos, u256_to_data(value));
                // debug::print(&utf8(b"sstore"));
                // debug::print(&evm_contract_address);
                // debug::print(&pos);
                // debug::print(&value);
                i = i + 1;
            }
                //dup1 -> dup16
            else if(opcode >= 0x80 && opcode <= 0x8f) {
                let size = vector::length(stack);
                let value = *vector::borrow(stack, size - ((opcode - 0x80 + 1) as u64));
                vector::push_back(stack, value);
                i = i + 1;
            }
                //swap1 -> swap16
            else if(opcode >= 0x90 && opcode <= 0x9f) {
                let size = vector::length(stack);
                vector::swap(stack, size - 1, size - ((opcode - 0x90 + 2) as u64));
                i = i + 1;
            }
                //iszero
            else if(opcode == 0x15) {
                let value = vector::pop_back(stack);
                if(value == 0) {
                    vector::push_back(stack, 1)
                } else {
                    vector::push_back(stack, 0)
                };
                i = i + 1;
            }
                //jump
            else if(opcode == 0x56) {
                let dest = vector::pop_back(stack);
                i = (dest as u64) + 1
            }
                //jumpi
            else if(opcode == 0x57) {
                let dest = vector::pop_back(stack);
                let condition = vector::pop_back(stack);
                if(condition > 0) {
                    i = (dest as u64) + 1
                } else {
                    i = i + 1
                }
            }
                //gas
            else if(opcode == 0x5a) {
                vector::push_back(stack, 0);
                i = i + 1
            }
                //jump dest (no action, continue execution)
            else if(opcode == 0x5b) {
                i = i + 1
            }
                //TLOAD
            else if(opcode == 0x5c) {
                let key = vector::pop_back(stack);
                if(simple_map::contains_key(transient, &key)) {
                    vector::push_back(stack, *simple_map::borrow(transient, &key));
                } else {
                    vector::push_back(stack, 0);
                };

                i = i + 1
            }
                //TSTORE
            else if(opcode == 0x5d) {
                let key = vector::pop_back(stack);
                let value = vector::pop_back(stack);
                simple_map::upsert(transient, key, value);
                i = i + 1
            }
                //MCOPY
            else if(opcode == 0x5e) {
                let m_pos = vector::pop_back(stack);
                let d_pos = vector::pop_back(stack);
                let len = vector::pop_back(stack);
                let bytes = slice(*memory, d_pos, len);
                mstore(memory, m_pos, bytes);
                i = i + 1;
            }
                //sha3
            else if(opcode == 0x20) {
                let pos = vector::pop_back(stack);
                let len = vector::pop_back(stack);
                let bytes = slice(*memory, pos, len);
                // debug::print(&utf8(b"sha3"));
                // debug::print(&bytes);
                let value = data_to_u256(keccak256(bytes), 0, 32);
                // debug::print(&keccak256(bytes));
                vector::push_back(stack, value);
                i = i + 1
            }
                //call 0xf1 static call 0xfa delegate call 0xf4
            else if(opcode == 0xf1 || opcode == 0xfa || opcode == 0xf4) {
                let readOnly = if (opcode == 0xfa) true else false;
                let _gas = vector::pop_back(stack);
                let evm_dest_addr = to_32bit(u256_to_data(vector::pop_back(stack)));
                let move_dest_addr = create_resource_address(&@aptos_framework, evm_dest_addr);
                let msg_value = if (opcode == 0xf1) vector::pop_back(stack) else 0;
                let m_pos = vector::pop_back(stack);
                let m_len = vector::pop_back(stack);
                let ret_pos = vector::pop_back(stack);
                let ret_len = vector::pop_back(stack);
                let ret_end = ret_len + ret_pos;
                let params = slice(*memory, m_pos, m_len);

                // debug::print(&utf8(b"call 222"));
                // debug::print(&opcode);
                // debug::print(&dest_addr);
                if (is_precompile_address(evm_dest_addr) ||exist_contract(move_dest_addr)) {
                    let dest_code = get_code(evm_dest_addr);

                    let target = if (opcode == 0xf4) evm_contract_address else evm_dest_addr;
                    let from = if (opcode == 0xf4) sender else evm_contract_address;
                    let(call_res, bytes) = run(from, sender, target, dest_code, params, readOnly, msg_value, transient);
                    ret_size = (vector::length(&bytes) as u256);
                    ret_bytes = bytes;
                    let index = 0;

                    while (ret_pos < ret_end) {
                        let bytes = if (ret_end - ret_pos >= 32) {
                            slice(bytes, index, 32)
                        } else {
                            slice(bytes, index, ret_end - ret_pos)
                        };
                        mstore(memory, ret_pos, bytes);
                        ret_pos = ret_pos + 32;
                        index = index + 32;
                    };
                    vector::push_back(stack, if(call_res) 1 else 0);
                } else {
                    transfer_to_evm_addr(evm_contract_address, evm_dest_addr, msg_value);
                    vector::push_back(stack, 1);
                };
                // debug::print(&opcode);
                i = i + 1
            }
                //create
            else if(opcode == 0xf0) {
                if(readOnly) {
                    assert!(false, CONTRACT_READ_ONLY);
                };
                let msg_value = vector::pop_back(stack);
                let pos = vector::pop_back(stack);
                let len = vector::pop_back(stack);
                let new_codes = slice(*memory, pos, len);
                let contract_store = borrow_global_mut<Account>(move_contract_address);
                let nonce = contract_store.nonce;
                // must be 20 bytes

                let new_evm_contract_addr = get_contract_address(evm_contract_address, nonce);
                // debug::print(&utf8(b"create start"));
                // debug::print(&nonce);
                // debug::print(&new_evm_contract_addr);
                let new_move_contract_addr = create_resource_address(&@aptos_framework, new_evm_contract_addr);
                contract_store.nonce = contract_store.nonce + 1;

                // debug::print(&exists<Account>(new_move_contract_addr));
                assert!(!exist_contract(new_move_contract_addr), CONTRACT_DEPLOYED);
                create_account_if_not_exist(new_move_contract_addr);
                create_event_if_not_exist(new_move_contract_addr);

                let (create_res, bytes) = run(evm_contract_address, sender, new_evm_contract_addr, new_codes, x"", false, msg_value, transient);
                if(create_res) {
                    borrow_global_mut<Account>(new_move_contract_addr).code = bytes;
                    borrow_global_mut<Account>(new_move_contract_addr).nonce = 1;
                    borrow_global_mut<Account>(new_move_contract_addr).is_contract = true;
                    ret_bytes = new_evm_contract_addr;
                    vector::push_back(stack, data_to_u256(new_evm_contract_addr, 0, 32));
                } else {
                    ret_bytes = bytes;
                    vector::push_back(stack, 0);
                };

                debug::print(&utf8(b"create end"));
                ret_size = 32;


                i = i + 1
            }
                //create2
            else if(opcode == 0xf5) {
                if(readOnly) {
                    assert!(false, CONTRACT_READ_ONLY);
                };
                let msg_value = vector::pop_back(stack);
                let pos = vector::pop_back(stack);
                let len = vector::pop_back(stack);
                let salt = u256_to_data(vector::pop_back(stack));
                let new_codes = slice(*memory, pos, len);
                let p = vector::empty<u8>();
                // let contract_store = ;
                vector::append(&mut p, x"ff");
                // must be 20 bytes
                vector::append(&mut p, slice(evm_contract_address, 12, 20));
                vector::append(&mut p, salt);
                vector::append(&mut p, keccak256(new_codes));
                let new_evm_contract_addr = to_32bit(slice(keccak256(p), 12, 20));
                let new_move_contract_addr = create_resource_address(&@aptos_framework, new_evm_contract_addr);
                debug::print(&utf8(b"create2 start"));
                debug::print(&evm_contract_address);
                debug::print(&sender);
                debug::print(&p);
                debug::print(&new_evm_contract_addr);
                assert!(!exist_contract(new_move_contract_addr), CONTRACT_DEPLOYED);
                create_account_if_not_exist(new_move_contract_addr);
                create_event_if_not_exist(new_move_contract_addr);

                // debug::print(&p);
                // debug::print(&new_codes);
                // debug::print(&new_contract_addr);
                borrow_global_mut<Account>(move_contract_address).nonce = borrow_global_mut<Account>(move_contract_address).nonce + 1;
                let (create_res, bytes) = run(evm_contract_address, sender, new_evm_contract_addr, new_codes, x"", false, msg_value, transient);
                if(create_res) {
                    borrow_global_mut<Account>(new_move_contract_addr).nonce = 1;
                    borrow_global_mut<Account>(new_move_contract_addr).is_contract = true;
                    borrow_global_mut<Account>(new_move_contract_addr).code = bytes;

                    ret_bytes = new_evm_contract_addr;
                    vector::push_back(stack, data_to_u256(new_evm_contract_addr, 0, 32));
                } else {
                    ret_bytes = bytes;
                    vector::push_back(stack, 0);
                };

                ret_size = 32;
                i = i + 1
            }
                //revert
            else if(opcode == 0xfd) {
                let pos = vector::pop_back(stack);
                let len = vector::pop_back(stack);
                let bytes = slice(*memory, pos, len);
                debug::print(&utf8(b"revert"));
                debug::print(&bytes);
                // debug::print(&pos);
                // debug::print(&len);
                // debug::print(memory);
                // i = i + 1;
                return (false, bytes)
            }
                //log0
            else if(opcode == 0xa0) {
                let pos = vector::pop_back(stack);
                let len = vector::pop_back(stack);
                let data = slice(*memory, pos, len);
                let event_store = borrow_global_mut<ContractEvent>(move_contract_address);
                event::emit_event<Log0Event>(
                    &mut event_store.log0Event,
                    Log0Event{
                        contract: evm_contract_address,
                        data,
                    },
                );
                i = i + 1
            }
                //log1
            else if(opcode == 0xa1) {
                let pos = vector::pop_back(stack);
                let len = vector::pop_back(stack);
                let data = slice(*memory, pos, len);
                let topic0 = u256_to_data(vector::pop_back(stack));
                let event_store = borrow_global_mut<ContractEvent>(move_contract_address);
                event::emit_event<Log1Event>(
                    &mut event_store.log1Event,
                    Log1Event{
                        contract: evm_contract_address,
                        data,
                        topic0,
                    },
                );
                i = i + 1
            }
                //log2
            else if(opcode == 0xa2) {
                let pos = vector::pop_back(stack);
                let len = vector::pop_back(stack);
                let data = slice(*memory, pos, len);
                let topic0 = u256_to_data(vector::pop_back(stack));
                let topic1 = u256_to_data(vector::pop_back(stack));
                let event_store = borrow_global_mut<ContractEvent>(move_contract_address);
                event::emit_event<Log2Event>(
                    &mut event_store.log2Event,
                    Log2Event{
                        contract: evm_contract_address,
                        data,
                        topic0,
                        topic1
                    },
                );
                i = i + 1
            }
                //log3
            else if(opcode == 0xa3) {
                let pos = vector::pop_back(stack);
                let len = vector::pop_back(stack);
                let data = slice(*memory, pos, len);
                let topic0 = u256_to_data(vector::pop_back(stack));
                let topic1 = u256_to_data(vector::pop_back(stack));
                let topic2 = u256_to_data(vector::pop_back(stack));
                let event_store = borrow_global_mut<ContractEvent>(move_contract_address);
                event::emit_event<Log3Event>(
                    &mut event_store.log3Event,
                    Log3Event{
                        contract: evm_contract_address,
                        data,
                        topic0,
                        topic1,
                        topic2
                    },
                );
                i = i + 1
            }
                //log4
            else if(opcode == 0xa4) {
                let pos = vector::pop_back(stack);
                let len = vector::pop_back(stack);
                let data = slice(*memory, pos, len);
                let topic0 = u256_to_data(vector::pop_back(stack));
                let topic1 = u256_to_data(vector::pop_back(stack));
                let topic2 = u256_to_data(vector::pop_back(stack));
                let topic3 = u256_to_data(vector::pop_back(stack));
                let event_store = borrow_global_mut<ContractEvent>(move_contract_address);
                event::emit_event<Log4Event>(
                    &mut event_store.log4Event,
                    Log4Event{
                        contract: evm_contract_address,
                        data,
                        topic0,
                        topic1,
                        topic2,
                        topic3
                    },
                );
                i = i + 1
            }
            else {
                assert!(false, (opcode as u64));
            };
            // debug::print(stack);
            // debug::print(&vector::length(stack));
        };
        // simple_map::borrow_mut<vector<u8>, T>(&mut global.contracts, &contract_addr).storage = storage;
        (true, ret_bytes)
    }

    fun exist_contract(addr: address): bool acquires Account {
        exists<Account>(addr) && (vector::length(&borrow_global<Account>(addr).code) > 0)
    }

    fun add_balance(addr: address, amount: u256) acquires Account {
        create_account_if_not_exist(addr);
        if(amount > 0) {
            let account_store = borrow_global_mut<Account>(addr);
            account_store.balance = account_store.balance + amount;
        }
    }

    fun transfer_from_move_addr(signer: &signer, evm_to: vector<u8>, amount: u256) acquires Account {
        if(amount > 0) {
            let move_to = create_resource_address(&@aptos_framework, evm_to);
            create_account_if_not_exist(move_to);
            coin::transfer<AptosCoin>(signer, move_to, ((amount / CONVERT_BASE)  as u64));

            let account_store_to = borrow_global_mut<Account>(move_to);
            account_store_to.balance = account_store_to.balance + amount;
        }
    }

    fun transfer_to_evm_addr(evm_from: vector<u8>, evm_to: vector<u8>, amount: u256) acquires Account {
        if(amount > 0) {
            let move_from = create_resource_address(&@aptos_framework, evm_from);
            let move_to = create_resource_address(&@aptos_framework, evm_to);
            create_account_if_not_exist(move_to);
            let account_store_from = borrow_global_mut<Account>(move_from);
            assert!(account_store_from.balance >= amount, INSUFFIENT_BALANCE);
            account_store_from.balance = account_store_from.balance - amount;

            let account_store_to = borrow_global_mut<Account>(move_to);
            account_store_to.balance = account_store_to.balance + amount;

            let signer = create_signer(move_from);
            coin::transfer<AptosCoin>(&signer, move_to, ((amount / CONVERT_BASE)  as u64));
        }
    }

    fun transfer_to_move_addr(evm_from: vector<u8>, move_to: address, amount: u256) acquires Account {
        if(amount > 0) {
            let move_from = create_resource_address(&@aptos_framework, evm_from);
            let account_store_from = borrow_global_mut<Account>(move_from);
            assert!(account_store_from.balance >= amount, INSUFFIENT_BALANCE);
            account_store_from.balance = account_store_from.balance - amount;

            let signer = create_signer(move_from);
            coin::transfer<AptosCoin>(&signer, move_to, ((amount / CONVERT_BASE)  as u64));
        }
    }

    fun create_event_if_not_exist(addr: address) {
        if(!exists<ContractEvent>(addr)) {
            let signer = create_signer(addr);
            move_to(&signer, ContractEvent {
                log0Event: new_event_handle<Log0Event>(&signer),
                log1Event: new_event_handle<Log1Event>(&signer),
                log2Event: new_event_handle<Log2Event>(&signer),
                log3Event: new_event_handle<Log3Event>(&signer),
                log4Event: new_event_handle<Log4Event>(&signer),
            })
        }
    }

    fun create2_address(sender: vector<u8>, t1: vector<u8>, t2: vector<u8>, fee: u256, hash: vector<u8>): vector<u8> {
        let salt = vector::empty<u8>();
        vector::append(&mut salt, t1);
        vector::append(&mut salt, t2);
        vector::append(&mut salt, u256_to_data(fee));
        debug::print(&salt);
        let p = vector::empty<u8>();
        vector::append(&mut p, x"ff");
        // must be 20 bytes
        vector::append(&mut p, slice(sender, 12, 20));
        vector::append(&mut p, keccak256(salt));
        vector::append(&mut p, hash);
        to_32bit(slice(keccak256(p), 12, 20))
    }

    fun create_account_if_not_exist(addr: address) {
        if(!exists<Account>(addr)) {
            if(!exists_at(addr)) {
                create_account(addr);
            };
            let signer = create_signer(addr);
            coin::register<AptosCoin>(&signer);
            move_to(&signer, Account {
                code: vector::empty(),
                storage: table::new<u256, vector<u8>>(),
                balance: 0,
                is_contract: false,
                nonce: 0
            })
        };
    }

    fun verify_nonce(addr: address, nonce: u64) acquires Account {
        let coin_store_from = borrow_global_mut<Account>(addr);
        assert!(coin_store_from.nonce == nonce, NONCE);
        coin_store_from.nonce = coin_store_from.nonce + 1;
    }

    fun verify_signature(from: vector<u8>, message_hash: vector<u8>, r: vector<u8>, s: vector<u8>, v: u64) {
        let input_bytes = r;
        vector::append(&mut input_bytes, s);
        let signature = ecdsa_signature_from_bytes(input_bytes);
        let recovery_id = if(v > 28) ((v - (CHAIN_ID * 2) - 35) as u8) else ((v - 27) as u8);
        let pk_recover = ecdsa_recover(message_hash, recovery_id, &signature);
        let pk = keccak256(ecdsa_raw_public_key_to_bytes(borrow(&pk_recover)));
        debug::print(&slice(pk, 12, 20));
        assert!(slice(pk, 12, 20) == from, SIGNATURE);
    }

    #[test(aptos_framework = @aptos_framework)]
    fun test_pancake_v3(aptos_framework: signer) acquires Account, ContractEvent {
        // debug::print(&exp(2, 5));
        account::create_account_for_test(@aptos_framework);
        block::initialize_for_test(&aptos_framework, 1);
        // let tokenA = to_32bit(x"4BAbc65A9164Fb63248b40cb04c4Eb57Be3eB901");
        // let tokenB = to_32bit(x"59646Fa0F756b55a77512038a8a2dD1E4FBa2078");
        let sender = to_32bit(x"054ecb78d0276cf182514211d0c21fe46590b654");
        let amount_to_mint = 1000000000000000000000000;
        deposit_to(x"054ecb78d0276cf182514211d0c21fe46590b654", amount_to_mint);


        timestamp::set_time_has_started_for_testing(&aptos_framework);
        let wethBytecode = x"60606040526040805190810160405280600b81526020017f5772617070656420424e420000000000000000000000000000000000000000008152506000908051906020019061004f9291906100c8565b506040805190810160405280600481526020017f57424e42000000000000000000000000000000000000000000000000000000008152506001908051906020019061009b9291906100c8565b506012600260006101000a81548160ff021916908360ff16021790555034156100c357600080fd5b61016d565b828054600181600116156101000203166002900490600052602060002090601f016020900481019282601f1061010957805160ff1916838001178555610137565b82800160010185558215610137579182015b8281111561013657825182559160200191906001019061011b565b5b5090506101449190610148565b5090565b61016a91905b8082111561016657600081600090555060010161014e565b5090565b90565b610c348061017c6000396000f3006060604052600436106100af576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff16806306fdde03146100b9578063095ea7b31461014757806318160ddd146101a157806323b872dd146101ca5780632e1a7d4d14610243578063313ce5671461026657806370a082311461029557806395d89b41146102e2578063a9059cbb14610370578063d0e30db0146103ca578063dd62ed3e146103d4575b6100b7610440565b005b34156100c457600080fd5b6100cc6104dd565b6040518080602001828103825283818151815260200191508051906020019080838360005b8381101561010c5780820151818401526020810190506100f1565b50505050905090810190601f1680156101395780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b341561015257600080fd5b610187600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061057b565b604051808215151515815260200191505060405180910390f35b34156101ac57600080fd5b6101b461066d565b6040518082815260200191505060405180910390f35b34156101d557600080fd5b610229600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061068c565b604051808215151515815260200191505060405180910390f35b341561024e57600080fd5b61026460048080359060200190919050506109d9565b005b341561027157600080fd5b610279610b05565b604051808260ff1660ff16815260200191505060405180910390f35b34156102a057600080fd5b6102cc600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610b18565b6040518082815260200191505060405180910390f35b34156102ed57600080fd5b6102f5610b30565b6040518080602001828103825283818151815260200191508051906020019080838360005b8381101561033557808201518184015260208101905061031a565b50505050905090810190601f1680156103625780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b341561037b57600080fd5b6103b0600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035906020019091905050610bce565b604051808215151515815260200191505060405180910390f35b6103d2610440565b005b34156103df57600080fd5b61042a600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610be3565b6040518082815260200191505060405180910390f35b34600360003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055503373ffffffffffffffffffffffffffffffffffffffff167fe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c346040518082815260200191505060405180910390a2565b60008054600181600116156101000203166002900480601f0160208091040260200160405190810160405280929190818152602001828054600181600116156101000203166002900480156105735780601f1061054857610100808354040283529160200191610573565b820191906000526020600020905b81548152906001019060200180831161055657829003601f168201915b505050505081565b600081600460003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925846040518082815260200191505060405180910390a36001905092915050565b60003073ffffffffffffffffffffffffffffffffffffffff1631905090565b600081600360008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054101515156106dc57600080fd5b3373ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff16141580156107b457507fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600460008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205414155b156108cf5781600460008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020541015151561084457600080fd5b81600460008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055505b81600360008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600360008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055508273ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a3600190509392505050565b80600360003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205410151515610a2757600080fd5b80600360003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055503373ffffffffffffffffffffffffffffffffffffffff166108fc829081150290604051600060405180830381858888f193505050501515610ab457600080fd5b3373ffffffffffffffffffffffffffffffffffffffff167f7fcf532c15f0a6db0bd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65826040518082815260200191505060405180910390a250565b600260009054906101000a900460ff1681565b60036020528060005260406000206000915090505481565b60018054600181600116156101000203166002900480601f016020809104026020016040519081016040528092919081815260200182805460018160011615610100020316600290048015610bc65780601f10610b9b57610100808354040283529160200191610bc6565b820191906000526020600020905b815481529060010190602001808311610ba957829003601f168201915b505050505081565b6000610bdb33848461068c565b905092915050565b60046020528160005260406000206020528060005260406000206000915091505054815600a165627a7a72305820bcf3db16903185450bc04cb54da92f216e96710cce101fd2b4b47d5b70dc11e00029";
        let weth9 = execute(sender, ZERO_ADDR, 0, wethBytecode, 0);
        debug::print(&weth9);
        // let weth9 = to_32bit(x"4BAbc65A9164Fb63248b40cb04c4Eb57Be3eB901");

        create_account_if_not_exist(create_resource_address(&@aptos_framework, sender));

        debug::print(&utf8(b"deployer"));
        let deployer_bytecode = x"608060405234801561001057600080fd5b50615eba806100206000396000f3fe608060405234801561001057600080fd5b506004361061004c5760003560e01c806383c17c55146100515780638903573014610079578063966dae0e146100c3578063fad5359f146100e7575b600080fd5b6100776004803603602081101561006757600080fd5b50356001600160a01b0316610131565b005b6100816101d9565b604080516001600160a01b0396871681529486166020860152929094168383015262ffffff16606083015260029290920b608082015290519081900360a00190f35b6100cb61020f565b604080516001600160a01b039092168252519081900360200190f35b6100cb600480360360a08110156100fd57600080fd5b506001600160a01b03813581169160208101358216916040820135169062ffffff606082013516906080013560020b61021e565b6003546001600160a01b03161561018f576040805162461bcd60e51b815260206004820152601360248201527f616c726561647920696e697469616c697a656400000000000000000000000000604482015290519081900360640190fd5b600380546001600160a01b0319166001600160a01b0383169081179091556040517fb4dd887347efc97a6ad35fc9824a2ac4c0a6a04344d89bf05f3308c854325a6490600090a250565b600054600154600280546001600160a01b03938416939283169281169162ffffff600160a01b83041691600160b81b9004900b85565b6003546001600160a01b031681565b6003546000906001600160a01b03163314610280576040805162461bcd60e51b815260206004820152601c60248201527f6f6e6c7920666163746f72792063616e2063616c6c206465706c6f7900000000604482015290519081900360640190fd5b6040805160a0810182526001600160a01b03888116808352888216602080850182905292891684860181905262ffffff898116606080880182905260028b810b6080998a01819052600080546001600160a01b03199081169099179055600180548916881790558154909716851762ffffff60a01b1916600160a01b84021762ffffff60b81b1916600160b81b97820b909416969096029290921790945586518086019390935282870191909152818101929092528451808203909201825290920192839052815191012090610355906103c4565b8190604051809103906000f5905080158015610375573d6000803e3d6000fd5b50600080546001600160a01b0319908116909155600180549091169055600280547fffffffffffff00000000000000000000000000000000000000000000000000001690559695505050505050565b615adc806103d28339019056fe6101406040523480156200001257600080fd5b506000336001600160a01b031663890357306040518163ffffffff1660e01b815260040160a06040518083038186803b1580156200004f57600080fd5b505afa15801562000064573d6000803e3d6000fd5b505050506040513d60a08110156200007b57600080fd5b50805160208083015160408401516060808601516080968701516001600160e81b031960e892831b1660e0526001600160601b031993831b841660c05293821b831660a05294901b16909352600283810b900b90911b61010052909150620000ee90829062002e4062000106821b17901c565b60801b6001600160801b031916610120525062000174565b60008082600281900b620d89e719816200011c57fe5b05029050600083600281900b620d89e8816200013457fe5b0502905060008460020b83830360020b816200014c57fe5b0560010190508062ffffff166001600160801b038016816200016a57fe5b0495945050505050565b60805160601c60a05160601c60c05160601c60e05160e81c6101005160e81c6101205160801c61589462000248600039806121735280614daf5280614de6525080610cb15280612be95280614e1a5280614e4c525080610da05280611b475280611b7e5280612c315250806113145280611c01528061206852806123f85280612c0d52806140df52508061091452806114425280611bd0528061200252806123725280613f965250806121f6528061221f52806128d552806128fe5280612aa35280612ad05280612af952506158946000f3fe608060405234801561001057600080fd5b50600436106101c45760003560e01c806370cf754a116100f9578063cc7e7fa211610097578063ddca3f4311610071578063ddca3f4314610842578063f305839914610862578063f30dba931461086a578063f637731d146108ec576101c4565b8063cc7e7fa2146107f5578063d0c93a7c1461081b578063d21220a71461083a576101c4565b8063a34123a7116100d3578063a34123a71461072d578063a38807f214610767578063b0d0d211146107c2578063c45a0155146107ed576101c4565b806370cf754a146105e157806385b66729146105e9578063883bdbfd14610626576101c4565b80633c8a7d8d116101665780634f1eb3d8116101405780634f1eb3d81461050f578063514ea4bf146105605780635339c296146105b9578063540d4918146105d9576101c4565b80633c8a7d8d146103cb578063461413191461046b578063490e6cbc14610485576101c4565b80631ad8b03b116101a25780631ad8b03b146102be578063252c09d7146102f557806332148f671461034c5780633850c7bd1461036f576101c4565b80630dfe1681146101c9578063128acb08146101ed5780631a6865021461029a575b600080fd5b6101d1610912565b604080516001600160a01b039092168252519081900360200190f35b610281600480360360a081101561020357600080fd5b6001600160a01b0382358116926020810135151592604082013592606083013516919081019060a081016080820135600160201b81111561024357600080fd5b82018360208201111561025557600080fd5b803590602001918460018302840111600160201b8311171561027657600080fd5b509092509050610936565b6040805192835260208301919091528051918290030190f35b6102a2611633565b604080516001600160801b039092168252519081900360200190f35b6102c6611642565b60405180836001600160801b03168152602001826001600160801b031681526020019250505060405180910390f35b6103126004803603602081101561030b57600080fd5b503561165c565b6040805163ffffffff909516855260069390930b60208501526001600160a01b039091168383015215156060830152519081900360800190f35b61036d6004803603602081101561036257600080fd5b503561ffff166116a1565b005b610377611793565b604080516001600160a01b03909816885260029690960b602088015261ffff9485168787015292841660608701529216608085015263ffffffff90911660a0840152151560c0830152519081900360e00190f35b610281600480360360a08110156103e157600080fd5b6001600160a01b03823516916020810135600290810b92604083013590910b916001600160801b036060820135169181019060a081016080820135600160201b81111561042d57600080fd5b82018360208201111561043f57600080fd5b803590602001918460018302840111600160201b8311171561046057600080fd5b5090925090506117e8565b610473611aa6565b60408051918252519081900360200190f35b61036d6004803603608081101561049b57600080fd5b6001600160a01b038235169160208101359160408201359190810190608081016060820135600160201b8111156104d157600080fd5b8201836020820111156104e357600080fd5b803590602001918460018302840111600160201b8311171561050457600080fd5b509092509050611aac565b6102c6600480360360a081101561052557600080fd5b506001600160a01b03813516906020810135600290810b91604081013590910b906001600160801b0360608201358116916080013516611ef3565b61057d6004803603602081101561057657600080fd5b5035612111565b604080516001600160801b0396871681526020810195909552848101939093529084166060840152909216608082015290519081900360a00190f35b610473600480360360208110156105cf57600080fd5b503560010b61214e565b6101d1612160565b6102a2612171565b6102c6600480360360608110156105ff57600080fd5b506001600160a01b03813516906001600160801b0360208201358116916040013516612195565b6106946004803603602081101561063c57600080fd5b810190602081018135600160201b81111561065657600080fd5b82018360208201111561066857600080fd5b803590602001918460208302840111600160201b8311171561068957600080fd5b509092509050612490565b604051808060200180602001838103835285818151815260200191508051906020019060200280838360005b838110156106d85781810151838201526020016106c0565b50505050905001838103825284818151815260200191508051906020019060200280838360005b838110156107175781810151838201526020016106ff565b5050505090500194505050505060405180910390f35b6102816004803603606081101561074357600080fd5b508035600290810b91602081013590910b90604001356001600160801b0316612515565b6107916004803603604081101561077d57600080fd5b508035600290810b9160200135900b612691565b6040805160069490940b84526001600160a01b03909216602084015263ffffffff1682820152519081900360600190f35b61036d600480360360408110156107d857600080fd5b5063ffffffff81358116916020013516612879565b6101d1612aa1565b61036d6004803603602081101561080b57600080fd5b50356001600160a01b0316612ac5565b610823612be7565b6040805160029290920b8252519081900360200190f35b6101d1612c0b565b61084a612c2f565b6040805162ffffff9092168252519081900360200190f35b610473612c53565b61088a6004803603602081101561088057600080fd5b503560020b612c59565b604080516001600160801b039099168952600f9790970b602089015287870195909552606087019390935260069190910b60808601526001600160a01b031660a085015263ffffffff1660c0840152151560e083015251908190036101000190f35b61036d6004803603602081101561090257600080fd5b50356001600160a01b0316612cc5565b7f000000000000000000000000000000000000000000000000000000000000000081565b60008085610970576040805162461bcd60e51b8152602060048201526002602482015261415360f01b604482015290519081900360640190fd5b6040805160e0810182526000546001600160a01b0381168252600160a01b8104600290810b810b900b602083015261ffff600160b81b8204811693830193909352600160c81b810483166060830152600160d81b9004909116608082015260015463ffffffff811660a083015260ff600160201b90910416151560c08201819052610a28576040805162461bcd60e51b81526020600482015260036024820152624c4f4b60e81b604482015290519081900360640190fd5b87610a735780600001516001600160a01b0316866001600160a01b0316118015610a6e575073fffd8963efd1fc6a506488495d951d5263988d266001600160a01b038716105b610aa5565b80600001516001600160a01b0316866001600160a01b0316108015610aa557506401000276a36001600160a01b038716115b610adc576040805162461bcd60e51b815260206004820152600360248201526214d41360ea1b604482015290519081900360640190fd5b6001805460ff60201b191690556040805160c08101909152600090808a610b115760108460a0015163ffffffff16901c610b1b565b60a084015161ffff165b63ffffffff1681526005546001600160801b03166020820152604001610b3f612eac565b63ffffffff1681526000602082018190526040820181905260609091015262010008549091506001600160a01b031615610be557620100085460408083015181516310a537f160e11b815263ffffffff909116600482015290516001600160a01b039092169163214a6fe29160248082019260009290919082900301818387803b158015610bcc57600080fd5b505af1158015610be0573d6000803e3d6000fd5b505050505b6000808913905060006040518060e001604052808b81526020016000815260200185600001516001600160a01b03168152602001856020015160020b81526020018c610c3357600354610c37565b6002545b815260200160006001600160801b0316815260200184602001516001600160801b031681525090505b805115801590610c865750886001600160a01b031681604001516001600160a01b031614155b156110f557610c93615824565b60408201516001600160a01b031681526060820151610cd6906007907f00000000000000000000000000000000000000000000000000000000000000008f612eb0565b15156040830152600290810b810b60208301819052620d89e719910b1215610d0757620d89e7196020820152610d26565b6020810151620d89e860029190910b1315610d2657620d89e860208201525b610d338160200151612ff2565b6001600160a01b031660608201526040820151610dc4908d610d6d578b6001600160a01b031683606001516001600160a01b031611610d87565b8b6001600160a01b031683606001516001600160a01b0316105b610d95578260600151610d97565b8b5b60c085015185517f0000000000000000000000000000000000000000000000000000000000000000613323565b60c085015260a084015260808301526001600160a01b031660408301528215610e2657610dfa8160c00151826080015101613515565b825103825260a0810151610e1c90610e1190613515565b60208401519061352b565b6020830152610e61565b610e338160a00151613515565b825101825260c08101516080820151610e5b91610e509101613515565b602084015190613547565b60208301525b835163ffffffff1615610ec1576000612710610e94866000015163ffffffff168460c0015161355d90919063ffffffff16565b81610e9b57fe5b60c0840180519290910491829003905260a0840180519091016001600160801b03169052505b60c08201516001600160801b031615610f0057610ef48160c00151600160801b8460c001516001600160801b0316613581565b60808301805190910190525b80606001516001600160a01b031682604001516001600160a01b031614156110b45780604001511561108b578360a00151610f8a57610f68846040015160008760200151886040015188602001518a606001516009613631909695949392919063ffffffff16565b6001600160a01b03166080860152600690810b900b6060850152600160a08501525b62010008546001600160a01b03161561101557620100085460208201516040805163a498463360e01b815260029290920b60048301528e15156024830152516001600160a01b039092169163a49846339160448082019260009290919082900301818387803b158015610ffc57600080fd5b505af1158015611010573d6000803e3d6000fd5b505050505b600061106182602001518e61102c57600254611032565b84608001515b8f611041578560800151611045565b6003545b608089015160608a015160408b015160069594939291906137c3565b90508c1561106d576000035b61107b8360c0015182613881565b6001600160801b031660c0840152505b8b61109a5780602001516110a3565b60018160200151035b600290810b900b60608301526110ef565b80600001516001600160a01b031682604001516001600160a01b0316146110ef576110e28260400151613937565b600290810b900b60608301525b50610c60565b836020015160020b816060015160020b146111c35760008061114386604001518660400151886020015188602001518a606001518b608001516009613c5f909695949392919063ffffffff16565b604085015160608601516000805461ffff60c81b1916600160c81b61ffff958616021761ffff60b81b1916600160b81b95909416949094029290921762ffffff60a01b1916600160a01b62ffffff60029490940b9390931692909202919091176001600160a01b0319166001600160a01b03909116179055506111e89050565b6040810151600080546001600160a01b0319166001600160a01b039092169190911790555b8060c001516001600160801b031683602001516001600160801b03161461122e5760c0810151600580546001600160801b0319166001600160801b039092169190911790555b6000808c1561128857608083015160025560a08301516001600160801b03161561127c5760a0830151600480546001600160801b031981166001600160801b03918216909301169190911790555b8260a0015191506112d5565b608083015160035560a08301516001600160801b0316156112ce5760a0830151600480546001600160801b03808216600160801b92839004821690940116029190911790555b5060a08201515b8315158d1515146112ee57602083015183518d036112fb565b82600001518c0383602001515b90985096508c1561143457600087121561133d5761133d7f00000000000000000000000000000000000000000000000000000000000000008f89600003613dfa565b6000611347613f48565b9050336001600160a01b03166323a69e758a8a8e8e6040518563ffffffff1660e01b815260040180858152602001848152602001806020018281038252848482818152602001925080828437600081840152601f19601f82011690508083019250505095505050505050600060405180830381600087803b1580156113cb57600080fd5b505af11580156113df573d6000803e3d6000fd5b505050506113eb613f48565b6113f5828b614081565b111561142e576040805162461bcd60e51b815260206004820152600360248201526249494160e81b604482015290519081900360640190fd5b5061155e565b600088121561146b5761146b7f00000000000000000000000000000000000000000000000000000000000000008f8a600003613dfa565b6000611475614091565b9050336001600160a01b03166323a69e758a8a8e8e6040518563ffffffff1660e01b815260040180858152602001848152602001806020018281038252848482818152602001925080828437600081840152601f19601f82011690508083019250505095505050505050600060405180830381600087803b1580156114f957600080fd5b505af115801561150d573d6000803e3d6000fd5b50505050611519614091565b611523828a614081565b111561155c576040805162461bcd60e51b815260206004820152600360248201526249494160e81b604482015290519081900360640190fd5b505b8d6001600160a01b0316336001600160a01b03167f19b47279256b2a23a1665c810c8d55a1758940ee09377d4f8d26497a3577dc838a8a87604001518860c001518960600151898960405180888152602001878152602001866001600160a01b03168152602001856001600160801b031681526020018460020b8152602001836001600160801b03168152602001826001600160801b0316815260200197505050505050505060405180910390a350506001805460ff60201b1916600160201b17905550939a92995091975050505050505050565b6005546001600160801b031681565b6004546001600160801b0380821691600160801b90041682565b60098161ffff811061166d57600080fd5b015463ffffffff81169150600160201b810460060b90600160581b81046001600160a01b031690600160f81b900460ff1684565b600154600160201b900460ff166116e5576040805162461bcd60e51b81526020600482015260036024820152624c4f4b60e81b604482015290519081900360640190fd5b6001805460ff60201b1916905560008054600160d81b900461ffff169061170e60098385614129565b6000805461ffff808416600160d81b810261ffff60d81b199093169290921790925591925083161461177b576040805161ffff80851682528316602082015281517fac49e518f90a358f652e4400164f05a5d8f7e35e7747279bc3a93dbf584e125a929181900390910190a15b50506001805460ff60201b1916600160201b17905550565b6000546001546001600160a01b03821691600160a01b810460020b9161ffff600160b81b8304811692600160c81b8104821692600160d81b9091049091169063ffffffff81169060ff600160201b9091041687565b6001546000908190600160201b900460ff16611831576040805162461bcd60e51b81526020600482015260036024820152624c4f4b60e81b604482015290519081900360640190fd5b6001805460ff60201b191690556001600160801b03851661185157600080fd5b60008061189f60405180608001604052808c6001600160a01b031681526020018b60020b81526020018a60020b81526020016118958a6001600160801b03166141cc565b600f0b90526141dd565b925092505081935080925060008060008611156118c1576118be613f48565b91505b84156118d2576118cf614091565b90505b336001600160a01b03166399eee9d087878b8b6040518563ffffffff1660e01b815260040180858152602001848152602001806020018281038252848482818152602001925080828437600081840152601f19601f82011690508083019250505095505050505050600060405180830381600087803b15801561195457600080fd5b505af1158015611968573d6000803e3d6000fd5b5050505060008611156119bf5761197d613f48565b6119878388614081565b11156119bf576040805162461bcd60e51b815260206004820152600260248201526104d360f41b604482015290519081900360640190fd5b8415611a0f576119cd614091565b6119d78287614081565b1115611a0f576040805162461bcd60e51b81526020600482015260026024820152614d3160f01b604482015290519081900360640190fd5b8960020b8b60020b8d6001600160a01b03167f7a53080ba414158be7ec69b987b5fb7d07dee101fe85488f0853ae16239d0bde338d8b8b60405180856001600160a01b03168152602001846001600160801b0316815260200183815260200182815260200194505050505060405180910390a450506001805460ff60201b1916600160201b17905550919890975095505050505050565b60035481565b600154600160201b900460ff16611af0576040805162461bcd60e51b81526020600482015260036024820152624c4f4b60e81b604482015290519081900360640190fd5b6001805460ff60201b191690556005546001600160801b031680611b3f576040805162461bcd60e51b81526020600482015260016024820152601360fa1b604482015290519081900360640190fd5b6000611b74867f000000000000000000000000000000000000000000000000000000000000000062ffffff16620f4240614413565b90506000611bab867f000000000000000000000000000000000000000000000000000000000000000062ffffff16620f4240614413565b90506000611bb7613f48565b90506000611bc3614091565b90508815611bf657611bf67f00000000000000000000000000000000000000000000000000000000000000008b8b613dfa565b8715611c2757611c277f00000000000000000000000000000000000000000000000000000000000000008b8a613dfa565b336001600160a01b031663a1d4833685858a8a6040518563ffffffff1660e01b815260040180858152602001848152602001806020018281038252848482818152602001925080828437600081840152601f19601f82011690508083019250505095505050505050600060405180830381600087803b158015611ca957600080fd5b505af1158015611cbd573d6000803e3d6000fd5b505050506000611ccb613f48565b90506000611cd7614091565b905081611ce48588614081565b1115611d1c576040805162461bcd60e51b8152602060048201526002602482015261046360f41b604482015290519081900360640190fd5b80611d278487614081565b1115611d5f576040805162461bcd60e51b8152602060048201526002602482015261463160f01b604482015290519081900360640190fd5b8382038382038115611de85760015461ffff1660008115611d8c5761271063ffffffff8316850204611d8f565b60005b90506001600160801b03811615611dc257600480546001600160801b038082168401166001600160801b03199091161790555b611ddc818503600160801b8d6001600160801b0316613581565b60028054909101905550505b8015611e6d5760015460101c61ffff1660008115611e125761271063ffffffff8316840204611e15565b60005b90506001600160801b03811615611e4757600480546001600160801b03600160801b8083048216850182160291161790555b611e61818403600160801b8d6001600160801b0316613581565b60038054909101905550505b8d6001600160a01b0316336001600160a01b03167fbdbdb71d7860376ba52b25a5028beea23581364a40522f6bcfb86bb1f2dca6338f8f86866040518085815260200184815260200183815260200182815260200194505050505060405180910390a350506001805460ff60201b1916600160201b179055505050505050505050505050565b6001546000908190600160201b900460ff16611f3c576040805162461bcd60e51b81526020600482015260036024820152624c4f4b60e81b604482015290519081900360640190fd5b6001805460ff60201b191690556000611f58600833898961444d565b60038101549091506001600160801b0390811690861611611f795784611f88565b60038101546001600160801b03165b60038201549093506001600160801b03600160801b909104811690851611611fb05783611fc6565b6003810154600160801b90046001600160801b03165b91506001600160801b0383161561202b576003810180546001600160801b031981166001600160801b0391821686900382161790915561202b907f0000000000000000000000000000000000000000000000000000000000000000908a908616613dfa565b6001600160801b03821615612091576003810180546001600160801b03600160801b808304821686900382160291811691909117909155612091907f0000000000000000000000000000000000000000000000000000000000000000908a908516613dfa565b604080516001600160a01b038a1681526001600160801b0380861660208301528416818301529051600288810b92908a900b9133917f70935338e69775456a85ddef226c395fb668b63fa0115f5f20610b388e6ca9c0919081900360600190a4506001805460ff60201b1916600160201b17905590969095509350505050565b60086020526000908152604090208054600182015460028301546003909301546001600160801b0392831693919281811691600160801b90041685565b60076020526000908152604090205481565b62010008546001600160a01b031681565b7f000000000000000000000000000000000000000000000000000000000000000081565b6001546000908190600160201b900460ff166121de576040805162461bcd60e51b81526020600482015260036024820152624c4f4b60e81b604482015290519081900360640190fd5b6001805460ff60201b19169055336001600160a01b037f00000000000000000000000000000000000000000000000000000000000000001614806122ae57507f00000000000000000000000000000000000000000000000000000000000000006001600160a01b0316638da5cb5b6040518163ffffffff1660e01b815260040160206040518083038186803b15801561227657600080fd5b505afa15801561228a573d6000803e3d6000fd5b505050506040513d60208110156122a057600080fd5b50516001600160a01b031633145b6122b757600080fd5b6004546001600160801b03908116908516116122d357836122e0565b6004546001600160801b03165b6004549092506001600160801b03600160801b909104811690841611612306578261231a565b600454600160801b90046001600160801b03165b90506001600160801b0382161561239b576004546001600160801b038381169116141561234957600019909101905b600480546001600160801b031981166001600160801b0391821685900382161790915561239b907f00000000000000000000000000000000000000000000000000000000000000009087908516613dfa565b6001600160801b03811615612421576004546001600160801b03828116600160801b9092041614156123cc57600019015b600480546001600160801b03600160801b808304821685900382160291811691909117909155612421907f00000000000000000000000000000000000000000000000000000000000000009087908416613dfa565b604080516001600160801b0380851682528316602082015281516001600160a01b0388169233927f596b573906218d3411850b26a6b437d6c4522fdb43d2d2386263f86d50b8b151929081900390910190a36001805460ff60201b1916600160201b1790559094909350915050565b60608061250a61249e612eac565b858580806020026020016040519081016040528093929190818152602001838360200280828437600092018290525054600554600996959450600160a01b820460020b935061ffff600160b81b8304811693506001600160801b0390911691600160c81b9004166144b1565b915091509250929050565b6001546000908190600160201b900460ff1661255e576040805162461bcd60e51b81526020600482015260036024820152624c4f4b60e81b604482015290519081900360640190fd5b6001805460ff60201b1916905560408051608081018252338152600287810b602083015286900b91810191909152600090819081906125ba90606081016125ad6001600160801b038a166141cc565b600003600f0b90526141dd565b92509250925081600003945080600003935060008511806125db5750600084115b1561261a576003830180546001600160801b038082168089018216600160801b93849004831689019092169092029091176001600160801b0319161790555b604080516001600160801b0388168152602081018790528082018690529051600289810b92908b900b9133917f0c396cd989a39f4459b5fa1aed6a9a8dcdbc45908acfd67e028cd568da98982c919081900360600190a450506001805460ff60201b1916600160201b179055509094909350915050565b60008060006126a0858561460b565b600285810b810b600090815260066020819052604080832088850b90940b8352822060038401549182900b93600160381b83046001600160a01b0316928492600160d81b820463ffffffff16928492909190600160f81b900460ff168061270657600080fd5b6003820154600681900b9850600160381b81046001600160a01b03169650600160d81b810463ffffffff169450600160f81b900460ff168061274757600080fd5b50506040805160e0810182526000546001600160a01b0381168252600160a01b8104600290810b810b810b6020840181905261ffff600160b81b8404811695850195909552600160c81b830485166060850152600160d81b909204909316608083015260015463ffffffff811660a084015260ff600160201b90910416151560c08301529093508e820b910b121590506127ef57509390940396509003935090039050612872565b8a60020b816020015160020b121561286357600061280b612eac565b6020830151604084015160055460608601519394506000938493612841936009938893879392916001600160801b031690613631565b9a9003989098039b505094909603929092039650909103039250612872915050565b50949093039650039350900390505b9250925092565b600154600160201b900460ff166128bd576040805162461bcd60e51b81526020600482015260036024820152624c4f4b60e81b604482015290519081900360640190fd5b6001805460ff60201b19169055336001600160a01b037f000000000000000000000000000000000000000000000000000000000000000016148061298d57507f00000000000000000000000000000000000000000000000000000000000000006001600160a01b0316638da5cb5b6040518163ffffffff1660e01b815260040160206040518083038186803b15801561295557600080fd5b505afa158015612969573d6000803e3d6000fd5b505050506040513d602081101561297f57600080fd5b50516001600160a01b031633145b61299657600080fd5b63ffffffff821615806129c457506103e88263ffffffff16101580156129c457506113888263ffffffff1611155b80156129f9575063ffffffff811615806129f957506103e88163ffffffff16101580156129f957506113888163ffffffff1611155b612a0257600080fd5b6001805465ffffffff0000601084901b16840163ffffffff90811663ffffffff19831617909255167fb3159fed3ddfba67bae294599eafe2d0ec98c08bb38e0e5fb87d33154b6e05aa62010000826040805163ffffffff939092068316825261ffff601086901c16602083015286831682820152918516606082015290519081900360800190a150506001805460ff60201b1916600160201b17905550565b7f000000000000000000000000000000000000000000000000000000000000000081565b336001600160a01b037f0000000000000000000000000000000000000000000000000000000000000000161480612b8857507f00000000000000000000000000000000000000000000000000000000000000006001600160a01b0316638da5cb5b6040518163ffffffff1660e01b815260040160206040518083038186803b158015612b5057600080fd5b505afa158015612b64573d6000803e3d6000fd5b505050506040513d6020811015612b7a57600080fd5b50516001600160a01b031633145b612b9157600080fd5b6201000880546001600160a01b0383166001600160a01b0319909116811790915560408051918252517f29983690a85a11696ce8a357993744f8d5a74fde14653e517cc2f8608a7235e99181900360200190a150565b7f000000000000000000000000000000000000000000000000000000000000000081565b7f000000000000000000000000000000000000000000000000000000000000000081565b7f000000000000000000000000000000000000000000000000000000000000000081565b60025481565b60066020819052600091825260409091208054600182015460028301546003909301546001600160801b03831694600160801b909304600f0b93919281900b90600160381b81046001600160a01b031690600160d81b810463ffffffff1690600160f81b900460ff1688565b6000546001600160a01b031615612d08576040805162461bcd60e51b8152602060048201526002602482015261414960f01b604482015290519081900360640190fd5b6000612d1382613937565b9050600080612d2b612d23612eac565b6009906146d4565b6040805160e0810182526001600160a01b038816808252600288810b6020808501829052600085870181905261ffff8981166060880181905290891660808801819052631388138860a08901819052600160c090990189905283546001600160a01b031916881762ffffff60a01b1916600160a01b62ffffff9888900b98909816979097029690961763ffffffff60b81b1916600160c81b9092029190911761ffff60d81b1916600160d81b9091021790558454600160201b63ffffffff1990911690931760ff60201b191692909217909355835191825281019190915281519395509193507f98636036cb66a9c19a37435efc1e90142190214e8abeb821bdba3f2990dd4c9592918290030190a150505050565b60008082600281900b620d89e71981612e5557fe5b05029050600083600281900b620d89e881612e6c57fe5b0502905060008460020b83830360020b81612e8357fe5b0560010190508062ffffff166001600160801b03801681612ea057fe5b0493505050505b919050565b4290565b60008060008460020b8660020b81612ec457fe5b05905060008660020b128015612eeb57508460020b8660020b81612ee457fe5b0760020b15155b15612ef557600019015b8315612f6a57600080612f0783614720565b600182810b810b600090815260208d9052604090205460ff83169190911b80016000190190811680151597509294509092509085612f4c57888360ff16860302612f5f565b88612f5682614732565b840360ff168603025b965050505050612fe8565b600080612f7983600101614720565b91509150600060018260ff166001901b031990506000818b60008660010b60010b8152602001908152602001600020541690508060001415955085612fcb57888360ff0360ff16866001010102612fe1565b8883612fd6836147d1565b0360ff168660010101025b9650505050505b5094509492505050565b60008060008360020b12613009578260020b613011565b8260020b6000035b9050620d89e881111561304f576040805162461bcd60e51b81526020600482015260016024820152601560fa1b604482015290519081900360640190fd5b60006001821661306357600160801b613075565b6ffffcb933bd6fad37aa2d162d1a5940015b70ffffffffffffffffffffffffffffffffff16905060028216156130a9576ffff97272373d413259a46990580e213a0260801c5b60048216156130c8576ffff2e50f5f656932ef12357cf3c7fdcc0260801c5b60088216156130e7576fffe5caca7e10e4e61c3624eaa0941cd00260801c5b6010821615613106576fffcb9843d60f6159c9db58835c9266440260801c5b6020821615613125576fff973b41fa98c081472e6896dfb254c00260801c5b6040821615613144576fff2ea16466c96a3843ec78b326b528610260801c5b6080821615613163576ffe5dee046a99a2a811c461f1969c30530260801c5b610100821615613183576ffcbe86c7900a88aedcffc83b479aa3a40260801c5b6102008216156131a3576ff987a7253ac413176f2b074cf7815e540260801c5b6104008216156131c3576ff3392b0822b70005940c7a398e4b70f30260801c5b6108008216156131e3576fe7159475a2c29b7443b29c7fa6e889d90260801c5b611000821615613203576fd097f3bdfd2022b8845ad8f792aa58250260801c5b612000821615613223576fa9f746462d870fdf8a65dc1f90e061e50260801c5b614000821615613243576f70d869a156d2a1b890bb3df62baf32f70260801c5b618000821615613263576f31be135f97d08fd981231505542fcfa60260801c5b62010000821615613284576f09aa508b5b7a84e1c677de54f3e99bc90260801c5b620200008216156132a4576e5d6af8dedb81196699c329225ee6040260801c5b620400008216156132c3576d2216e584f5fa1ea926041bedfe980260801c5b620800008216156132e0576b048a170391f7dc42444e8fa20260801c5b60008460020b13156132fb5780600019816132f757fe5b0490505b600160201b81061561330e576001613311565b60005b60ff16602082901c0192505050919050565b60008080806001600160a01b03808916908a1610158187128015906133a857600061335c8989620f42400362ffffff16620f4240613581565b905082613375576133708c8c8c60016148bb565b613382565b6133828b8d8c6001614936565b9550858110613393578a96506133a2565b61339f8c8b83866149ea565b96505b506133f2565b816133bf576133ba8b8b8b6000614936565b6133cc565b6133cc8a8c8b60006148bb565b93508388600003106133e0578995506133f2565b6133ef8b8a8a60000385614a36565b95505b6001600160a01b038a8116908716148215613455578080156134115750815b61342757613422878d8c6001614936565b613429565b855b9550808015613436575081155b61344c57613447878d8c60006148bb565b61344e565b845b945061349f565b80801561345f5750815b613475576134708c888c60016148bb565b613477565b855b9550808015613484575081155b61349a576134958c888c6000614936565b61349c565b845b94505b811580156134af57508860000385115b156134bb578860000394505b8180156134da57508a6001600160a01b0316876001600160a01b031614155b156134e9578589039350613506565b613503868962ffffff168a620f42400362ffffff16614413565b93505b50505095509550955095915050565b6000600160ff1b821061352757600080fd5b5090565b8082038281131560008312151461354157600080fd5b92915050565b8181018281121560008312151461354157600080fd5b60008215806135785750508181028183828161357557fe5b04145b61354157600080fd5b60008080600019858709868602925082811090839003039050806135b757600084116135ac57600080fd5b50829004905061362a565b8084116135c357600080fd5b6000848688096000868103871696879004966002600389028118808a02820302808a02820302808a02820302808a02820302808a02820302808a02909103029181900381900460010186841190950394909402919094039290920491909117919091029150505b9392505050565b60008063ffffffff87166136d7576000898661ffff1661ffff811061365257fe5b60408051608081018252919092015463ffffffff808216808452600160201b8304600690810b810b900b6020850152600160581b83046001600160a01b031694840194909452600160f81b90910460ff16151560608301529092508a16146136c3576136c0818a8988614a82565b90505b8060200151816040015192509250506137b7565b8688036000806136ec8c8c858c8c8c8c614b25565b91509150816000015163ffffffff168363ffffffff16141561371e5781602001518260400151945094505050506137b7565b805163ffffffff848116911614156137465780602001518160400151945094505050506137b7565b8151815160208085015190840151918390039286039163ffffffff80841692908516910360060b8161377457fe5b05028460200151018263ffffffff168263ffffffff1686604001518660400151036001600160a01b031602816137a657fe5b048560400151019650965050505050505b97509795505050505050565b600295860b860b60009081526020979097526040909620600181018054909503909455938301805490920390915560038201805463ffffffff600160d81b6001600160a01b03600160381b808504821690960316909402670100000000000000600160d81b031990921691909117600681810b90960390950b66ffffffffffffff1666ffffffffffffff199095169490941782810485169095039093160263ffffffff60d81b1990931692909217905554600160801b9004600f0b90565b60008082600f0b12156138e657826001600160801b03168260000384039150816001600160801b0316106138e1576040805162461bcd60e51b81526020600482015260026024820152614c5360f01b604482015290519081900360640190fd5b613541565b826001600160801b03168284019150816001600160801b03161015613541576040805162461bcd60e51b81526020600482015260026024820152614c4160f01b604482015290519081900360640190fd5b60006401000276a36001600160a01b03831610801590613973575073fffd8963efd1fc6a506488495d951d5263988d266001600160a01b038316105b6139a8576040805162461bcd60e51b81526020600482015260016024820152602960f91b604482015290519081900360640190fd5b77ffffffffffffffffffffffffffffffffffffffff00000000602083901b166001600160801b03811160071b81811c67ffffffffffffffff811160061b90811c63ffffffff811160051b90811c61ffff811160041b90811c60ff8111600390811b91821c600f811160021b90811c918211600190811b92831c97908811961790941790921717909117171760808110613a4957607f810383901c9150613a53565b80607f0383901b91505b908002607f81811c60ff83811c9190911c800280831c81831c1c800280841c81841c1c800280851c81851c1c800280861c81861c1c800280871c81871c1c800280881c81881c1c800280891c81891c1c8002808a1c818a1c1c8002808b1c818b1c1c8002808c1c818c1c1c8002808d1c818d1c1c8002808e1c9c81901c9c909c1c80029c8d901c9e9d607f198f0160401b60c09190911c678000000000000000161760c19b909b1c674000000000000000169a909a1760c29990991c672000000000000000169890981760c39790971c671000000000000000169690961760c49590951c670800000000000000169490941760c59390931c670400000000000000169290921760c69190911c670200000000000000161760c79190911c600160381b161760c89190911c6680000000000000161760c99190911c6640000000000000161760ca9190911c6620000000000000161760cb9190911c6610000000000000161760cc9190911c6608000000000000161760cd9190911c66040000000000001617693627a301d71055774c8581026f028f6481ab7f045a5af012a19d003aa9198101608090811d906fdb2df09e81959a81455e260799a0632f8301901d600281810b9083900b14613c5057886001600160a01b0316613c3482612ff2565b6001600160a01b03161115613c495781613c4b565b805b613c52565b815b9998505050505050505050565b6000806000898961ffff1661ffff8110613c7557fe5b60408051608081018252919092015463ffffffff808216808452600160201b8304600690810b810b900b6020850152600160581b83046001600160a01b031694840194909452600160f81b90910460ff161515606083015290925089161415613ce457888592509250506137b7565b8461ffff168461ffff16118015613d0557506001850361ffff168961ffff16145b15613d1257839150613d16565b8491505b8161ffff168960010161ffff1681613d2a57fe5b069250613d3981898989614a82565b8a8461ffff1661ffff8110613d4a57fe5b825191018054602084015160408501516060909501511515600160f81b026001600160f81b036001600160a01b03909616600160581b027fff0000000000000000000000000000000000000000ffffffffffffffffffffff60069390930b66ffffffffffffff16600160201b026affffffffffffff000000001963ffffffff90971663ffffffff199095169490941795909516929092171692909217929092161790555097509795505050505050565b604080516001600160a01b038481166024830152604480830185905283518084039091018152606490920183526020820180516001600160e01b031663a9059cbb60e01b1781529251825160009485949389169392918291908083835b60208310613e765780518252601f199092019160209182019101613e57565b6001836020036101000a0380198251168184511680821785525050505050509050019150506000604051808303816000865af19150503d8060008114613ed8576040519150601f19603f3d011682016040523d82523d6000602084013e613edd565b606091505b5091509150818015613f0b575080511580613f0b5750808060200190516020811015613f0857600080fd5b50515b613f41576040805162461bcd60e51b81526020600482015260026024820152612a2360f11b604482015290519081900360640190fd5b5050505050565b604080513060248083019190915282518083039091018152604490910182526020810180516001600160e01b03166370a0823160e01b17815291518151600093849384936001600160a01b037f00000000000000000000000000000000000000000000000000000000000000001693919290918291908083835b60208310613fe15780518252601f199092019160209182019101613fc2565b6001836020036101000a038019825116818451168082178552505050505050905001915050600060405180830381855afa9150503d8060008114614041576040519150601f19603f3d011682016040523d82523d6000602084013e614046565b606091505b509150915081801561405a57506020815110155b61406357600080fd5b80806020019051602081101561407857600080fd5b50519250505090565b8082018281101561354157600080fd5b604080513060248083019190915282518083039091018152604490910182526020810180516001600160e01b03166370a0823160e01b17815291518151600093849384936001600160a01b037f000000000000000000000000000000000000000000000000000000000000000016939192909182919080838360208310613fe15780518252601f199092019160209182019101613fc2565b6000808361ffff1611614167576040805162461bcd60e51b81526020600482015260016024820152604960f81b604482015290519081900360640190fd5b8261ffff168261ffff161161417d57508161362a565b825b8261ffff168161ffff1610156141c3576001858261ffff1661ffff81106141a257fe5b01805463ffffffff191663ffffffff9290921691909117905560010161417f565b50909392505050565b80600f81900b8114612ea757600080fd5b60008060006141f48460200151856040015161460b565b6040805160e0810182526000546001600160a01b0381168252600160a01b8104600290810b810b900b602080840182905261ffff600160b81b8404811685870152600160c81b84048116606080870191909152600160d81b90940416608085015260015463ffffffff811660a086015260ff600160201b90910416151560c0850152885190890151948901519289015193946142969491939092909190614d1f565b93508460600151600f0b60001461440b57846020015160020b816020015160020b12156142eb576142e46142cd8660200151612ff2565b6142da8760400151612ff2565b8760600151614ed4565b925061440b565b846040015160020b816020015160020b12156143e15760055460408201516001600160801b039091169061433d90614321612eac565b6020850151606086015160808701516009949392918791613c5f565b6000805461ffff60c81b1916600160c81b61ffff938416021761ffff60b81b1916600160b81b93909216929092021790558151604087015161438d919061438390612ff2565b8860600151614ed4565b93506143ab61439f8760200151612ff2565b83516060890151614f18565b92506143bb818760600151613881565b600580546001600160801b0319166001600160801b03929092169190911790555061440b565b6144086143f18660200151612ff2565b6143fe8760400151612ff2565b8760600151614f18565b91505b509193909250565b6000614420848484613581565b90506000828061442c57fe5b848609111561362a57600019811061444357600080fd5b6001019392505050565b6040805160609490941b6bffffffffffffffffffffffff1916602080860191909152600293840b60e890811b60348701529290930b90911b60378401528051808403601a018152603a90930181528251928201929092206000908152929052902090565b60608060008361ffff16116144f1576040805162461bcd60e51b81526020600482015260016024820152604960f81b604482015290519081900360640190fd5b865167ffffffffffffffff8111801561450957600080fd5b50604051908082528060200260200182016040528015614533578160200160208202803683370190505b509150865167ffffffffffffffff8111801561454e57600080fd5b50604051908082528060200260200182016040528015614578578160200160208202803683370190505b50905060005b87518110156145fe576145a98a8a8a848151811061459857fe5b60200260200101518a8a8a8a613631565b8483815181106145b557fe5b602002602001018484815181106145c857fe5b60200260200101826001600160a01b03166001600160a01b03168152508260060b60060b8152505050808060010191505061457e565b5097509795505050505050565b8060020b8260020b1261464b576040805162461bcd60e51b8152602060048201526003602482015262544c5560e81b604482015290519081900360640190fd5b620d89e719600283900b121561468e576040805162461bcd60e51b8152602060048201526003602482015262544c4d60e81b604482015290519081900360640190fd5b620d89e8600282900b13156146d0576040805162461bcd60e51b815260206004820152600360248201526254554d60e81b604482015290519081900360640190fd5b5050565b6040805160808101825263ffffffff9283168082526000602083018190529282019290925260016060909101819052835463ffffffff1916909117909116600160f81b17909155908190565b60020b600881901d9161010090910790565b600080821161474057600080fd5b600160801b821061475357608091821c91015b68010000000000000000821061476b57604091821c91015b600160201b821061477e57602091821c91015b62010000821061479057601091821c91015b61010082106147a157600891821c91015b601082106147b157600491821c91015b600482106147c157600291821c91015b60028210612ea757600101919050565b60008082116147df57600080fd5b5060ff6001600160801b038216156147fa57607f1901614802565b608082901c91505b67ffffffffffffffff82161561481b57603f1901614823565b604082901c91505b63ffffffff82161561483857601f1901614840565b602082901c91505b61ffff82161561485357600f190161485b565b601082901c91505b60ff82161561486d5760071901614875565b600882901c91505b600f821615614887576003190161488f565b600482901c91505b60038216156148a157600119016148a9565b600282901c91505b6001821615612ea75760001901919050565b6000836001600160a01b0316856001600160a01b031611156148db579293925b8161490857614903836001600160801b03168686036001600160a01b0316600160601b613581565b61492b565b61492b836001600160801b03168686036001600160a01b0316600160601b614413565b90505b949350505050565b6000836001600160a01b0316856001600160a01b03161115614956579293925b6fffffffffffffffffffffffffffffffff60601b606084901b166001600160a01b03868603811690871661498957600080fd5b836149b957866001600160a01b03166149ac8383896001600160a01b0316613581565b816149b357fe5b046149df565b6149df6149d08383896001600160a01b0316614413565b886001600160a01b0316614f47565b979650505050505050565b600080856001600160a01b031611614a0157600080fd5b6000846001600160801b031611614a1757600080fd5b81614a29576149038585856001614f52565b61492b8585856001615033565b600080856001600160a01b031611614a4d57600080fd5b6000846001600160801b031611614a6357600080fd5b81614a75576149038585856000615033565b61492b8585856000614f52565b614a8a615860565b600085600001518503905060405180608001604052808663ffffffff1681526020018263ffffffff168660020b0288602001510160060b81526020016000856001600160801b031611614ade576001614ae0565b845b6001600160801b031663ffffffff60801b608085901b1681614afe57fe5b048860400151016001600160a01b0316815260200160011515815250915050949350505050565b614b2d615860565b614b35615860565b888561ffff1661ffff8110614b4657fe5b60408051608081018252919092015463ffffffff8116808352600160201b8204600690810b810b900b6020840152600160581b82046001600160a01b031693830193909352600160f81b900460ff16151560608201529250614baa9089908961511f565b15614be2578663ffffffff16826000015163ffffffff161415614bcc576137b7565b81614bd983898988614a82565b915091506137b7565b888361ffff168660010161ffff1681614bf757fe5b0661ffff1661ffff8110614c0757fe5b60408051608081018252929091015463ffffffff81168352600160201b8104600690810b810b900b60208401526001600160a01b03600160581b8204169183019190915260ff600160f81b90910416151560608201819052909250614cbc57604080516080810182528a5463ffffffff81168252600160201b8104600690810b810b900b6020830152600160581b81046001600160a01b031692820192909252600160f81b90910460ff161515606082015291505b614ccb8883600001518961511f565b614d02576040805162461bcd60e51b815260206004820152600360248201526213d31160ea1b604482015290519081900360640190fd5b614d0f89898988876151e0565b9150915097509795505050505050565b6000614d2e600887878761444d565b60025460035491925090600080600f87900b15614e74576000614d4f612eac565b6000805460055492935090918291614d999160099186918591600160a01b810460020b9161ffff600160b81b83048116926001600160801b0390921691600160c81b900416613631565b9092509050614dd360068d8b8d8b8b87898b60007f000000000000000000000000000000000000000000000000000000000000000061537e565b9450614e0a60068c8b8d8b8b87898b60017f000000000000000000000000000000000000000000000000000000000000000061537e565b93508415614e3e57614e3e60078d7f000000000000000000000000000000000000000000000000000000000000000061553b565b8315614e7057614e7060078c7f000000000000000000000000000000000000000000000000000000000000000061553b565b5050505b600080614e8660068c8c8b8a8a6155a1565b9092509050614e97878a848461564d565b600089600f0b1215614ec5578315614eb457614eb460068c6157e2565b8215614ec557614ec560068b6157e2565b50505050505095945050505050565b60008082600f0b12614efa57614ef5614ef08585856001614936565b613515565b61492e565b614f0d614ef08585856000036000614936565b600003949350505050565b60008082600f0b12614f3457614ef5614ef085858560016148bb565b614f0d614ef085858560000360006148bb565b808204910615150190565b60008115614fc55760006001600160a01b03841115614f8857614f8384600160601b876001600160801b0316613581565b614fa0565b6001600160801b038516606085901b81614f9e57fe5b045b9050614fbd614fb86001600160a01b03881683614081565b61580e565b91505061492e565b60006001600160a01b03841115614ff357614fee84600160601b876001600160801b0316614413565b61500a565b61500a606085901b6001600160801b038716614f47565b905080866001600160a01b03161161502157600080fd5b6001600160a01b03861603905061492e565b60008261504157508361492e565b6fffffffffffffffffffffffffffffffff60601b606085901b1682156150d8576001600160a01b0386168481029085828161507857fe5b0414156150a9578181018281106150a75761509d83896001600160a01b031683614413565b935050505061492e565b505b6150cf826150ca878a6001600160a01b031686816150c357fe5b0490614081565b614f47565b9250505061492e565b6001600160a01b038616848102908582816150ef57fe5b041480156150fc57508082115b61510557600080fd5b80820361509d614fb8846001600160a01b038b1684614413565b60008363ffffffff168363ffffffff161115801561514957508363ffffffff168263ffffffff1611155b15615165578163ffffffff168363ffffffff161115905061362a565b60008463ffffffff168463ffffffff161161518c578363ffffffff16600160201b01615194565b8363ffffffff165b64ffffffffff16905060008563ffffffff168463ffffffff16116151c4578363ffffffff16600160201b016151cc565b8363ffffffff165b64ffffffffff169091111595945050505050565b6151e8615860565b6151f0615860565b60008361ffff168560010161ffff168161520657fe5b0661ffff169050600060018561ffff16830103905060005b506002818301048961ffff8716828161523357fe5b0661ffff811061523f57fe5b60408051608081018252929091015463ffffffff81168352600160201b8104600690810b810b900b60208401526001600160a01b03600160581b8204169183019190915260ff600160f81b909104161515606082018190529095506152a95780600101925061521e565b898661ffff1682600101816152ba57fe5b0661ffff81106152c657fe5b60408051608081018252929091015463ffffffff81168352600160201b8104600690810b810b900b60208401526001600160a01b03600160581b8204169183019190915260ff600160f81b90910416151560608201528551909450600090615330908b908b61511f565b905080801561534957506153498a8a876000015161511f565b156153545750615371565b806153645760018203925061536b565b8160010193505b5061521e565b5050509550959350505050565b60028a810b900b600090815260208c90526040812080546001600160801b0316826153a9828d613881565b9050846001600160801b0316816001600160801b031611156153f7576040805162461bcd60e51b81526020600482015260026024820152614c4f60f01b604482015290519081900360640190fd5b6001600160801b0382811615908216158114159450156154a0578c60020b8e60020b1361548857600183018b9055600283018a9055600383018054670100000000000000600160d81b031916600160381b6001600160a01b038c16021766ffffffffffffff191666ffffffffffffff60068b900b161763ffffffff60d81b1916600160d81b63ffffffff8a16021790555b6003830180546001600160f81b0316600160f81b1790555b82546001600160801b0319166001600160801b038216178355856154e95782546154e4906154df90600160801b9004600f90810b810b908f900b613547565b6141cc565b61550a565b825461550a906154df90600160801b9004600f90810b810b908f900b61352b565b8354600f9190910b6001600160801b03908116600160801b0291161790925550909c9b505050505050505050505050565b8060020b8260020b8161554a57fe5b0760020b1561555857600080fd5b6000806155738360020b8560020b8161556d57fe5b05614720565b600191820b820b60009081526020979097526040909620805460ff9097169190911b90951890945550505050565b600285810b80820b60009081526020899052604080822088850b850b83529082209193849391929184918291908a900b126155e7575050600182015460028301546155fa565b8360010154880391508360020154870390505b6000808b60020b8b60020b121561561c5750506001830154600284015461562f565b84600101548a0391508460020154890390505b92909803979097039b96909503949094039850939650505050505050565b6040805160a08101825285546001600160801b0390811682526001870154602083015260028701549282019290925260038601548083166060830152600160801b900490911660808201526000600f85900b6156ec5781516001600160801b03166156e4576040805162461bcd60e51b815260206004820152600260248201526104e560f41b604482015290519081900360640190fd5b5080516156fb565b81516156f89086613881565b90505b600061571f8360200151860384600001516001600160801b0316600160801b613581565b905060006157458460400151860385600001516001600160801b0316600160801b613581565b905086600f0b60001461576c5787546001600160801b0319166001600160801b0384161788555b60018801869055600288018590556001600160801b03821615158061579a57506000816001600160801b0316115b156157d8576003880180546001600160801b031981166001600160801b039182168501821617808216600160801b9182900483168501909216021790555b5050505050505050565b600290810b810b6000908152602092909252604082208281556001810183905590810182905560030155565b806001600160a01b0381168114612ea757600080fd5b6040805160e081018252600080825260208201819052918101829052606081018290526080810182905260a0810182905260c081019190915290565b6040805160808101825260008082526020820181905291810182905260608101919091529056fea164736f6c6343000706000aa164736f6c6343000706000a";
        let deployer = execute(sender, ZERO_ADDR, 1, deployer_bytecode, 0);
        debug::print(&deployer);

        debug::print(&utf8(b"factory"));
        let factory_bytecode = &mut x"60a060405234801561001057600080fd5b506040516118753803806118758339818101604052602081101561003357600080fd5b50516001600160601b0319606082901b16608052600080546001600160a01b0319163390811782556040519091907fb532073b38c83145e3e5135377a08bf9aab55bc0fd7c1179cd4fb995d2a5159c908290a37f1bd07f61ef326b4de236f5b68f225f46ff76ee2c375ae31a06da201c49c70c12805462ffffff19166001908117909155604080518082018252600080825260208281018581526064808452600390925292517f6b16ef514f22b74729cbea5cc7babfecbdc2309e530ca716643d11fe929eed2e8054945115156101000261ff001992151560ff199096169590951791909116939093179092559151909160008051602061183583398151915291a36040805160008152600160208201528151606492600080516020611855833981519152928290030190a27fdf8fbcd2e8050ff10755b1defc84e6a72827884928f329fe5f5d4c92e9ca46de805462ffffff1916601e9081179091556040805180820182526000808252600160208381019182526105dc808452600390915292517fcbce329e1ffee4c2c9ce52003b225dac0c58969e1e40a84d4c3bb56386ac298a8054925115156101000261ff001992151560ff1990941693909317919091169190911790559151909160008051602061183583398151915291a360408051600081526001602082015281516105dc92600080516020611855833981519152928290030190a27f8bf1273959200f3b11670b7338c174c40286607d4b851c000be7fc007987b275805462ffffff1916603c908117909155604080518082018252600080825260016020838101918252610bb8808452600390915292517fa81df8da5a49e0ca2395b3c1eb4d55b23a04eb0615a8bee310459ef8a1c6e29c8054925115156101000261ff001992151560ff1990941693909317919091169190911790559151909160008051602061183583398151915291a36040805160008152600160208201528151610bb892600080516020611855833981519152928290030190a27f1ca239af1d44623dfaa87ee0cbbbe4bbeb2112df36e66deedafd694350d045cd805462ffffff191660c8908117909155604080518082018252600080825260016020838101918252612710808452600390915292517fbed90d45c8c5fb2e8fcae0027c6e57da3d943cdb82d794c1080bce28e166f2118054925115156101000261ff001992151560ff1990941693909317919091169190911790559151909160008051602061183583398151915291a3604080516000815260016020820152815161271092600080516020611855833981519152928290030190a25060805160601c61141f610416600039806106f352806110db525061141f6000f3fe608060405234801561001057600080fd5b50600436106100f55760003560e01c80637e8435e6116100975780638da5cb5b116100665780638da5cb5b146103a55780638ff38e80146103ad578063a1671295146103df578063e4a86a9914610428576100f5565b80637e8435e6146102c357806380d6a7921461030a57806388e8006d1461033d5780638a7c195f1461037a576100f5565b806322afcccb116100d357806322afcccb146101dc5780633119049a1461021557806343db87da1461021d5780635e492ac8146102bb576100f5565b806311ff5e8d146100fa57806313af4035146101375780631698ee821461016a575b600080fd5b6101356004803603604081101561011057600080fd5b5073ffffffffffffffffffffffffffffffffffffffff81358116916020013516610463565b005b6101356004803603602081101561014d57600080fd5b503573ffffffffffffffffffffffffffffffffffffffff16610590565b6101b36004803603606081101561018057600080fd5b50803573ffffffffffffffffffffffffffffffffffffffff908116916020810135909116906040013562ffffff166106a3565b6040805173ffffffffffffffffffffffffffffffffffffffff9092168252519081900360200190f35b6101fe600480360360208110156101f257600080fd5b503562ffffff166106dc565b6040805160029290920b8252519081900360200190f35b6101b36106f1565b61027a6004803603608081101561023357600080fd5b5073ffffffffffffffffffffffffffffffffffffffff81358116916020810135909116906fffffffffffffffffffffffffffffffff60408201358116916060013516610715565b60405180836fffffffffffffffffffffffffffffffff168152602001826fffffffffffffffffffffffffffffffff1681526020019250505060405180910390f35b6101b361086b565b610135600480360360608110156102d957600080fd5b5073ffffffffffffffffffffffffffffffffffffffff8135169063ffffffff60208201358116916040013516610887565b6101356004803603602081101561032057600080fd5b503573ffffffffffffffffffffffffffffffffffffffff166109a5565b61035f6004803603602081101561035357600080fd5b503562ffffff16610a9a565b60408051921515835290151560208301528051918290030190f35b6101356004803603604081101561039057600080fd5b5062ffffff813516906020013560020b610ab8565b6101b3610cc3565b610135600480360360608110156103c357600080fd5b5062ffffff813516906020810135151590604001351515610cdf565b6101b3600480360360608110156103f557600080fd5b50803573ffffffffffffffffffffffffffffffffffffffff908116916020810135909116906040013562ffffff16610e50565b6101356004803603604081101561043e57600080fd5b5073ffffffffffffffffffffffffffffffffffffffff81351690602001351515611234565b60005473ffffffffffffffffffffffffffffffffffffffff163314806104a0575060055473ffffffffffffffffffffffffffffffffffffffff1633145b61050b57604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601d60248201527f4e6f74206f776e6572206f72204c4d20706f6f6c206465706c6f796572000000604482015290519081900360640190fd5b8173ffffffffffffffffffffffffffffffffffffffff1663cc7e7fa2826040518263ffffffff1660e01b8152600401808273ffffffffffffffffffffffffffffffffffffffff168152602001915050600060405180830381600087803b15801561057457600080fd5b505af1158015610588573d6000803e3d6000fd5b505050505050565b60005473ffffffffffffffffffffffffffffffffffffffff16331461061657604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600960248201527f4e6f74206f776e65720000000000000000000000000000000000000000000000604482015290519081900360640190fd5b6000805460405173ffffffffffffffffffffffffffffffffffffffff808516939216917fb532073b38c83145e3e5135377a08bf9aab55bc0fd7c1179cd4fb995d2a5159c91a3600080547fffffffffffffffffffffffff00000000000000000000000000000000000000001673ffffffffffffffffffffffffffffffffffffffff92909216919091179055565b600260209081526000938452604080852082529284528284209052825290205473ffffffffffffffffffffffffffffffffffffffff1681565b60016020526000908152604090205460020b81565b7f000000000000000000000000000000000000000000000000000000000000000081565b60008054819073ffffffffffffffffffffffffffffffffffffffff16331461079e57604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600960248201527f4e6f74206f776e65720000000000000000000000000000000000000000000000604482015290519081900360640190fd5b604080517f85b6672900000000000000000000000000000000000000000000000000000000815273ffffffffffffffffffffffffffffffffffffffff87811660048301526fffffffffffffffffffffffffffffffff8088166024840152861660448301528251908916926385b6672992606480820193918290030181600087803b15801561082b57600080fd5b505af115801561083f573d6000803e3d6000fd5b505050506040513d604081101561085557600080fd5b5080516020909101519097909650945050505050565b60055473ffffffffffffffffffffffffffffffffffffffff1681565b60005473ffffffffffffffffffffffffffffffffffffffff16331461090d57604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600960248201527f4e6f74206f776e65720000000000000000000000000000000000000000000000604482015290519081900360640190fd5b604080517fb0d0d21100000000000000000000000000000000000000000000000000000000815263ffffffff808516600483015283166024820152905173ffffffffffffffffffffffffffffffffffffffff85169163b0d0d21191604480830192600092919082900301818387803b15801561098857600080fd5b505af115801561099c573d6000803e3d6000fd5b50505050505050565b60005473ffffffffffffffffffffffffffffffffffffffff163314610a2b57604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600960248201527f4e6f74206f776e65720000000000000000000000000000000000000000000000604482015290519081900360640190fd5b600580547fffffffffffffffffffffffff00000000000000000000000000000000000000001673ffffffffffffffffffffffffffffffffffffffff83169081179091556040517f4c912280cda47bed324de14f601d3f125a98254671772f3f1f491e50fa0ca40790600090a250565b60036020526000908152604090205460ff8082169161010090041682565b60005473ffffffffffffffffffffffffffffffffffffffff163314610b3e57604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600960248201527f4e6f74206f776e65720000000000000000000000000000000000000000000000604482015290519081900360640190fd5b620f42408262ffffff1610610b5257600080fd5b60008160020b138015610b6957506140008160020b125b610b7257600080fd5b62ffffff8216600090815260016020526040902054600290810b900b15610b9857600080fd5b62ffffff828116600081815260016020818152604080842080547fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000016600289900b9788161790558051808201825284815280830193845285855260039092528084209151825493517fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00909416901515177fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff1661010093151593909302929092179055517fc66a3fdf07232cdd185febcc6579d408c241b47ae2f9907d84be655141eeaecc9190a3604080516000815260016020820152815162ffffff8516927fed85b616dbfbc54d0f1180a7bd0f6e3bb645b269b234e7a9edcc269ef1443d88928290030190a25050565b60005473ffffffffffffffffffffffffffffffffffffffff1681565b60005473ffffffffffffffffffffffffffffffffffffffff163314610d6557604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600960248201527f4e6f74206f776e65720000000000000000000000000000000000000000000000604482015290519081900360640190fd5b62ffffff8316600090815260016020526040902054600290810b900b610d8a57600080fd5b604080518082018252831515808252831515602080840182815262ffffff89166000818152600384528790209551865492511515610100027fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff9115157fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff009094169390931716919091179094558451928352820152825191927fed85b616dbfbc54d0f1180a7bd0f6e3bb645b269b234e7a9edcc269ef1443d8892918290030190a2505050565b60008273ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff161415610e8b57600080fd5b6000808473ffffffffffffffffffffffffffffffffffffffff168673ffffffffffffffffffffffffffffffffffffffff1610610ec8578486610ecb565b85855b909250905073ffffffffffffffffffffffffffffffffffffffff8216610ef057600080fd5b62ffffff8416600090815260016020908152604080832054600383529281902081518083019092525460ff8082161515835261010090910416151591810191909152600291820b9182900b15801590610f4a575080602001515b610fb557604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601860248201527f666565206973206e6f7420617661696c61626c65207965740000000000000000604482015290519081900360640190fd5b805115611024573360009081526004602052604090205460ff16611024576040517f08c379a00000000000000000000000000000000000000000000000000000000081526004018080602001828103825260328152602001806113e16032913960400191505060405180910390fd5b73ffffffffffffffffffffffffffffffffffffffff84811660009081526002602090815260408083208785168452825280832062ffffff8b168452909152902054161561107057600080fd5b604080517ffad5359f00000000000000000000000000000000000000000000000000000000815230600482015273ffffffffffffffffffffffffffffffffffffffff8681166024830152858116604483015262ffffff89166064830152600285900b608483015291517f00000000000000000000000000000000000000000000000000000000000000009092169163fad5359f9160a4808201926020929091908290030181600087803b15801561112657600080fd5b505af115801561113a573d6000803e3d6000fd5b505050506040513d602081101561115057600080fd5b505173ffffffffffffffffffffffffffffffffffffffff80861660008181526002602081815260408084208a871680865290835281852062ffffff8f168087529084528286208054988a167fffffffffffffffffffffffff0000000000000000000000000000000000000000998a1681179091558287528585528387208888528552838720828852855295839020805490981686179097558151938a900b8452918301939093528251959a5093947f783cca1c0412dd0d695e784568c96da2e9c22ff989357a2e8b1d9b2b4e6b7118929181900390910190a4505050509392505050565b60005473ffffffffffffffffffffffffffffffffffffffff1633146112ba57604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600960248201527f4e6f74206f776e65720000000000000000000000000000000000000000000000604482015290519081900360640190fd5b73ffffffffffffffffffffffffffffffffffffffff821660009081526004602052604090205460ff161515811515141561135557604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601060248201527f7374617465206e6f74206368616e676500000000000000000000000000000000604482015290519081900360640190fd5b73ffffffffffffffffffffffffffffffffffffffff821660008181526004602090815260409182902080547fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0016851515908117909155825190815291517faec42ac7f1bb8651906ae6522f50a19429e124e8ea678ef59fd27750759288a29281900390910190a2505056fe757365722073686f756c6420626520696e20746865207768697465206c69737420666f722074686973206665652074696572a164736f6c6343000706000ac66a3fdf07232cdd185febcc6579d408c241b47ae2f9907d84be655141eeaecced85b616dbfbc54d0f1180a7bd0f6e3bb645b269b234e7a9edcc269ef1443d88";
        vector::append(factory_bytecode, deployer);
        let factory = execute(sender, ZERO_ADDR, 2, *factory_bytecode, 0);
        debug::print(&factory);

        debug::print(&utf8(b"set factory"));
        let set_factory_data = &mut x"83c17c55";
        vector::append(set_factory_data, factory);
        execute(sender, deployer, 3, *set_factory_data, 0);

        debug::print(&utf8(b"manager"));
        let manager_bytecode = &mut x"610140604052600d80546001600160b01b0319166001176001600160b01b0316600160b01b1790553480156200003457600080fd5b5060405162006366380380620063668339810160408190526200005791620002e6565b8383836040518060400160405280601981526020017f5741525020563320506f736974696f6e7320574152502d5631000000000000008152506040518060400160405280600b81526020016a574152502d56332d504f5360a81b815250604051806040016040528060018152602001603160f81b8152508282620000e86301ffc9a760e01b6200019860201b60201c565b8151620000fd9060069060208501906200021d565b508051620001139060079060208401906200021d565b50620001266380ac58cd60e01b62000198565b62000138635b5e139f60e01b62000198565b6200014a63780e9d6360e01b62000198565b50508251602093840120608052805192019190912060a052506001600160601b0319606093841b811660c05291831b821660e052821b81166101005291901b16610120525062000342915050565b6001600160e01b03198082161415620001f8576040805162461bcd60e51b815260206004820152601c60248201527f4552433136353a20696e76616c696420696e7465726661636520696400000000604482015290519081900360640190fd5b6001600160e01b0319166000908152602081905260409020805460ff19166001179055565b828054600181600116156101000203166002900490600052602060002090601f016020900481019282620002555760008555620002a0565b82601f106200027057805160ff1916838001178555620002a0565b82800160010185558215620002a0579182015b82811115620002a057825182559160200191906001019062000283565b50620002ae929150620002b2565b5090565b5b80821115620002ae5760008155600101620002b3565b80516001600160a01b0381168114620002e157600080fd5b919050565b60008060008060808587031215620002fc578384fd5b6200030785620002c9565b93506200031760208601620002c9565b92506200032760408601620002c9565b91506200033760608601620002c9565b905092959194509250565b60805160a05160c05160601c60e05160601c6101005160601c6101205160601c615f92620003d460003980612b315250806102b45280611748528061183e52806118c65280613e5f5280613ea55280613f19525080610e0e5280610ed55280612acb525080610ad752806124165280612bbe5280612e98528061373552508061152f52508061150e5250615f926000f3fe6080604052600436106102a45760003560e01c80636352211e1161016e578063ac9650d8116100cb578063d5f394881161007f578063e985e9c511610064578063e985e9c514610725578063f3995c6714610745578063fc6f78651461075857610328565b8063d5f39488146106fd578063df2ab5bb1461071257610328565b8063c2e3140a116100b0578063c2e3140a146106b5578063c45a0155146106c8578063c87b56dd146106dd57610328565b8063ac9650d814610675578063b88d4fde1461069557610328565b806395d89b411161012257806399fbab881161010757806399fbab881461060a578063a22cb46514610642578063a4a78f0c1461066257610328565b806395d89b41146105d557806399eee9d0146105ea57610328565b806370a082311161015357806370a082311461057f5780637ac2ff7b1461059f57806388316456146105b257610328565b80636352211e1461054a5780636c0360eb1461056a57610328565b806323b872dd1161021c57806342966c68116101d057806349404b7c116101b557806349404b7c146105025780634aa4a4fc146105155780634f6ccce71461052a57610328565b806342966c68146104dc5780634659a494146104ef57610328565b806330adf81f1161020157806330adf81f146104925780633644e515146104a757806342842e0e146104bc57610328565b806323b872dd146104525780632f745c591461047257610328565b80630c49ccbe1161027357806313ead5621161025857806313ead562146103fb57806318160ddd1461040e578063219f5d171461043057610328565b80630c49ccbe146103d257806312210e8a146103f357610328565b806301ffc9a71461032d57806306fdde0314610363578063081812fc14610385578063095ea7b3146103b257610328565b3661032857336001600160a01b037f00000000000000000000000000000000000000000000000000000000000000001614610326576040805162461bcd60e51b815260206004820152600960248201527f4e6f742057455448390000000000000000000000000000000000000000000000604482015290519081900360640190fd5b005b600080fd5b34801561033957600080fd5b5061034d6103483660046153ff565b61076b565b60405161035a919061597f565b60405180910390f35b34801561036f57600080fd5b506103786107a6565b60405161035a91906159d2565b34801561039157600080fd5b506103a56103a0366004615719565b61083c565b60405161035a9190615843565b3480156103be57600080fd5b506103266103cd3660046152c4565b610898565b6103e56103e03660046154dc565b61096e565b60405161035a929190615ba3565b610326610dda565b6103a5610409366004615157565b610dec565b34801561041a57600080fd5b506104236110f9565b60405161035a919061598a565b61044361043e3660046154ed565b61110a565b60405161035a93929190615b5e565b34801561045e57600080fd5b5061032661046d3660046151b0565b611443565b34801561047e57600080fd5b5061042361048d3660046152c4565b61149a565b34801561049e57600080fd5b506104236114c5565b3480156104b357600080fd5b506104236114e9565b3480156104c857600080fd5b506103266104d73660046151b0565b6115a7565b6103266104ea366004615719565b6115c2565b6103266104fd366004615330565b611691565b610326610510366004615731565b611744565b34801561052157600080fd5b506103a56118c4565b34801561053657600080fd5b50610423610545366004615719565b6118e8565b34801561055657600080fd5b506103a5610565366004615719565b6118fe565b34801561057657600080fd5b50610378611926565b34801561058b57600080fd5b5061042361059a366004615103565b61192b565b6103266105ad366004615330565b611993565b6105c56105c03660046155a9565b611e3f565b60405161035a9493929190615b7f565b3480156105e157600080fd5b506103786123a0565b3480156105f657600080fd5b50610326610605366004615778565b612401565b34801561061657600080fd5b5061062a610625366004615719565b61247f565b60405161035a9c9b9a99989796959493929190615bb1565b34801561064e57600080fd5b5061032661065d366004615297565b6126ae565b610326610670366004615330565b6127d1565b610688610683366004615390565b612883565b60405161035a9190615901565b3480156106a157600080fd5b506103266106b03660046151f0565b6129c3565b6103266106c3366004615330565b612a21565b3480156106d457600080fd5b506103a5612ac9565b3480156106e957600080fd5b506103786106f8366004615719565b612aed565b34801561070957600080fd5b506103a5612bbc565b6103266107203660046152ef565b612be0565b34801561073157600080fd5b5061034d61074036600461511f565b612cc3565b610326610753366004615330565b612cf1565b6103e56107663660046154c5565b612d7c565b7fffffffff00000000000000000000000000000000000000000000000000000000811660009081526020819052604090205460ff165b919050565b60068054604080516020601f60026000196101006001881615020190951694909404938401819004810282018101909252828152606093909290918301828280156108325780601f1061080757610100808354040283529160200191610832565b820191906000526020600020905b81548152906001019060200180831161081557829003601f168201915b5050505050905090565b60006108478261329a565b61086c5760405162461bcd60e51b815260040161086390615a1c565b60405180910390fd5b506000908152600c60205260409020546c0100000000000000000000000090046001600160a01b031690565b60006108a3826118fe565b9050806001600160a01b0316836001600160a01b031614156108f65760405162461bcd60e51b8152600401808060200182810382526021815260200180615f346021913960400191505060405180910390fd5b806001600160a01b03166109086132a7565b6001600160a01b031614806109245750610924816107406132a7565b61095f5760405162461bcd60e51b8152600401808060200182810382526038815260200180615e5e6038913960400191505060405180910390fd5b61096983836132ab565b505050565b600080823561097d338261332f565b6109995760405162461bcd60e51b8152600401610863906159e5565b8360800135806109a76133cb565b11156109fa576040805162461bcd60e51b815260206004820152601360248201527f5472616e73616374696f6e20746f6f206f6c6400000000000000000000000000604482015290519081900360640190fd5b6000610a0c60408701602088016155bb565b6001600160801b031611610a1f57600080fd5b84356000908152600c602090815260409182902060018101549092600160801b9091046001600160801b031691610a5a9189019089016155bb565b6001600160801b0316816001600160801b03161015610a7857600080fd5b60018281015469ffffffffffffffffffff166000908152600b60209081526040808320815160608101835281546001600160a01b039081168252919095015490811692850192909252600160a01b90910462ffffff1690830152610afc7f0000000000000000000000000000000000000000000000000000000000000000836133cf565b60018501549091506001600160a01b0382169063a34123a7906a01000000000000000000008104600290810b91600160681b9004900b610b4260408e0160208f016155bb565b6040518463ffffffff1660e01b8152600401610b60939291906159ac565b6040805180830381600087803b158015610b7957600080fd5b505af1158015610b8d573d6000803e3d6000fd5b505050506040513d601f19601f82011682018060405250810190610bb19190615755565b909850965060408901358810801590610bce575088606001358710155b610bea5760405162461bcd60e51b815260040161086390615a79565b6001840154600090610c1a9030906a01000000000000000000008104600290810b91600160681b9004900b6134cb565b9050600080836001600160a01b031663514ea4bf846040518263ffffffff1660e01b8152600401610c4b919061598a565b60a06040518083038186803b158015610c6357600080fd5b505afa158015610c77573d6000803e3d6000fd5b505050506040513d601f19601f82011682018060405250810190610c9b9190615605565b50509250925050610cc087600201548303876001600160801b0316600160801b613525565b6004880180546fffffffffffffffffffffffffffffffff198116928e016001600160801b039182160181169290921790556003880154610d0a91908303908816600160801b613525565b6004880180546001600160801b03808216938e01600160801b9283900482160116029190911790556002870182905560038701819055610d5060408d0160208e016155bb565b86038760010160106101000a8154816001600160801b0302191690836001600160801b031602179055508b600001357f26f6a048ee9138f2c0ce266f322cb99228e8d619ae2bff30c67f8dcf9d2377b48d6020016020810190610db391906155bb565b8d8d604051610dc493929190615b5e565b60405180910390a2505050505050505050915091565b4715610dea57610dea33476135d4565b565b6000836001600160a01b0316856001600160a01b031610610e0c57600080fd5b7f00000000000000000000000000000000000000000000000000000000000000006001600160a01b0316631698ee828686866040518463ffffffff1660e01b815260040180846001600160a01b03168152602001836001600160a01b031681526020018262ffffff168152602001935050505060206040518083038186803b158015610e9757600080fd5b505afa158015610eab573d6000803e3d6000fd5b505050506040513d6020811015610ec157600080fd5b505190506001600160a01b038116611010577f00000000000000000000000000000000000000000000000000000000000000006001600160a01b031663a16712958686866040518463ffffffff1660e01b815260040180846001600160a01b03168152602001836001600160a01b031681526020018262ffffff1681526020019350505050602060405180830381600087803b158015610f6057600080fd5b505af1158015610f74573d6000803e3d6000fd5b505050506040513d6020811015610f8a57600080fd5b5051604080517ff637731d0000000000000000000000000000000000000000000000000000000081526001600160a01b03858116600483015291519293509083169163f637731d9160248082019260009290919082900301818387803b158015610ff357600080fd5b505af1158015611007573d6000803e3d6000fd5b505050506110f1565b6000816001600160a01b0316633850c7bd6040518163ffffffff1660e01b815260040160e06040518083038186803b15801561104b57600080fd5b505afa15801561105f573d6000803e3d6000fd5b505050506040513d60e081101561107557600080fd5b505190506001600160a01b0381166110ef57816001600160a01b031663f637731d846040518263ffffffff1660e01b815260040180826001600160a01b03168152602001915050600060405180830381600087803b1580156110d657600080fd5b505af11580156110ea573d6000803e3d6000fd5b505050505b505b949350505050565b600061110560026136dd565b905090565b60008060008360a001358061111d6133cb565b1115611170576040805162461bcd60e51b815260206004820152601360248201527f5472616e73616374696f6e20746f6f206f6c6400000000000000000000000000604482015290519081900360640190fd5b84356000908152600c6020908152604080832060018082015469ffffffffffffffffffff81168652600b855283862084516060808201875282546001600160a01b039081168352929094015480831682890190815262ffffff600160a01b9092048216838901908152885161014081018a528451861681529151909416818a01529251168287015230828501526a01000000000000000000008304600290810b810b608080850191909152600160681b909404810b900b60a0830152958c013560c0820152938b013560e0850152908a0135610100840152890135610120830152929061125c906136e8565b6001870154939a50919850965091506000906112969030906a01000000000000000000008104600290810b91600160681b9004900b6134cb565b9050600080836001600160a01b031663514ea4bf846040518263ffffffff1660e01b81526004016112c7919061598a565b60a06040518083038186803b1580156112df57600080fd5b505afa1580156112f3573d6000803e3d6000fd5b505050506040513d601f19601f820116820180604052508101906113179190615605565b50509250925050611353866002015483038760010160109054906101000a90046001600160801b03166001600160801b0316600160801b613525565b6004870180546001600160801b0380821690930183166fffffffffffffffffffffffffffffffff19909116179055600387015460018801546113a39291840391600160801b918290041690613525565b6004870180546001600160801b03600160801b80830482169094018116840291811691909117909155600288018490556003880183905560018801805483810483168e018316909302929091169190911790556040518b35907f3067048beee31b25b2f1681f88dac838c8bba36af25bfb2b7cf7473a5847e35f9061142d908d908d908d90615b5e565b60405180910390a2505050505050509193909250565b61145461144e6132a7565b8261332f565b61148f5760405162461bcd60e51b8152600401808060200182810382526031815260200180615f556031913960400191505060405180910390fd5b610969838383613923565b6001600160a01b03821660009081526001602052604081206114bc9083613a6f565b90505b92915050565b7f49ecf333e5b8c95c40fdafc95c1ad136e8914a8fb55e9dc8bb01eaa83a2df9ad81565b60007f8b73c3c69bb8fe3d512ecc4cf759cc79239f7b179b0ffacaa9a75d522b39400f7f00000000000000000000000000000000000000000000000000000000000000007f0000000000000000000000000000000000000000000000000000000000000000611556613a7b565b3060405160200180868152602001858152602001848152602001838152602001826001600160a01b031681526020019550505050505060405160208183030381529060405280519060200120905090565b610969838383604051806020016040528060008152506129c3565b806115cd338261332f565b6115e95760405162461bcd60e51b8152600401610863906159e5565b6000828152600c602052604090206001810154600160801b90046001600160801b0316158015611624575060048101546001600160801b0316155b801561164257506004810154600160801b90046001600160801b0316155b61165e5760405162461bcd60e51b815260040161086390615ae7565b6000838152600c602052604081208181556001810182905560028101829055600381018290556004015561096983613a7f565b604080517f8fcbaf0c00000000000000000000000000000000000000000000000000000000815233600482015230602482015260448101879052606481018690526001608482015260ff851660a482015260c4810184905260e4810183905290516001600160a01b03881691638fcbaf0c9161010480830192600092919082900301818387803b15801561172457600080fd5b505af1158015611738573d6000803e3d6000fd5b50505050505050505050565b60007f00000000000000000000000000000000000000000000000000000000000000006001600160a01b03166370a08231306040518263ffffffff1660e01b815260040180826001600160a01b0316815260200191505060206040518083038186803b1580156117b357600080fd5b505afa1580156117c7573d6000803e3d6000fd5b505050506040513d60208110156117dd57600080fd5b5051905082811015611836576040805162461bcd60e51b815260206004820152601260248201527f496e73756666696369656e742057455448390000000000000000000000000000604482015290519081900360640190fd5b8015610969577f00000000000000000000000000000000000000000000000000000000000000006001600160a01b0316632e1a7d4d826040518263ffffffff1660e01b815260040180828152602001915050600060405180830381600087803b1580156118a257600080fd5b505af11580156118b6573d6000803e3d6000fd5b5050505061096982826135d4565b7f000000000000000000000000000000000000000000000000000000000000000081565b6000806118f6600284613b4c565b509392505050565b60006114bf82604051806060016040528060298152602001615ec06029913960029190613b6a565b606090565b60006001600160a01b0382166119725760405162461bcd60e51b815260040180806020018281038252602a815260200180615e96602a913960400191505060405180910390fd5b6001600160a01b03821660009081526001602052604090206114bf906136dd565b8361199c6133cb565b11156119ef576040805162461bcd60e51b815260206004820152600e60248201527f5065726d69742065787069726564000000000000000000000000000000000000604482015290519081900360640190fd5b60006119f96114e9565b7f49ecf333e5b8c95c40fdafc95c1ad136e8914a8fb55e9dc8bb01eaa83a2df9ad8888611a2581613b77565b604080516020808201969096526001600160a01b03909416848201526060840192909252608083015260a08083018a90528151808403909101815260c0830182528051908401207f190100000000000000000000000000000000000000000000000000000000000060e084015260e283019490945261010280830194909452805180830390940184526101229091019052815191012090506000611ac8876118fe565b9050806001600160a01b0316886001600160a01b03161415611b1b5760405162461bcd60e51b8152600401808060200182810382526027815260200180615dc16027913960400191505060405180910390fd5b611b2481613bb6565b15611cff576040805160208082018790528183018690527fff0000000000000000000000000000000000000000000000000000000000000060f889901b16606083015282516041818403018152606183018085527f1626ba7e0000000000000000000000000000000000000000000000000000000090526065830186815260858401948552815160a585015281516001600160a01b03871695631626ba7e958995919260c59091019185019080838360005b83811015611bee578181015183820152602001611bd6565b50505050905090810190601f168015611c1b5780820380516001836020036101000a031916815260200191505b50935050505060206040518083038186803b158015611c3957600080fd5b505afa158015611c4d573d6000803e3d6000fd5b505050506040513d6020811015611c6357600080fd5b50517fffffffff00000000000000000000000000000000000000000000000000000000167f1626ba7e0000000000000000000000000000000000000000000000000000000014611cfa576040805162461bcd60e51b815260206004820152600c60248201527f556e617574686f72697a65640000000000000000000000000000000000000000604482015290519081900360640190fd5b611e2b565b600060018387878760405160008152602001604052604051808581526020018460ff1681526020018381526020018281526020019450505050506020604051602081039080840390855afa158015611d5b573d6000803e3d6000fd5b5050604051601f1901519150506001600160a01b038116611dc3576040805162461bcd60e51b815260206004820152601160248201527f496e76616c6964207369676e6174757265000000000000000000000000000000604482015290519081900360640190fd5b816001600160a01b0316816001600160a01b031614611e29576040805162461bcd60e51b815260206004820152600c60248201527f556e617574686f72697a65640000000000000000000000000000000000000000604482015290519081900360640190fd5b505b611e3588886132ab565b5050505050505050565b60008060008084610140013580611e546133cb565b1115611ea7576040805162461bcd60e51b815260206004820152601360248201527f5472616e73616374696f6e20746f6f206f6c6400000000000000000000000000604482015290519081900360640190fd5b604080516101408101909152600090611f739080611ec860208b018b615103565b6001600160a01b03168152602001896020016020810190611ee99190615103565b6001600160a01b03168152602001611f0760608b0160408c016156ff565b62ffffff168152306020820152604001611f2760808b0160608c0161543f565b60020b8152602001611f3f60a08b0160808c0161543f565b60020b81526020018960a0013581526020018960c0013581526020018960e0013581526020018961010001358152506136e8565b92975090955093509050611fe7611f9261014089016101208a01615103565b600d80547fffffffffffffffffffff000000000000000000000000000000000000000000008116600175ffffffffffffffffffffffffffffffffffffffffffff92831690810190921617909155975087613bbc565b600061201230611ffd60808b0160608c0161543f565b61200d60a08c0160808d0161543f565b6134cb565b9050600080836001600160a01b031663514ea4bf846040518263ffffffff1660e01b8152600401612043919061598a565b60a06040518083038186803b15801561205b57600080fd5b505afa15801561206f573d6000803e3d6000fd5b505050506040513d601f19601f820116820180604052508101906120939190615605565b50509250925050600061210c8560405180606001604052808e60000160208101906120be9190615103565b6001600160a01b031681526020018e60200160208101906120df9190615103565b6001600160a01b031681526020018e604001602081019061210091906156ff565b62ffffff169052613cea565b905060405180610140016040528060006bffffffffffffffffffffffff16815260200160006001600160a01b031681526020018269ffffffffffffffffffff1681526020018c6060016020810190612164919061543f565b60020b815260200161217c60a08e0160808f0161543f565b60020b81526020018a6001600160801b0316815260200184815260200183815260200160006001600160801b0316815260200160006001600160801b0316815250600c60008c815260200190815260200160002060008201518160000160006101000a8154816bffffffffffffffffffffffff02191690836bffffffffffffffffffffffff160217905550602082015181600001600c6101000a8154816001600160a01b0302191690836001600160a01b0316021790555060408201518160010160006101000a81548169ffffffffffffffffffff021916908369ffffffffffffffffffff160217905550606082015181600101600a6101000a81548162ffffff021916908360020b62ffffff160217905550608082015181600101600d6101000a81548162ffffff021916908360020b62ffffff16021790555060a08201518160010160106101000a8154816001600160801b0302191690836001600160801b0316021790555060c0820151816002015560e082015181600301556101008201518160040160006101000a8154816001600160801b0302191690836001600160801b031602179055506101208201518160040160106101000a8154816001600160801b0302191690836001600160801b03160217905550905050897f3067048beee31b25b2f1681f88dac838c8bba36af25bfb2b7cf7473a5847e35f8a8a8a60405161238b93929190615b5e565b60405180910390a25050505050509193509193565b60078054604080516020601f60026000196101006001881615020190951694909404938401819004810282018101909252828152606093909290918301828280156108325780601f1061080757610100808354040283529160200191610832565b600061240f828401846154fe565b905061243f7f00000000000000000000000000000000000000000000000000000000000000008260000151613e3a565b50841561245a57805151602082015161245a91903388613e5d565b83156124785761247881600001516020015182602001513387613e5d565b5050505050565b6000818152600c6020908152604080832081516101408101835281546bffffffffffffffffffffffff811682526001600160a01b036c010000000000000000000000009091041693810193909352600181015469ffffffffffffffffffff81169284018390526a01000000000000000000008104600290810b810b810b6060860152600160681b8204810b810b810b60808601526001600160801b03600160801b92839004811660a08701529083015460c0860152600383015460e0860152600490920154808316610100860152041661012083015282918291829182918291829182918291829182918291906125885760405162461bcd60e51b815260040161086390615ab0565b6000600b6000836040015169ffffffffffffffffffff1669ffffffffffffffffffff1681526020019081526020016000206040518060600160405290816000820160009054906101000a90046001600160a01b03166001600160a01b03166001600160a01b031681526020016001820160009054906101000a90046001600160a01b03166001600160a01b03166001600160a01b031681526020016001820160149054906101000a900462ffffff1662ffffff1662ffffff1681525050905081600001518260200151826000015183602001518460400151866060015187608001518860a001518960c001518a60e001518b61010001518c61012001519d509d509d509d509d509d509d509d509d509d509d509d50505091939597999b5091939597999b565b6126b66132a7565b6001600160a01b0316826001600160a01b0316141561271c576040805162461bcd60e51b815260206004820152601960248201527f4552433732313a20617070726f766520746f2063616c6c657200000000000000604482015290519081900360640190fd5b80600560006127296132a7565b6001600160a01b0390811682526020808301939093526040918201600090812091871680825291909352912080547fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00169215159290921790915561278b6132a7565b6001600160a01b03167f17307eab39ab6107e8899845ad3d59bd9653f200f220920489ca2b5937696c318360405180821515815260200191505060405180910390a35050565b604080517fdd62ed3e0000000000000000000000000000000000000000000000000000000081523360048201523060248201529051600019916001600160a01b0389169163dd62ed3e91604480820192602092909190829003018186803b15801561283b57600080fd5b505afa15801561284f573d6000803e3d6000fd5b505050506040513d602081101561286557600080fd5b5051101561287b5761287b868686868686611691565b505050505050565b60608167ffffffffffffffff8111801561289c57600080fd5b506040519080825280602002602001820160405280156128d057816020015b60608152602001906001900390816128bb5790505b50905060005b828110156129bc57600080308686858181106128ee57fe5b90506020028101906129009190615c50565b60405161290e929190615833565b600060405180830381855af49150503d8060008114612949576040519150601f19603f3d011682016040523d82523d6000602084013e61294e565b606091505b50915091508161299a5760448151101561296757600080fd5b60048101905080806020019051810190612981919061545b565b60405162461bcd60e51b815260040161086391906159d2565b808484815181106129a757fe5b602090810291909101015250506001016128d6565b5092915050565b6129d46129ce6132a7565b8361332f565b612a0f5760405162461bcd60e51b8152600401808060200182810382526031815260200180615f556031913960400191505060405180910390fd5b612a1b84848484613fed565b50505050565b604080517fdd62ed3e000000000000000000000000000000000000000000000000000000008152336004820152306024820152905186916001600160a01b0389169163dd62ed3e91604480820192602092909190829003018186803b158015612a8957600080fd5b505afa158015612a9d573d6000803e3d6000fd5b505050506040513d6020811015612ab357600080fd5b5051101561287b5761287b868686868686612cf1565b7f000000000000000000000000000000000000000000000000000000000000000081565b6060612af88261329a565b612b0157600080fd5b6040517fe9dc63750000000000000000000000000000000000000000000000000000000081526001600160a01b037f0000000000000000000000000000000000000000000000000000000000000000169063e9dc637590612b689030908690600401615993565b60006040518083038186803b158015612b8057600080fd5b505afa158015612b94573d6000803e3d6000fd5b505050506040513d6000823e601f3d908101601f191682016040526114bf919081019061545b565b7f000000000000000000000000000000000000000000000000000000000000000081565b6000836001600160a01b03166370a08231306040518263ffffffff1660e01b815260040180826001600160a01b0316815260200191505060206040518083038186803b158015612c2f57600080fd5b505afa158015612c43573d6000803e3d6000fd5b505050506040513d6020811015612c5957600080fd5b5051905082811015612cb2576040805162461bcd60e51b815260206004820152601260248201527f496e73756666696369656e7420746f6b656e0000000000000000000000000000604482015290519081900360640190fd5b8015612a1b57612a1b84838361403f565b6001600160a01b03918216600090815260056020908152604080832093909416825291909152205460ff1690565b604080517fd505accf000000000000000000000000000000000000000000000000000000008152336004820152306024820152604481018790526064810186905260ff8516608482015260a4810184905260c4810183905290516001600160a01b0388169163d505accf9160e480830192600092919082900301818387803b15801561172457600080fd5b6000808235612d8b338261332f565b612da75760405162461bcd60e51b8152600401610863906159e5565b6000612db960608601604087016155bb565b6001600160801b03161180612de657506000612ddb60808601606087016155bb565b6001600160801b0316115b612def57600080fd5b600080612e026040870160208801615103565b6001600160a01b031614612e2557612e206040860160208701615103565b612e27565b305b85356000908152600c6020908152604080832060018082015469ffffffffffffffffffff168552600b8452828520835160608101855281546001600160a01b039081168252919092015490811694820194909452600160a01b90930462ffffff169183019190915292935090612ebd7f0000000000000000000000000000000000000000000000000000000000000000836133cf565b600484015460018501549192506001600160801b0380821692600160801b92839004821692900416156130da5760018501546040517fa34123a70000000000000000000000000000000000000000000000000000000081526001600160a01b0385169163a34123a791612f54916a01000000000000000000008104600290810b92600160681b909204900b906000906004016159ac565b6040805180830381600087803b158015612f6d57600080fd5b505af1158015612f81573d6000803e3d6000fd5b505050506040513d601f19601f82011682018060405250810190612fa59190615755565b5050600185015460009081906001600160a01b0386169063514ea4bf90612fea9030906a01000000000000000000008104600290810b91600160681b9004900b6134cb565b6040518263ffffffff1660e01b8152600401613006919061598a565b60a06040518083038186803b15801561301e57600080fd5b505afa158015613032573d6000803e3d6000fd5b505050506040513d601f19601f820116820180604052508101906130569190615605565b50509250925050613092876002015483038860010160109054906101000a90046001600160801b03166001600160801b0316600160801b613525565b840193506130cb876003015482038860010160109054906101000a90046001600160801b03166001600160801b0316600160801b613525565b60028801929092556003870155015b6000806001600160801b0384166130f760608e0160408f016155bb565b6001600160801b03161161311a5761311560608d0160408e016155bb565b61311c565b835b836001600160801b03168d606001602081019061313991906155bb565b6001600160801b03161161315c5761315760808e0160608f016155bb565b61315e565b835b60018901546040517f4f1eb3d80000000000000000000000000000000000000000000000000000000081529294509092506001600160a01b03871691634f1eb3d8916131d1918c916a01000000000000000000008104600290810b92600160681b909204900b908890889060040161589a565b6040805180830381600087803b1580156131ea57600080fd5b505af11580156131fe573d6000803e3d6000fd5b505050506040513d601f19601f8201168201806040525081019061322291906155d7565b6004890180546fffffffffffffffffffffffffffffffff196001600160801b03918216600160801b878a0384160217168689038216179091556040519281169d50169a508c35907f40d0efd1a53d60ecbf40971b9daf7dc90178c3aadc7aab1765632738fa8b8f0190610dc4908b90869086906158d7565b60006114bf6002836141cf565b3390565b6000818152600c6020526040902080546bffffffffffffffffffffffff166c010000000000000000000000006001600160a01b0385169081029190911790915581906132f6826118fe565b6001600160a01b03167f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b92560405160405180910390a45050565b600061333a8261329a565b6133755760405162461bcd60e51b815260040180806020018281038252602c815260200180615e32602c913960400191505060405180910390fd5b6000613380836118fe565b9050806001600160a01b0316846001600160a01b031614806133bb5750836001600160a01b03166133b08461083c565b6001600160a01b0316145b806110f157506110f18185612cc3565b4290565b600081602001516001600160a01b031682600001516001600160a01b0316106133f757600080fd5b50805160208083015160409384015184516001600160a01b0394851681850152939091168385015262ffffff166060808401919091528351808403820181526080840185528051908301207fff0000000000000000000000000000000000000000000000000000000000000060a085015294901b6bffffffffffffffffffffffff191660a183015260b58201939093527f965fc9e2b83fdb334d9096bef7094a4584dccd9e2ddd24e23eebe1c03603b39860d5808301919091528251808303909101815260f5909101909152805191012090565b604080516bffffffffffffffffffffffff19606086901b16602080830191909152600285810b60e890811b60348501529085900b901b60378301528251601a818403018152603a90920190925280519101205b9392505050565b600080806000198587098686029250828110908390030390508061355b576000841161355057600080fd5b50829004905061351e565b80841161356757600080fd5b6000848688096000868103871696879004966002600389028118808a02820302808a02820302808a02820302808a02820302808a02820302808a02909103029181900381900460010186841190950394909402919094039290920491909117919091029150509392505050565b604080516000808252602082019092526001600160a01b0384169083906040518082805190602001908083835b602083106136205780518252601f199092019160209182019101613601565b6001836020036101000a03801982511681845116808217855250505050505090500191505060006040518083038185875af1925050503d8060008114613682576040519150601f19603f3d011682016040523d82523d6000602084013e613687565b606091505b5050905080610969576040805162461bcd60e51b815260206004820152600360248201527f5354450000000000000000000000000000000000000000000000000000000000604482015290519081900360640190fd5b60006114bf826141db565b6000806000806000604051806060016040528087600001516001600160a01b0316815260200187602001516001600160a01b03168152602001876040015162ffffff16815250905061375a7f0000000000000000000000000000000000000000000000000000000000000000826133cf565b91506000826001600160a01b0316633850c7bd6040518163ffffffff1660e01b815260040160e06040518083038186803b15801561379757600080fd5b505afa1580156137ab573d6000803e3d6000fd5b505050506040513d601f19601f820116820180604052508101906137cf9190615666565b505050505050905060006137e688608001516141df565b905060006137f78960a001516141df565b905061380e8383838c60c001518d60e0015161452d565b9750505050816001600160a01b0316633c8a7d8d876060015188608001518960a00151896040518060400160405280888152602001336001600160a01b03168152506040516020016138609190615b1e565b6040516020818303038152906040526040518663ffffffff1660e01b815260040161388f959493929190615857565b6040805180830381600087803b1580156138a857600080fd5b505af11580156138bc573d6000803e3d6000fd5b505050506040513d601f19601f820116820180604052508101906138e09190615755565b610100880151919550935084108015906138ff57508561012001518310155b61391b5760405162461bcd60e51b815260040161086390615a79565b509193509193565b826001600160a01b0316613936826118fe565b6001600160a01b03161461397b5760405162461bcd60e51b8152600401808060200182810382526029815260200180615f0b6029913960400191505060405180910390fd5b6001600160a01b0382166139c05760405162461bcd60e51b8152600401808060200182810382526024815260200180615de86024913960400191505060405180910390fd5b6139cb838383610969565b6139d66000826132ab565b6001600160a01b03831660009081526001602052604090206139f890826145f1565b506001600160a01b0382166000908152600160205260409020613a1b90826145fd565b50613a2860028284614609565b5080826001600160a01b0316846001600160a01b03167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef60405160405180910390a4505050565b60006114bc838361461f565b4690565b6000613a8a826118fe565b9050613a9881600084610969565b613aa36000836132ab565b6000828152600860205260409020546002600019610100600184161502019091160415613ae1576000828152600860205260408120613ae191615073565b6001600160a01b0381166000908152600160205260409020613b0390836145f1565b50613b0f600283614683565b5060405182906000906001600160a01b038416907fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef908390a45050565b6000808080613b5b868661468f565b909450925050505b9250929050565b60006110f184848461470a565b6000908152600c6020526040902080546bffffffffffffffffffffffff19811660016bffffffffffffffffffffffff9283169081019092161790915590565b3b151590565b6001600160a01b038216613c17576040805162461bcd60e51b815260206004820181905260248201527f4552433732313a206d696e7420746f20746865207a65726f2061646472657373604482015290519081900360640190fd5b613c208161329a565b15613c72576040805162461bcd60e51b815260206004820152601c60248201527f4552433732313a20746f6b656e20616c7265616479206d696e74656400000000604482015290519081900360640190fd5b613c7e60008383610969565b6001600160a01b0382166000908152600160205260409020613ca090826145fd565b50613cad60028284614609565b5060405181906001600160a01b038416906000907fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef908290a45050565b6001600160a01b0382166000908152600a602052604090205469ffffffffffffffffffff16806114bf5750600d8054600169ffffffffffffffffffff76010000000000000000000000000000000000000000000080840482168381019092160275ffffffffffffffffffffffffffffffffffffffffffff909316929092179092556001600160a01b038085166000908152600a6020908152604080832080547fffffffffffffffffffffffffffffffffffffffffffff000000000000000000001686179055848352600b825291829020865181549085167fffffffffffffffffffffffff000000000000000000000000000000000000000091821617825591870151950180549287015162ffffff16600160a01b027fffffffffffffffffff000000ffffffffffffffffffffffffffffffffffffffff969094169290911691909117939093161790915592915050565b6000613e4683836133cf565b9050336001600160a01b038216146114bf57600080fd5b7f00000000000000000000000000000000000000000000000000000000000000006001600160a01b0316846001600160a01b0316148015613e9e5750804710155b15613fc0577f00000000000000000000000000000000000000000000000000000000000000006001600160a01b031663d0e30db0826040518263ffffffff1660e01b81526004016000604051808303818588803b158015613efe57600080fd5b505af1158015613f12573d6000803e3d6000fd5b50505050507f00000000000000000000000000000000000000000000000000000000000000006001600160a01b031663a9059cbb83836040518363ffffffff1660e01b815260040180836001600160a01b0316815260200182815260200192505050602060405180830381600087803b158015613f8e57600080fd5b505af1158015613fa2573d6000803e3d6000fd5b505050506040513d6020811015613fb857600080fd5b50612a1b9050565b6001600160a01b038316301415613fe157613fdc84838361403f565b612a1b565b612a1b848484846147d4565b613ff8848484613923565b6140048484848461496c565b612a1b5760405162461bcd60e51b8152600401808060200182810382526032815260200180615d8f6032913960400191505060405180910390fd5b604080516001600160a01b038481166024830152604480830185905283518084039091018152606490920183526020820180517bffffffffffffffffffffffffffffffffffffffffffffffffffffffff167fa9059cbb000000000000000000000000000000000000000000000000000000001781529251825160009485949389169392918291908083835b602083106140e95780518252601f1990920191602091820191016140ca565b6001836020036101000a0380198251168184511680821785525050505050509050019150506000604051808303816000865af19150503d806000811461414b576040519150601f19603f3d011682016040523d82523d6000602084013e614150565b606091505b509150915081801561417e57508051158061417e575080806020019051602081101561417b57600080fd5b50515b612478576040805162461bcd60e51b815260206004820152600260248201527f5354000000000000000000000000000000000000000000000000000000000000604482015290519081900360640190fd5b60006114bc8383614b48565b5490565b60008060008360020b126141f6578260020b6141fe565b8260020b6000035b9050620d89e8811115614258576040805162461bcd60e51b815260206004820152600160248201527f5400000000000000000000000000000000000000000000000000000000000000604482015290519081900360640190fd5b60006001821661426c57600160801b61427e565b6ffffcb933bd6fad37aa2d162d1a5940015b70ffffffffffffffffffffffffffffffffff16905060028216156142b2576ffff97272373d413259a46990580e213a0260801c5b60048216156142d1576ffff2e50f5f656932ef12357cf3c7fdcc0260801c5b60088216156142f0576fffe5caca7e10e4e61c3624eaa0941cd00260801c5b601082161561430f576fffcb9843d60f6159c9db58835c9266440260801c5b602082161561432e576fff973b41fa98c081472e6896dfb254c00260801c5b604082161561434d576fff2ea16466c96a3843ec78b326b528610260801c5b608082161561436c576ffe5dee046a99a2a811c461f1969c30530260801c5b61010082161561438c576ffcbe86c7900a88aedcffc83b479aa3a40260801c5b6102008216156143ac576ff987a7253ac413176f2b074cf7815e540260801c5b6104008216156143cc576ff3392b0822b70005940c7a398e4b70f30260801c5b6108008216156143ec576fe7159475a2c29b7443b29c7fa6e889d90260801c5b61100082161561440c576fd097f3bdfd2022b8845ad8f792aa58250260801c5b61200082161561442c576fa9f746462d870fdf8a65dc1f90e061e50260801c5b61400082161561444c576f70d869a156d2a1b890bb3df62baf32f70260801c5b61800082161561446c576f31be135f97d08fd981231505542fcfa60260801c5b6201000082161561448d576f09aa508b5b7a84e1c677de54f3e99bc90260801c5b620200008216156144ad576e5d6af8dedb81196699c329225ee6040260801c5b620400008216156144cc576d2216e584f5fa1ea926041bedfe980260801c5b620800008216156144e9576b048a170391f7dc42444e8fa20260801c5b60008460020b131561450457806000198161450057fe5b0490505b64010000000081061561451857600161451b565b60005b60ff16602082901c0192505050919050565b6000836001600160a01b0316856001600160a01b0316111561454d579293925b846001600160a01b0316866001600160a01b03161161457857614571858585614b60565b90506145e8565b836001600160a01b0316866001600160a01b031610156145da57600061459f878686614b60565b905060006145ae878986614bcc565b9050806001600160801b0316826001600160801b0316106145cf57806145d1565b815b925050506145e8565b6145e5858584614bcc565b90505b95945050505050565b60006114bc8383614c12565b60006114bc8383614cd8565b60006110f184846001600160a01b038516614d22565b815460009082106146615760405162461bcd60e51b8152600401808060200182810382526022815260200180615d6d6022913960400191505060405180910390fd5b82600001828154811061467057fe5b9060005260206000200154905092915050565b60006114bc8383614db9565b8154600090819083106146d35760405162461bcd60e51b8152600401808060200182810382526022815260200180615ee96022913960400191505060405180910390fd5b60008460000184815481106146e457fe5b906000526020600020906002020190508060000154816001015492509250509250929050565b600082815260018401602052604081205482816147a55760405162461bcd60e51b81526004018080602001828103825283818151815260200191508051906020019080838360005b8381101561476a578181015183820152602001614752565b50505050905090810190601f1680156147975780820380516001836020036101000a031916815260200191505b509250505060405180910390fd5b508460000160018203815481106147b857fe5b9060005260206000209060020201600101549150509392505050565b604080516001600160a01b0385811660248301528481166044830152606480830185905283518084039091018152608490920183526020820180517bffffffffffffffffffffffffffffffffffffffffffffffffffffffff167f23b872dd00000000000000000000000000000000000000000000000000000000178152925182516000948594938a169392918291908083835b602083106148865780518252601f199092019160209182019101614867565b6001836020036101000a0380198251168184511680821785525050505050509050019150506000604051808303816000865af19150503d80600081146148e8576040519150601f19603f3d011682016040523d82523d6000602084013e6148ed565b606091505b509150915081801561491b57508051158061491b575080806020019051602081101561491857600080fd5b50515b61287b576040805162461bcd60e51b815260206004820152600360248201527f5354460000000000000000000000000000000000000000000000000000000000604482015290519081900360640190fd5b6000614980846001600160a01b0316613bb6565b61498c575060016110f1565b6000614add7f150b7a02000000000000000000000000000000000000000000000000000000006149ba6132a7565b88878760405160240180856001600160a01b03168152602001846001600160a01b0316815260200183815260200180602001828103825283818151815260200191508051906020019080838360005b83811015614a21578181015183820152602001614a09565b50505050905090810190601f168015614a4e5780820380516001836020036101000a031916815260200191505b5095505050505050604051602081830303815290604052907bffffffffffffffffffffffffffffffffffffffffffffffffffffffff19166020820180517bffffffffffffffffffffffffffffffffffffffffffffffffffffffff8381831617835250505050604051806060016040528060328152602001615d8f603291396001600160a01b0388169190614e8d565b90506000818060200190516020811015614af657600080fd5b50517fffffffff00000000000000000000000000000000000000000000000000000000167f150b7a02000000000000000000000000000000000000000000000000000000001492505050949350505050565b60009081526001919091016020526040902054151590565b6000826001600160a01b0316846001600160a01b03161115614b80579192915b6000614bac856001600160a01b0316856001600160a01b03166c01000000000000000000000000613525565b90506145e8614bc784838888036001600160a01b0316613525565b614e9c565b6000826001600160a01b0316846001600160a01b03161115614bec579192915b6110f1614bc7836c010000000000000000000000008787036001600160a01b0316613525565b60008181526001830160205260408120548015614cce5783546000198083019190810190600090879083908110614c4557fe5b9060005260206000200154905080876000018481548110614c6257fe5b600091825260208083209091019290925582815260018981019092526040902090840190558654879080614c9257fe5b600190038181906000526020600020016000905590558660010160008781526020019081526020016000206000905560019450505050506114bf565b60009150506114bf565b6000614ce48383614b48565b614d1a575081546001818101845560008481526020808220909301849055845484825282860190935260409020919091556114bf565b5060006114bf565b600082815260018401602052604081205480614d8757505060408051808201825283815260208082018481528654600181810189556000898152848120955160029093029095019182559151908201558654868452818801909252929091205561351e565b82856000016001830381548110614d9a57fe5b906000526020600020906002020160010181905550600091505061351e565b60008181526001830160205260408120548015614cce5783546000198083019190810190600090879083908110614dec57fe5b9060005260206000209060020201905080876000018481548110614e0c57fe5b600091825260208083208454600290930201918255600193840154918401919091558354825289830190526040902090840190558654879080614e4b57fe5b60008281526020808220600260001990940193840201828155600190810183905592909355888152898201909252604082209190915594506114bf9350505050565b60606110f18484600085614eb2565b806001600160801b03811681146107a157600080fd5b606082471015614ef35760405162461bcd60e51b8152600401808060200182810382526026815260200180615e0c6026913960400191505060405180910390fd5b614efc85613bb6565b614f4d576040805162461bcd60e51b815260206004820152601d60248201527f416464726573733a2063616c6c20746f206e6f6e2d636f6e7472616374000000604482015290519081900360640190fd5b600080866001600160a01b031685876040518082805190602001908083835b60208310614f8b5780518252601f199092019160209182019101614f6c565b6001836020036101000a03801982511681845116808217855250505050505090500191505060006040518083038185875af1925050503d8060008114614fed576040519150601f19603f3d011682016040523d82523d6000602084013e614ff2565b606091505b509150915061500282828661500d565b979650505050505050565b6060831561501c57508161351e565b82511561502c5782518084602001fd5b60405162461bcd60e51b815260206004820181815284516024840152845185939192839260440191908501908083836000831561476a578181015183820152602001614752565b50805460018160011615610100020316600290046000825580601f1061509957506150b7565b601f0160209004906000526020600020908101906150b791906150ba565b50565b5b808211156150cf57600081556001016150bb565b5090565b80356107a181615d25565b805161ffff811681146107a157600080fd5b803562ffffff811681146107a157600080fd5b600060208284031215615114578081fd5b813561351e81615d25565b60008060408385031215615131578081fd5b823561513c81615d25565b9150602083013561514c81615d25565b809150509250929050565b6000806000806080858703121561516c578182fd5b843561517781615d25565b9350602085013561518781615d25565b9250615195604086016150f0565b915060608501356151a581615d25565b939692955090935050565b6000806000606084860312156151c4578081fd5b83356151cf81615d25565b925060208401356151df81615d25565b929592945050506040919091013590565b60008060008060808587031215615205578182fd5b843561521081615d25565b9350602085013561522081615d25565b925060408501359150606085013567ffffffffffffffff811115615242578182fd5b8501601f81018713615252578182fd5b803561526561526082615cd7565b615cb3565b818152886020838501011115615279578384fd5b81602084016020830137908101602001929092525092959194509250565b600080604083850312156152a9578182fd5b82356152b481615d25565b9150602083013561514c81615d3a565b600080604083850312156152d6578182fd5b82356152e181615d25565b946020939093013593505050565b600080600060608486031215615303578081fd5b833561530e81615d25565b925060208401359150604084013561532581615d25565b809150509250925092565b60008060008060008060c08789031215615348578384fd5b863561535381615d25565b95506020870135945060408701359350606087013560ff81168114615376578283fd5b9598949750929560808101359460a0909101359350915050565b600080602083850312156153a2578182fd5b823567ffffffffffffffff808211156153b9578384fd5b818501915085601f8301126153cc578384fd5b8135818111156153da578485fd5b86602080830285010111156153ed578485fd5b60209290920196919550909350505050565b600060208284031215615410578081fd5b81357fffffffff000000000000000000000000000000000000000000000000000000008116811461351e578182fd5b600060208284031215615450578081fd5b813561351e81615d48565b60006020828403121561546c578081fd5b815167ffffffffffffffff811115615482578182fd5b8201601f81018413615492578182fd5b80516154a061526082615cd7565b8181528560208385010111156154b4578384fd5b6145e8826020830160208601615cf9565b6000608082840312156154d6578081fd5b50919050565b600060a082840312156154d6578081fd5b600060c082840312156154d6578081fd5b60008183036080811215615510578182fd5b6040516040810167ffffffffffffffff828210818311171561552e57fe5b81604052606084121561553f578485fd5b60a083019350818410818511171561555357fe5b50826040528435925061556583615d25565b91825260208401359161557783615d25565b826060830152615589604086016150f0565b6080830152815261559c606085016150d3565b6020820152949350505050565b600061016082840312156154d6578081fd5b6000602082840312156155cc578081fd5b813561351e81615d57565b600080604083850312156155e9578182fd5b82516155f481615d57565b602084015190925061514c81615d57565b600080600080600060a0868803121561561c578283fd5b855161562781615d57565b809550506020860151935060408601519250606086015161564781615d57565b608087015190925061565881615d57565b809150509295509295909350565b600080600080600080600060e0888a031215615680578485fd5b875161568b81615d25565b602089015190975061569c81615d48565b95506156aa604089016150de565b94506156b8606089016150de565b93506156c6608089016150de565b925060a088015163ffffffff811681146156de578182fd5b60c08901519092506156ef81615d3a565b8091505092959891949750929550565b600060208284031215615710578081fd5b6114bc826150f0565b60006020828403121561572a578081fd5b5035919050565b60008060408385031215615743578182fd5b82359150602083013561514c81615d25565b60008060408385031215615767578182fd5b505080516020909101519092909150565b6000806000806060858703121561578d578182fd5b8435935060208501359250604085013567ffffffffffffffff808211156157b2578384fd5b818701915087601f8301126157c5578384fd5b8135818111156157d3578485fd5b8860208285010111156157e4578485fd5b95989497505060200194505050565b6000815180845261580b816020860160208601615cf9565b601f01601f19169290920160200192915050565b60020b9052565b6001600160801b03169052565b6000828483379101908152919050565b6001600160a01b0391909116815260200190565b60006001600160a01b03871682528560020b60208301528460020b60408301526001600160801b038416606083015260a0608083015261500260a08301846157f3565b6001600160a01b03959095168552600293840b60208601529190920b60408401526001600160801b03918216606084015216608082015260a00190565b6001600160a01b039390931683526001600160801b03918216602084015216604082015260600190565b6000602080830181845280855180835260408601915060408482028701019250838701855b82811015615972577fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc08886030184526159608583516157f3565b94509285019290850190600101615926565b5092979650505050505050565b901515815260200190565b90815260200190565b6001600160a01b03929092168252602082015260400190565b600293840b81529190920b60208201526001600160801b03909116604082015260600190565b6000602082526114bc60208301846157f3565b6020808252600c908201527f4e6f7420617070726f7665640000000000000000000000000000000000000000604082015260600190565b6020808252602c908201527f4552433732313a20617070726f76656420717565727920666f72206e6f6e657860408201527f697374656e7420746f6b656e0000000000000000000000000000000000000000606082015260800190565b60208082526014908201527f507269636520736c69707061676520636865636b000000000000000000000000604082015260600190565b60208082526010908201527f496e76616c696420746f6b656e20494400000000000000000000000000000000604082015260600190565b6020808252600b908201527f4e6f7420636c6561726564000000000000000000000000000000000000000000604082015260600190565b815180516001600160a01b03908116835260208083015182168185015260409283015162ffffff1692840192909252920151909116606082015260800190565b6001600160801b039390931683526020830191909152604082015260600190565b9384526001600160801b039290921660208401526040830152606082015260800190565b918252602082015260400190565b6bffffffffffffffffffffffff8d1681526001600160a01b038c811660208301528b811660408301528a16606082015262ffffff89166080820152600288900b60a08201526101808101615c0860c083018961581f565b615c1560e0830188615826565b8561010083015284610120830152615c31610140830185615826565b615c3f610160830184615826565b9d9c50505050505050505050505050565b60008083357fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe1843603018112615c84578283fd5b83018035915067ffffffffffffffff821115615c9e578283fd5b602001915036819003821315613b6357600080fd5b60405181810167ffffffffffffffff81118282101715615ccf57fe5b604052919050565b600067ffffffffffffffff821115615ceb57fe5b50601f01601f191660200190565b60005b83811015615d14578181015183820152602001615cfc565b83811115612a1b5750506000910152565b6001600160a01b03811681146150b757600080fd5b80151581146150b757600080fd5b8060020b81146150b757600080fd5b6001600160801b03811681146150b757600080fdfe456e756d657261626c655365743a20696e646578206f7574206f6620626f756e64734552433732313a207472616e7366657220746f206e6f6e20455243373231526563656976657220696d706c656d656e7465724552433732315065726d69743a20617070726f76616c20746f2063757272656e74206f776e65724552433732313a207472616e7366657220746f20746865207a65726f2061646472657373416464726573733a20696e73756666696369656e742062616c616e636520666f722063616c6c4552433732313a206f70657261746f7220717565727920666f72206e6f6e6578697374656e7420746f6b656e4552433732313a20617070726f76652063616c6c6572206973206e6f74206f776e6572206e6f7220617070726f76656420666f7220616c6c4552433732313a2062616c616e636520717565727920666f7220746865207a65726f20616464726573734552433732313a206f776e657220717565727920666f72206e6f6e6578697374656e7420746f6b656e456e756d657261626c654d61703a20696e646578206f7574206f6620626f756e64734552433732313a207472616e73666572206f6620746f6b656e2074686174206973206e6f74206f776e4552433732313a20617070726f76616c20746f2063757272656e74206f776e65724552433732313a207472616e736665722063616c6c6572206973206e6f74206f776e6572206e6f7220617070726f766564a164736f6c6343000706000a";
        vector::append(manager_bytecode, deployer);
        vector::append(manager_bytecode, factory);
        vector::append(manager_bytecode, weth9);
        vector::append(manager_bytecode, weth9);
        let manager = execute(sender, ZERO_ADDR, 4, *manager_bytecode, 0);

        let erc20 = x"60806040523480156200001157600080fd5b5060405162000a7c38038062000a7c833981016040819052620000349162000123565b818160036200004483826200021c565b5060046200005382826200021c565b5050505050620002e8565b634e487b7160e01b600052604160045260246000fd5b600082601f8301126200008657600080fd5b81516001600160401b0380821115620000a357620000a36200005e565b604051601f8301601f19908116603f01168101908282118183101715620000ce57620000ce6200005e565b81604052838152602092508683858801011115620000eb57600080fd5b600091505b838210156200010f5785820183015181830184015290820190620000f0565b600093810190920192909252949350505050565b600080604083850312156200013757600080fd5b82516001600160401b03808211156200014f57600080fd5b6200015d8683870162000074565b935060208501519150808211156200017457600080fd5b50620001838582860162000074565b9150509250929050565b600181811c90821680620001a257607f821691505b602082108103620001c357634e487b7160e01b600052602260045260246000fd5b50919050565b601f8211156200021757600081815260208120601f850160051c81016020861015620001f25750805b601f850160051c820191505b818110156200021357828155600101620001fe565b5050505b505050565b81516001600160401b038111156200023857620002386200005e565b62000250816200024984546200018d565b84620001c9565b602080601f8311600181146200028857600084156200026f5750858301515b600019600386901b1c1916600185901b17855562000213565b600085815260208120601f198616915b82811015620002b95788860151825594840194600190910190840162000298565b5085821015620002d85787850151600019600388901b60f8161c191681555b5050505050600190811b01905550565b61078480620002f86000396000f3fe608060405234801561001057600080fd5b506004361061009e5760003560e01c806340c10f191161006657806340c10f191461011857806370a082311461012d57806395d89b4114610156578063a9059cbb1461015e578063dd62ed3e1461017157600080fd5b806306fdde03146100a3578063095ea7b3146100c157806318160ddd146100e457806323b872dd146100f6578063313ce56714610109575b600080fd5b6100ab6101aa565b6040516100b891906105ce565b60405180910390f35b6100d46100cf366004610638565b61023c565b60405190151581526020016100b8565b6002545b6040519081526020016100b8565b6100d4610104366004610662565b610256565b604051601281526020016100b8565b61012b610126366004610638565b61027a565b005b6100e861013b36600461069e565b6001600160a01b031660009081526020819052604090205490565b6100ab610288565b6100d461016c366004610638565b610297565b6100e861017f3660046106c0565b6001600160a01b03918216600090815260016020908152604080832093909416825291909152205490565b6060600380546101b9906106f3565b80601f01602080910402602001604051908101604052809291908181526020018280546101e5906106f3565b80156102325780601f1061020757610100808354040283529160200191610232565b820191906000526020600020905b81548152906001019060200180831161021557829003601f168201915b5050505050905090565b60003361024a8185856102a5565b60019150505b92915050565b6000336102648582856102b7565b61026f85858561033a565b506001949350505050565b6102848282610399565b5050565b6060600480546101b9906106f3565b60003361024a81858561033a565b6102b283838360016103cf565b505050565b6001600160a01b038381166000908152600160209081526040808320938616835292905220546000198114610334578181101561032557604051637dc7a0d960e11b81526001600160a01b038416600482015260248101829052604481018390526064015b60405180910390fd5b610334848484840360006103cf565b50505050565b6001600160a01b03831661036457604051634b637e8f60e11b81526000600482015260240161031c565b6001600160a01b03821661038e5760405163ec442f0560e01b81526000600482015260240161031c565b6102b28383836104a4565b6001600160a01b0382166103c35760405163ec442f0560e01b81526000600482015260240161031c565b610284600083836104a4565b6001600160a01b0384166103f95760405163e602df0560e01b81526000600482015260240161031c565b6001600160a01b03831661042357604051634a1406b160e11b81526000600482015260240161031c565b6001600160a01b038085166000908152600160209081526040808320938716835292905220829055801561033457826001600160a01b0316846001600160a01b03167f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b9258460405161049691815260200190565b60405180910390a350505050565b6001600160a01b0383166104cf5780600260008282546104c4919061072d565b909155506105419050565b6001600160a01b038316600090815260208190526040902054818110156105225760405163391434e360e21b81526001600160a01b0385166004820152602481018290526044810183905260640161031c565b6001600160a01b03841660009081526020819052604090209082900390555b6001600160a01b03821661055d5760028054829003905561057c565b6001600160a01b03821660009081526020819052604090208054820190555b816001600160a01b0316836001600160a01b03167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef836040516105c191815260200190565b60405180910390a3505050565b600060208083528351808285015260005b818110156105fb578581018301518582016040015282016105df565b506000604082860101526040601f19601f8301168501019250505092915050565b80356001600160a01b038116811461063357600080fd5b919050565b6000806040838503121561064b57600080fd5b6106548361061c565b946020939093013593505050565b60008060006060848603121561067757600080fd5b6106808461061c565b925061068e6020850161061c565b9150604084013590509250925092565b6000602082840312156106b057600080fd5b6106b98261061c565b9392505050565b600080604083850312156106d357600080fd5b6106dc8361061c565b91506106ea6020840161061c565b90509250929050565b600181811c9082168061070757607f821691505b60208210810361072757634e487b7160e01b600052602260045260246000fd5b50919050565b8082018082111561025057634e487b7160e01b600052601160045260246000fdfea2646970667358221220eb2074c6ef778f0a70b31dcb739e35ec3ee87e61f8951f5e5f1c279ff9425f1c64736f6c63430008130033000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000004555344430000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000045553444300000000000000000000000000000000000000000000000000000000";
        let tokenA = execute(sender, ZERO_ADDR, 5, erc20, 0);
        let tokenB = execute(sender, ZERO_ADDR, 6, erc20, 0);
        debug::print(&tokenA);
        debug::print(&tokenB);


        debug::print(&utf8(b"mint token"));
        let mint_token_data = &mut x"40c10f19";
        vector::append(mint_token_data, sender);
        vector::append(mint_token_data, u256_to_data(amount_to_mint * 10));
        execute(sender, tokenA, 7, *mint_token_data, 0);
        execute(sender, tokenB, 8, *mint_token_data, 0);

        debug::print(&utf8(b"approve token"));
        let approve_data = &mut x"095ea7b3";
        vector::append(approve_data, manager);
        vector::append(approve_data, u256_to_data(amount_to_mint));
        execute(sender, tokenA, 9, *approve_data, 0);
        execute(sender, tokenB, 10, *approve_data, 0);

        debug::print(&utf8(b"init pool"));
        // 0x0000000000000000000000000000000000000001000000000000000000000000
        let init_pool_data = &mut x"13ead562";
        vector::append(init_pool_data, weth9);
        vector::append(init_pool_data, tokenA);
        vector::append(init_pool_data, u256_to_data(3000));
        vector::append(init_pool_data, u256_to_data(79228162514264337593543950336));
        execute(sender, manager, 11, *init_pool_data, 0);

        debug::print(&utf8(b"add liquidity"));
        let add_liquidity_data = &mut x"88316456";
        vector::append(add_liquidity_data, weth9);
        vector::append(add_liquidity_data, tokenA);
        vector::append(add_liquidity_data, u256_to_data(3000));
        vector::append(add_liquidity_data, u256_to_data(add_sign(887220, true)));
        vector::append(add_liquidity_data, u256_to_data(887220));
        vector::append(add_liquidity_data, u256_to_data(amount_to_mint));
        vector::append(add_liquidity_data, u256_to_data(amount_to_mint));
        vector::append(add_liquidity_data, u256_to_data(1));
        vector::append(add_liquidity_data, u256_to_data(1));
        vector::append(add_liquidity_data, sender);
        vector::append(add_liquidity_data, u256_to_data(0));
        execute(sender, manager, 12, *add_liquidity_data, amount_to_mint);

        debug::print(&utf8(b"init pool2"));
        // 0x0000000000000000000000000000000000000001000000000000000000000000
        let init_pool_data = &mut x"13ead562";
        vector::append(init_pool_data, to_32bit(x"46A3F4514a37dAb2b22428eB663E05A6eA169b63"));
        vector::append(init_pool_data, to_32bit(x"4dAE7042D681274E184902c65bfFb0698DA10585"));
        vector::append(init_pool_data, u256_to_data(100));
        vector::append(init_pool_data, u256_to_data(79228162514264337593543950336));
        execute(sender, manager, 13, *init_pool_data, 0);

        debug::print(&create2_address(to_32bit(x"Aa2fd61123FCABf0AcE5f87Ce00BbC9E5AcB6d80")
            , to_32bit(x"01")
            , to_32bit(x"02"), 100, x"965fc9e2b83fdb334d9096bef7094a4584dccd9e2ddd24e23eebe1c03603b398"));
    }


    // #[test]
    // fun test_simple_deploy() acquires Account, ContractEvent {
    //     let sender = x"054ecb78d0276cf182514211d0c21fe46590b654";
    //     // let tx = x"02f906bd0582013f8459682f008459682f0a830619208080b90662608060405234801561000f575f80fd5b506106458061001d5f395ff3fe608060405234801561000f575f80fd5b5060043610610034575f3560e01c806306fdde0314610038578063c47f002714610056575b5f80fd5b610040610072565b60405161004d9190610199565b60405180910390f35b610070600480360381019061006b91906102f6565b6100fd565b005b5f805461007e9061036a565b80601f01602080910402602001604051908101604052809291908181526020018280546100aa9061036a565b80156100f55780601f106100cc576101008083540402835291602001916100f5565b820191905f5260205f20905b8154815290600101906020018083116100d857829003601f168201915b505050505081565b805f908161010b9190610540565b5050565b5f81519050919050565b5f82825260208201905092915050565b5f5b8381101561014657808201518184015260208101905061012b565b5f8484015250505050565b5f601f19601f8301169050919050565b5f61016b8261010f565b6101758185610119565b9350610185818560208601610129565b61018e81610151565b840191505092915050565b5f6020820190508181035f8301526101b18184610161565b905092915050565b5f604051905090565b5f80fd5b5f80fd5b5f80fd5b5f80fd5b7f4e487b71000000000000000000000000000000000000000000000000000000005f52604160045260245ffd5b61020882610151565b810181811067ffffffffffffffff82111715610227576102266101d2565b5b80604052505050565b5f6102396101b9565b905061024582826101ff565b919050565b5f67ffffffffffffffff821115610264576102636101d2565b5b61026d82610151565b9050602081019050919050565b828183375f83830152505050565b5f61029a6102958461024a565b610230565b9050828152602081018484840111156102b6576102b56101ce565b5b6102c184828561027a565b509392505050565b5f82601f8301126102dd576102dc6101ca565b5b81356102ed848260208601610288565b91505092915050565b5f6020828403121561030b5761030a6101c2565b5b5f82013567ffffffffffffffff811115610328576103276101c6565b5b610334848285016102c9565b91505092915050565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52602260045260245ffd5b5f600282049050600182168061038157607f821691505b6020821081036103945761039361033d565b5b50919050565b5f819050815f5260205f209050919050565b5f6020601f8301049050919050565b5f82821b905092915050565b5f600883026103f67fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff826103bb565b61040086836103bb565b95508019841693508086168417925050509392505050565b5f819050919050565b5f819050919050565b5f61044461043f61043a84610418565b610421565b610418565b9050919050565b5f819050919050565b61045d8361042a565b6104716104698261044b565b8484546103c7565b825550505050565b5f90565b610485610479565b610490818484610454565b505050565b5b818110156104b3576104a85f8261047d565b600181019050610496565b5050565b601f8211156104f8576104c98161039a565b6104d2846103ac565b810160208510156104e1578190505b6104f56104ed856103ac565b830182610495565b50505b505050565b5f82821c905092915050565b5f6105185f19846008026104fd565b1980831691505092915050565b5f6105308383610509565b9150826002028217905092915050565b6105498261010f565b67ffffffffffffffff811115610562576105616101d2565b5b61056c825461036a565b6105778282856104b7565b5f60209050601f8311600181146105a8575f8415610596578287015190505b6105a08582610525565b865550610607565b601f1984166105b68661039a565b5f5b828110156105dd578489015182556001820191506020850194506020810190506105b8565b868310156105fa57848901516105f6601f891682610509565b8355505b6001600288020188555050505b50505050505056fea26469706673582212202a4a6ecbf840f2c1630f654c6698a1524b4f6ee0fc5f769b9bb1968cc47c8b4464736f6c63430008160033c001a00a3b007ea2049c206926caacfc6875c58e2b46907e9a0addeb3067c544bfa25da07796d9edc4f0c647130e357526edc3b53c9b7a947e25f5d83353ba83966bd226";
    //     // let evm = account::create_account_for_test(@0x1);
    //     // send_tx(&evm, sender, tx, u256_to_data(0), 1);
    //
    //
    //     create_account_if_not_exist(create_resource_address(&@aptos_framework, sender));
    //     // let bytecode_1 = x"6101ca61003a600b82828239805160001a60731461002d57634e487b7160e01b600052600060045260246000fd5b30600052607381538281f3fe73000000000000000000000000000000000000000030146080604052600436106100355760003560e01c806313769cd41461003a575b600080fd5b81801561004657600080fd5b5061005a610055366004610177565b61005c565b005b600c8401546001600160a01b0316156100c75760405162461bcd60e51b8152602060048201526024808201527f526573657276652068617320616c7265616479206265656e20696e697469616c6044820152631a5e995960e21b606482015260840160405180910390fd5b83546000036100e0576b033b2e3c9fd0803ce800000084555b83600701546000036100ff576b033b2e3c9fd0803ce800000060078501555b600c840180546001600160a01b039485166001600160a01b0319909116179055600b840191909155600d909201805460ff60e81b19600168ff000000000000000160a01b03199091169390921692909217600160e01b17169055565b80356001600160a01b038116811461017257600080fd5b919050565b6000806000806080858703121561018d57600080fd5b8435935061019d6020860161015b565b9250604085013591506101b26060860161015b565b90509295919450925056fea164736f6c6343000815000a";
    //     // let addr_1 = execute(sender, ZERO_ADDR, 0, bytecode_1, 0);
    //     // debug::print(&addr_1);
    //
    //     let bytecode = x"6080604052348015600e575f80fd5b506040516019906074565b604051809103905ff0801580156031573d5f803e3d5ffd5b505f806101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff1602179055506081565b6101cf8061038b83390190565b6102fd8061008e5f395ff3fe608060405234801561000f575f80fd5b5060043610610034575f3560e01c806324d45ec3146100385780634e70b1dc14610068575b5f80fd5b610052600480360381019061004d919061016a565b610086565b60405161005f91906101b7565b60405180910390f35b61007061012d565b60405161007d91906101e8565b60405180910390f35b5f805f8054906101000a900473ffffffffffffffffffffffffffffffffffffffff1690505f60026040516100b990610255565b602060405180830381855afa1580156100d4573d5f803e3d5ffd5b5050506040513d601f19601f820116820180604052508101906100f7919061029c565b90506040518181528560048201528460248201526020816044835f87624c4b40f181519450604482016040525050505092915050565b60015481565b5f80fd5b5f819050919050565b61014981610137565b8114610153575f80fd5b50565b5f8135905061016481610140565b92915050565b5f80604083850312156101805761017f610133565b5b5f61018d85828601610156565b925050602061019e85828601610156565b9150509250929050565b6101b181610137565b82525050565b5f6020820190506101ca5f8301846101a8565b92915050565b5f819050919050565b6101e2816101d0565b82525050565b5f6020820190506101fb5f8301846101d9565b92915050565b5f81905092915050565b7f61646428696e743235362c696e743235362900000000000000000000000000005f82015250565b5f61023f601283610201565b915061024a8261020b565b601282019050919050565b5f61025f82610233565b9150819050919050565b5f819050919050565b61027b81610269565b8114610285575f80fd5b50565b5f8151905061029681610272565b92915050565b5f602082840312156102b1576102b0610133565b5b5f6102be84828501610288565b9150509291505056fea26469706673582212203ee8a7d788d7fc694e7e5103b8989b86cd692045bf1785e984bf4aa8690d199864736f6c634300081900336080604052348015600e575f80fd5b506101b38061001c5f395ff3fe608060405234801561000f575f80fd5b5060043610610029575f3560e01c8063a5f3c23b1461002d575b5f80fd5b610047600480360381019061004291906100a9565b61005d565b60405161005491906100f6565b60405180910390f35b5f818361006a919061013c565b905092915050565b5f80fd5b5f819050919050565b61008881610076565b8114610092575f80fd5b50565b5f813590506100a38161007f565b92915050565b5f80604083850312156100bf576100be610072565b5b5f6100cc85828601610095565b92505060206100dd85828601610095565b9150509250929050565b6100f081610076565b82525050565b5f6020820190506101095f8301846100e7565b92915050565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52601160045260245ffd5b5f61014682610076565b915061015183610076565b92508282019050828112155f8312168382125f8412151617156101775761017661010f565b5b9291505056fea26469706673582212201446233f6f7daec33e74aad617ebc21789cd985b3d4f31a38e7a44d7d2df5f6e64736f6c63430008190033";
    //     let addr = execute(sender, ZERO_ADDR, 0, bytecode, 0);
    //
    //     let calldata = x"24d45ec300000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002";
    //     debug::print(&addr);
    //     debug::print(&execute(sender, addr, 1, calldata, 0));
    //
    //
    //     // let bytecode_2 = x"608060405234801561001057600080fd5b506000610052576040517f08c379a0000000000000000000000000000000000000000000000000000000008152600401610049906100b4565b60405180910390fd5b6100d4565b600082825260208201905092915050565b7f6573746573747300000000000000000000000000000000000000000000000000600082015250565b600061009e600783610057565b91506100a982610068565b602082019050919050565b600060208201905081810360008301526100cd81610091565b9050919050565b6102f5806100e36000396000f3fe608060405234801561001057600080fd5b50600436106100415760003560e01c806324d45ec314610046578063410c47a0146100765780638e12aeac146100a6575b600080fd5b610060600480360381019061005b919061013b565b6100d6565b60405161006d919061018a565b60405180910390f35b610090600480360381019061008b91906101db565b6100ec565b60405161009d919061018a565b60405180910390f35b6100c060048036038101906100bb9190610208565b6100f6565b6040516100cd9190610244565b60405180910390f35b600081836100e4919061028e565b905092915050565b6000819050919050565b6000819050919050565b600080fd5b6000819050919050565b61011881610105565b811461012357600080fd5b50565b6000813590506101358161010f565b92915050565b6000806040838503121561015257610151610100565b5b600061016085828601610126565b925050602061017185828601610126565b9150509250929050565b61018481610105565b82525050565b600060208201905061019f600083018461017b565b92915050565b6000819050919050565b6101b8816101a5565b81146101c357600080fd5b50565b6000813590506101d5816101af565b92915050565b6000602082840312156101f1576101f0610100565b5b60006101ff848285016101c6565b91505092915050565b60006020828403121561021e5761021d610100565b5b600061022c84828501610126565b91505092915050565b61023e816101a5565b82525050565b60006020820190506102596000830184610235565b92915050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052601260045260246000fd5b600061029982610105565b91506102a483610105565b9250826102b4576102b361025f565b5b82820790509291505056fea2646970667358221220d6af6bbc08c9cf5e099dc59413ec5d68b5f1437cef3dd2061d02e0a76aad6fd064736f6c63430008120033";
    //     // let addr_2 = execute(sender, ZERO_ADDR, 2, bytecode_2, 0);
    //
    //     // query(sender, addr_1, x"");
    // }
    //
    #[test_only]
    fun deposit_to(addr: vector<u8>, amount: u256) acquires Account {
        let evm = account::create_account_for_test(@0x1);
        let (burn_cap, freeze_cap, mint_cap) = coin::initialize<AptosCoin>(
            &evm,
            string::utf8(b"APT"),
            string::utf8(b"APT"),
            8,
            false,
        );
        let to = account::create_account_for_test(@0xc5cb1f1ce6951226e9c46ce8d42eda1ac9774a0fef91e2910939119ef0c95568);
        let coins = coin::mint<AptosCoin>(((amount / CONVERT_BASE) as u64), &mint_cap);
        coin::register<AptosCoin>(&to);
        coin::register<AptosCoin>(&evm);
        coin::deposit(@aptos_framework, coins);

        deposit(&evm, addr, u256_to_data(amount));
        coin::destroy_freeze_cap(freeze_cap);
        coin::destroy_burn_cap(burn_cap);
        coin::destroy_mint_cap(mint_cap);
    }



    // #[test]
    // fun test_mul_mod() {
    //     // debug::print(&sdiv(18, 3));
    //     debug::print(&smod(115792089237316195423570985008687907853269984665640564039457584007913129639928, 115792089237316195423570985008687907853269984665640564039457584007913129639930));
    //     // debug::print(&add(115792089237316195423570985008687907853269984665640564039457584007913129639935, 3));
    //     // debug::print(&mul_mod(U256_MAX, U256_MAX, 14232329));
    //     // debug::print(&mul(3, U256_MAX));
    // }
    //
    // #[test]
    // fun test_opcode() acquires Account, ContractEvent{
    //     let tx = x"f885800a8404c4b40094cccccccccccccccccccccccccccccccccccccccc01a4693c613900000000000000000000000000000000000000000000000000000000000000001ba0e8ff56322287185f6afd3422a825b47bf5c1a4ccf0dc0389cdc03f7c1c32b7eaa0776b02f9f5773238d3ff36b74a123f409cd6420908d7855bbe4c8ff63e00d698";
    //     let evm = account::create_account_for_test(@0x1);
    //     let sender = x"054ecb78d0276cf182514211d0c21fe46590b654";
    //     send_tx(&evm, sender, tx, u256_to_data(0), 1);
    // }
    //
    // #[test]
    // fun test_precompile() acquires Account, ContractEvent {
    //     let framework_signer = &create_signer(@0x1);
    //     features::change_feature_flags(
    //         framework_signer, vector[features::get_sha_512_and_ripemd_160_feature(), features::get_blake2b_256_feature()], vector[]);
    //     let sender = to_32bit(x"054ecb78d0276cf182514211d0c21fe46590b654");
    //     let code = x"608060405234801561001057600080fd5b50611535806100206000396000f3fe608060405234801561001057600080fd5b506004361061009e5760003560e01c8063caa2603211610066578063caa2603214610149578063ce74602414610179578063e4614a6e14610197578063ec8b466a146101b5578063f7180826146101e55761009e565b80630743120d146100a35780633148f14f146100ad5780634849f279146100dd5780635270e2b71461010d578063a1e754ea1461012b575b600080fd5b6100ab610215565b005b6100c760048036038101906100c29190610b38565b610217565b6040516100d49190610b9a565b60405180910390f35b6100f760048036038101906100f29190610beb565b610262565b6040516101049190610cfd565b60405180910390f35b61011561030d565b6040516101229190610d33565b60405180910390f35b610133610774565b6040516101409190610d5d565b60405180910390f35b610163600480360381019061015e9190610ebe565b6107e6565b6040516101709190610f86565b60405180910390f35b61018161085a565b60405161018e9190610fe9565b60405180910390f35b61019f610931565b6040516101ac9190610d5d565b60405180910390f35b6101cf60048036038101906101ca9190611004565b6109ad565b6040516101dc9190610cfd565b60405180910390f35b6101ff60048036038101906101fa919061111f565b610a39565b60405161020c9190610d5d565b60405180910390f35b565b600060405160208152602080820152602060408201528460608201528360808201528260a082015260c05160208160c08460055afa61025557600080fd5b8051925050509392505050565b61026a610a88565b610272610aaa565b858160006004811061028757610286611168565b5b60200201818152505084816001600481106102a5576102a4611168565b5b60200201818152505083816002600481106102c3576102c2611168565b5b60200201818152505082816003600481106102e1576102e0611168565b5b60200201818152505060408260808360065afa806000810361030257600080fd5b505050949350505050565b6000807f456e9aea5e197a1f1af7a3e85a3212fa4049a3ba34c2289b4c860fc0b0c64ef360001b90506000601c905060007f9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac803882560860001b905060007f4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada60001b9050737156526fbd7a3c72969b54f64e42c10fbb768c8a73ffffffffffffffffffffffffffffffffffffffff16600185858585604051600081526020016040526040516103da94939291906111b3565b6020604051602081039080840390855afa1580156103fc573d6000803e3d6000fd5b5050506020604051035173ffffffffffffffffffffffffffffffffffffffff161461045c576040517f08c379a000000000000000000000000000000000000000000000000000000000815260040161045390611255565b60405180910390fd5b600060ff90507fa8100ae6aa1940d0b663bb31cd466142ebbdbd5187131b92d93818987832eb8960001b60028260405160200161049991906112ab565b6040516020818303038152906040526040516104b59190611302565b602060405180830381855afa1580156104d2573d6000803e3d6000fd5b5050506040513d601f19601f820116820180604052508101906104f5919061132e565b14610535576040517f08c379a000000000000000000000000000000000000000000000000000000000815260040161052c906113a7565b60405180910390fd5b600060ff905060007f2c0c45d3ecab80fe060e5f1d7057cd2f8de5e55700000000000000000000000060001b90508060038360405160200161057791906112ab565b6040516020818303038152906040526040516105939190611302565b602060405180830381855afa1580156105b0573d6000803e3d6000fd5b5050506040515160601b6bffffffffffffffffffffffff191614610609576040517f08c379a000000000000000000000000000000000000000000000000000000000815260040161060090611413565b60405180910390fd5b60006106496040518060400160405280600281526020017f61620000000000000000000000000000000000000000000000000000000000008152506107e6565b9050600281511480156106bb57507f61000000000000000000000000000000000000000000000000000000000000008160008151811061068c5761068b611168565b5b602001015160f81c60f81b7effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1916145b801561072657507f6200000000000000000000000000000000000000000000000000000000000000816001815181106106f7576106f6611168565b5b602001015160f81c60f81b7effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1916145b610765576040517f08c379a000000000000000000000000000000000000000000000000000000000815260040161075c9061147f565b60405180910390fd5b60019850505050505050505090565b60008060ff905060038160405160200161078e91906112ab565b6040516020818303038152906040526040516107aa9190611302565b602060405180830381855afa1580156107c7573d6000803e3d6000fd5b5050506040515160601b6bffffffffffffffffffffffff191691505090565b60606000825167ffffffffffffffff81111561080557610804610d93565b5b6040519080825280601f01601f1916602001820160405280156108375781602001600182028036833780820191505090505b50905082518060208301826020870160045afa61085057fe5b5080915050919050565b6000807f456e9aea5e197a1f1af7a3e85a3212fa4049a3ba34c2289b4c860fc0b0c64ef360001b90506000601c905060007f9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac803882560860001b905060007f4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada60001b9050600184848484604051600081526020016040526040516108fc94939291906111b3565b6020604051602081039080840390855afa15801561091e573d6000803e3d6000fd5b5050506020604051035194505050505090565b60008060ff905060028160405160200161094b91906112ab565b6040516020818303038152906040526040516109679190611302565b602060405180830381855afa158015610984573d6000803e3d6000fd5b5050506040513d601f19601f820116820180604052508101906109a7919061132e565b91505090565b6109b5610a88565b6109bd610acc565b84816000600381106109d2576109d1611168565b5b60200201818152505083816001600381106109f0576109ef611168565b5b6020020181815250508281600260038110610a0e57610a0d611168565b5b60200201818152505060408260608360075afa8060008103610a2f57600080fd5b5050509392505050565b60008082519050600060c082610a4f91906114ce565b14610a5957600080fd5b604051602081836020870160085afa8060008114610a7a5782519450610a7f565b600080fd5b50505050919050565b6040518060400160405280600290602082028036833780820191505090505090565b6040518060800160405280600490602082028036833780820191505090505090565b6040518060600160405280600390602082028036833780820191505090505090565b6000604051905090565b600080fd5b600080fd5b6000819050919050565b610b1581610b02565b8114610b2057600080fd5b50565b600081359050610b3281610b0c565b92915050565b600080600060608486031215610b5157610b50610af8565b5b6000610b5f86828701610b23565b9350506020610b7086828701610b23565b9250506040610b8186828701610b23565b9150509250925092565b610b9481610b02565b82525050565b6000602082019050610baf6000830184610b8b565b92915050565b6000819050919050565b610bc881610bb5565b8114610bd357600080fd5b50565b600081359050610be581610bbf565b92915050565b60008060008060808587031215610c0557610c04610af8565b5b6000610c1387828801610bd6565b9450506020610c2487828801610bd6565b9350506040610c3587828801610bd6565b9250506060610c4687828801610bd6565b91505092959194509250565b600060029050919050565b600081905092915050565b6000819050919050565b610c7b81610bb5565b82525050565b6000610c8d8383610c72565b60208301905092915050565b6000602082019050919050565b610caf81610c52565b610cb98184610c5d565b9250610cc482610c68565b8060005b83811015610cf5578151610cdc8782610c81565b9650610ce783610c99565b925050600181019050610cc8565b505050505050565b6000604082019050610d126000830184610ca6565b92915050565b60008115159050919050565b610d2d81610d18565b82525050565b6000602082019050610d486000830184610d24565b92915050565b610d5781610bb5565b82525050565b6000602082019050610d726000830184610d4e565b92915050565b600080fd5b600080fd5b6000601f19601f8301169050919050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052604160045260246000fd5b610dcb82610d82565b810181811067ffffffffffffffff82111715610dea57610de9610d93565b5b80604052505050565b6000610dfd610aee565b9050610e098282610dc2565b919050565b600067ffffffffffffffff821115610e2957610e28610d93565b5b610e3282610d82565b9050602081019050919050565b82818337600083830152505050565b6000610e61610e5c84610e0e565b610df3565b905082815260208101848484011115610e7d57610e7c610d7d565b5b610e88848285610e3f565b509392505050565b600082601f830112610ea557610ea4610d78565b5b8135610eb5848260208601610e4e565b91505092915050565b600060208284031215610ed457610ed3610af8565b5b600082013567ffffffffffffffff811115610ef257610ef1610afd565b5b610efe84828501610e90565b91505092915050565b600081519050919050565b600082825260208201905092915050565b60005b83811015610f41578082015181840152602081019050610f26565b60008484015250505050565b6000610f5882610f07565b610f628185610f12565b9350610f72818560208601610f23565b610f7b81610d82565b840191505092915050565b60006020820190508181036000830152610fa08184610f4d565b905092915050565b600073ffffffffffffffffffffffffffffffffffffffff82169050919050565b6000610fd382610fa8565b9050919050565b610fe381610fc8565b82525050565b6000602082019050610ffe6000830184610fda565b92915050565b60008060006060848603121561101d5761101c610af8565b5b600061102b86828701610bd6565b935050602061103c86828701610bd6565b925050604061104d86828701610bd6565b9150509250925092565b600067ffffffffffffffff82111561107257611071610d93565b5b602082029050602081019050919050565b600080fd5b600061109b61109684611057565b610df3565b905080838252602082019050602084028301858111156110be576110bd611083565b5b835b818110156110e757806110d38882610bd6565b8452602084019350506020810190506110c0565b5050509392505050565b600082601f83011261110657611105610d78565b5b8135611116848260208601611088565b91505092915050565b60006020828403121561113557611134610af8565b5b600082013567ffffffffffffffff81111561115357611152610afd565b5b61115f848285016110f1565b91505092915050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052603260045260246000fd5b600060ff82169050919050565b6111ad81611197565b82525050565b60006080820190506111c86000830187610d4e565b6111d560208301866111a4565b6111e26040830185610d4e565b6111ef6060830184610d4e565b95945050505050565b600082825260208201905092915050565b7f65637265636f7665720000000000000000000000000000000000000000000000600082015250565b600061123f6009836111f8565b915061124a82611209565b602082019050919050565b6000602082019050818103600083015261126e81611232565b9050919050565b60008160f81b9050919050565b600061128d82611275565b9050919050565b6112a56112a082611197565b611282565b82525050565b60006112b78284611294565b60018201915081905092915050565b600081905092915050565b60006112dc82610f07565b6112e681856112c6565b93506112f6818560208601610f23565b80840191505092915050565b600061130e82846112d1565b915081905092915050565b60008151905061132881610bbf565b92915050565b60006020828403121561134457611343610af8565b5b600061135284828501611319565b91505092915050565b7f7368613235360000000000000000000000000000000000000000000000000000600082015250565b60006113916006836111f8565b915061139c8261135b565b602082019050919050565b600060208201905081810360008301526113c081611384565b9050919050565b7f726970656d640000000000000000000000000000000000000000000000000000600082015250565b60006113fd6006836111f8565b9150611408826113c7565b602082019050919050565b6000602082019050818103600083015261142c816113f0565b9050919050565b7f64617461636f7079000000000000000000000000000000000000000000000000600082015250565b60006114696008836111f8565b915061147482611433565b602082019050919050565b600060208201905081810360008301526114988161145c565b9050919050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052601260045260246000fd5b60006114d982610b02565b91506114e483610b02565b9250826114f4576114f361149f565b5b82820690509291505056fea2646970667358221220882777d7230249bbdf4df7defbb924bbb7513dea56b8d048472fc5018b10e1b864736f6c63430008120033";
    //     let addr = execute(sender, ZERO_ADDR, 0, code, 0);
    //     debug::print(&execute(sender, addr, 1, x"5270e2b7", 0));
    // }

    #[test]
    fun test_deposit_withdraw() acquires Account {

        let sender = x"edd3bce148f5acffd4ae7589d12cf51f7e4788c6";
        let evm = account::create_account_for_test(@0x1);
        let (burn_cap, freeze_cap, mint_cap) = coin::initialize<AptosCoin>(
            &evm,
            string::utf8(b"APT"),
            string::utf8(b"APT"),
            8,
            false,
        );

        let to = account::create_account_for_test(@0xc5cb1f1ce6951226e9c46ce8d42eda1ac9774a0fef91e2910939119ef0c95568);
        let coins = coin::mint<AptosCoin>(1000000000000, &mint_cap);
        coin::register<AptosCoin>(&to);
        coin::register<AptosCoin>(&evm);
        coin::deposit(@aptos_framework, coins);

        deposit(&evm, sender, u256_to_data(10000000000000000000));

        // let tx = x"f8eb8085e8d4a5100082520894a4cd3b0eb6e5ab5d8ce4065bccd70040adab1f0080b884c7012626000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000027100000000000000000000000000000000000000000000000000000000000000020c5cb1f1ce6951226e9c46ce8d42eda1ac9774a0fef91e2910939119ef0c955688202c3a0bdbf42ff5f141f989d3b546f8a8514857d036cfccd8e0c3e56d4644e08e40ea1a03908d910179e0e1b6b4ea43b4cbdcfc21f9fb74cf3cca3adde058a062a8bebf6";
        // send_tx(&evm, sender, tx, 0, 1);

        debug::print(&coin::balance<AptosCoin>(@aptos_framework));
        debug::print(&coin::balance<AptosCoin>(@0xc5cb1f1ce6951226e9c46ce8d42eda1ac9774a0fef91e2910939119ef0c95568));
        // let coin_store_account = borrow_global<Account>(@aptos_framework);
        // debug::print(&coin_store_account.balance);


        let sender = x"8db97c7cece249c2b98bdc0226cc4c2a57bf52fc";
        deposit(&evm, sender, u256_to_data(1000000000000000000));
        // let data = x"608060405234801561001057600080fd5b5060f78061001f6000396000f3fe6080604052348015600f57600080fd5b5060043610603c5760003560e01c80633fb5c1cb1460415780638381f58a146053578063d09de08a14606d575b600080fd5b6051604c3660046083565b600055565b005b605b60005481565b60405190815260200160405180910390f35b6051600080549080607c83609b565b9190505550565b600060208284031215609457600080fd5b5035919050565b60006001820160ba57634e487b7160e01b600052601160045260246000fd5b506001019056fea2646970667358221220b7acd98dc008db06cadaea72991d3736d8dd08fbbf4bde9f69be2723a32b9be864736f6c63430008150033";
        // estimate_tx_gas(sender, data, u256_to_data(21000), u256_to_data(0), 1);
        // deposit(&evm, sender, u256_to_data(1000000000000000000));
        // let coin_store_account = borrow_global<Account>(create_resource_address(&@aptos_framework, to_32bit(sender)));
        // debug::print(&coin_store_account.balance);
        // let sender = x"749cf96d9291795a74572ef7089e34ee650dac8c";
        // let tx = x"f9605a81d086015d3ef79800830f42408080b96003615fdd610026600b82828239805160001a60731461001957fe5b30600052607381538281f3fe73000000000000000000000000000000000000000030146080604052600436106100355760003560e01c8063c49917d71461003a575b600080fd5b61004d610048366004613f08565b610063565b60405161005a919061464a565b60405180910390f35b6060600061007e83610079856101800151610170565b6103d1565b905060006100b2610092856060015161048c565b61009f866080015161048c565b6100ad876101a00151610644565b61065a565b905060006101006100c6866000015161068c565b6100d3876080015161048c565b6100e08860200151610644565b6100ed8960400151610644565b6100fb8a6101800151610170565b610767565b905060006101156101108761079d565b6109d8565b90506101458484848460405160200161013194939291906142c5565b6040516020818303038152906040526109d8565b6040516020016101559190614605565b6040516020818303038152906040529450505050505b919050565b606062ffffff82166101b6575060408051808201909152600281527f3025000000000000000000000000000000000000000000000000000000000000602082015261016b565b816000805b62ffffff8316156102065760ff8116156101d7576001016101f0565b600a62ffffff84160662ffffff166000146101f0576001015b600190910190600a62ffffff84160492506101bb565b61020e613e02565b60006005841061030357600060046102298660ff8716610b5d565b1015610236576001610239565b60005b60ff908116915061024d9085166001610b5d565b610258866005610b5d565b106102845761027f61026e60ff86166001610b5d565b610279876005610b5d565b90610b5d565b610287565b60005b60ff8516608085018190529092506102a6906001906102799085610bba565b60ff90811660a085015260808401516102cd9183916102c791166001610b5d565b90610bba565b60ff90811660408501526102f59082906102c7906102ee9088166001610bba565b8590610bba565b60ff16602084015250610373565b61030e600585610b5d565b60026080840181905290915061032c90600190610279908490610bba565b60ff90811660a084015261034e906103479085166002610bba565b8290610bba565b60ff1660208301819052610363906002610b5d565b60ff166040830152600160c08301525b6103926103838560ff8616610b5d565b62ffffff891690600a0a610c14565b8252600160e0830152600484116103aa5760006103b5565b6103b5846004610b5d565b60ff1660608301526103c682610c7b565b979650505050505050565b6060816103e1846060015161048c565b6103ee856080015161048c565b6104278660e00151156104065786610120015161040d565b8661010001515b8761016001518860c001518960a001518a60e00151610ea7565b6104608760e001511561043f57876101000151610446565b8761012001515b8861016001518960c001518a60a001518b60e00151610ea7565b6040516020016104749594939291906143ec565b60405160208183030381529060405290505b92915050565b6060816000805b82518160ff1610156104f057828160ff16815181106104ae57fe5b6020910101517fff0000000000000000000000000000000000000000000000000000000000000016601160f91b14156104e8576001909101905b600101610493565b5060ff81161561063c5760008160ff1683510167ffffffffffffffff8111801561051957600080fd5b506040519080825280601f01601f191660200182016040528015610544576020820181803683370190505b5090506000805b84518160ff16101561062f57848160ff168151811061056657fe5b6020910101517fff0000000000000000000000000000000000000000000000000000000000000016601160f91b14156105e4577f5c000000000000000000000000000000000000000000000000000000000000008383806001019450815181106105cc57fe5b60200101906001600160f81b031916908160001a9053505b848160ff16815181106105f357fe5b602001015160f81c60f81b83838060010194508151811061061057fe5b60200101906001600160f81b031916908160001a90535060010161054b565b508194505050505061016b565b509192915050565b60606104866001600160a01b0383166014610fd1565b6060838383866040516020016106739493929190614179565b60405160208183030381529060405290505b9392505050565b6060816106b157506040805180820190915260018152600360fc1b602082015261016b565b8160005b81156106c957600101600a820491506106b5565b60008167ffffffffffffffff811180156106e257600080fd5b506040519080825280601f01601f19166020018201604052801561070d576020820181803683370190505b50859350905060001982015b831561075e57600a840660300160f81b8282806001900393508151811061073c57fe5b60200101906001600160f81b031916908160001a905350600a84049350610719565b50949350505050565b606083858484896040516020016107829594939291906144ed565b60405160208183030381529060405290505b95945050505050565b60606000604051806102a001604052806107ba8560200151610644565b81526020016107cc8560400151610644565b8152602001846101a001516001600160a01b031681526020018460600151815260200184608001518152602001610807856101800151610170565b815260200184610100015160020b815260200184610120015160020b815260200184610160015160020b8152602001610850856101000151866101200151876101400151611159565b60000b81526020018460000151815260200161087a85602001516001600160a01b03166088611190565b815260200161089785604001516001600160a01b03166088611190565b81526020016108b485602001516001600160a01b03166000611190565b81526020016108d185604001516001600160a01b03166000611190565b81526020016109046108f686602001516001600160a01b03166010886000015161119f565b600060ff60106101126111bf565b815260200161093761092986604001516001600160a01b03166010886000015161119f565b600060ff60646101e46111bf565b815260200161095c6108f686602001516001600160a01b03166020886000015161119f565b815260200161098161092986604001516001600160a01b03166020886000015161119f565b81526020016109a66108f686602001516001600160a01b03166030886000015161119f565b81526020016109cb61092986604001516001600160a01b03166030886000015161119f565b9052905061068581611207565b60608151600014156109f9575060408051602081019091526000815261016b565b600060405180606001604052806040815260200161526b60409139905060006003845160020181610a2657fe5b04600402905060008160200167ffffffffffffffff81118015610a4857600080fd5b506040519080825280601f01601f191660200182016040528015610a73576020820181803683370190505b509050818152600183018586518101602084015b81831015610ae15760039283018051603f601282901c811687015160f890811b8552600c83901c8216880151811b6001860152600683901c8216880151811b60028601529116860151901b93820193909352600401610a87565b600389510660018114610afb5760028114610b2757610b4f565b7f3d3d000000000000000000000000000000000000000000000000000000000000600119830152610b4f565b7f3d000000000000000000000000000000000000000000000000000000000000006000198301525b509398975050505050505050565b600082821115610bb4576040805162461bcd60e51b815260206004820152601e60248201527f536166654d6174683a207375627472616374696f6e206f766572666c6f770000604482015290519081900360640190fd5b50900390565b600082820183811015610685576040805162461bcd60e51b815260206004820152601b60248201527f536166654d6174683a206164646974696f6e206f766572666c6f770000000000604482015290519081900360640190fd5b6000808211610c6a576040805162461bcd60e51b815260206004820152601a60248201527f536166654d6174683a206469766973696f6e206279207a65726f000000000000604482015290519081900360640190fd5b818381610c7357fe5b049392505050565b60606000826020015160ff1667ffffffffffffffff81118015610c9d57600080fd5b506040519080825280601f01601f191660200182016040528015610cc8576020820181803683370190505b5090508260e0015115610d1e577f250000000000000000000000000000000000000000000000000000000000000081600183510381518110610d0657fe5b60200101906001600160f81b031916908160001a9053505b8260c0015115610d7b57600360fc1b81600081518110610d3a57fe5b60200101906001600160f81b031916908160001a905350601760f91b81600181518110610d6357fe5b60200101906001600160f81b031916908160001a9053505b608083015160ff165b60a0840151610d979060ff166001610bba565b811015610dce57603060f81b828281518110610daf57fe5b60200101906001600160f81b031916908160001a905350600101610d84565b505b825115610486576000836060015160ff16118015610dfb5750826060015160ff16836040015160ff16145b15610e3e5760408301805160ff600019820181169092528251601760f91b92849216908110610e2657fe5b60200101906001600160f81b031916908160001a9053505b8251610e5090603090600a9006610bba565b60f81b818460400180518091906001900360ff1660ff1681525060ff1681518110610e7757fe5b60200101906001600160f81b031916908160001a905350600a8360000181815181610e9e57fe5b04905250610dd0565b606084600281900b620d89e71981610ebb57fe5b050260020b8660020b1415610f15578115610ef1576040518060400160405280600381526020016209a82b60eb1b815250610f0e565b6040518060400160405280600381526020016226a4a760e91b8152505b9050610794565b84600281900b620d89e881610f2657fe5b050260020b8660020b1415610f7c578115610f5c576040518060400160405280600381526020016226a4a760e91b815250610f0e565b5060408051808201909152600381526209a82b60eb1b6020820152610794565b6000610f8787611496565b90508215610fbe57610fbb78010000000000000000000000000000000000000000000000006001600160a01b038316610c14565b90505b610fc98186866117e4565b915050610794565b606060008260020260020167ffffffffffffffff81118015610ff257600080fd5b506040519080825280601f01601f19166020018201604052801561101d576020820181803683370190505b509050600360fc1b8160008151811061103257fe5b60200101906001600160f81b031916908160001a9053507f78000000000000000000000000000000000000000000000000000000000000008160018151811061107757fe5b60200101906001600160f81b031916908160001a905350600160028402015b6001811115611105577f303132333435363738396162636465660000000000000000000000000000000085600f16601081106110ce57fe5b1a60f81b8282815181106110de57fe5b60200101906001600160f81b031916908160001a90535060049490941c9360001901611096565b508315610685576040805162461bcd60e51b815260206004820181905260248201527f537472696e67733a20686578206c656e67746820696e73756666696369656e74604482015290519081900360640190fd5b60008360020b8260020b12156111725750600019610685565b8260020b8260020b131561118857506001610685565b506000610685565b606061068583831c60036119b2565b600060ff826111ae8686611a79565b02816111b657fe5b06949350505050565b60606111fd6111f8846102c76111d5888a610b5d565b6111f26111e2888a610b5d565b6111ec8d8d610b5d565b90611a80565b90610c14565b61068c565b9695505050505050565b606061121282611ad9565b61122e836000015184602001518560600151866080015161218d565b611245846060015185608001518660a001516124b8565b6112638560c001518660e00151876101000151886101200151612608565b61128361127487610140015161068c565b8760c001518860e0015161295b565b6112968761014001518860400151612d8c565b6040516020018087805190602001908083835b602083106112c85780518252601f1990920191602091820191016112a9565b51815160209384036101000a600019018019909216911617905289519190930192890191508083835b602083106113105780518252601f1990920191602091820191016112f1565b51815160209384036101000a600019018019909216911617905288519190930192880191508083835b602083106113585780518252601f199092019160209182019101611339565b51815160209384036101000a600019018019909216911617905287519190930192870191508083835b602083106113a05780518252601f199092019160209182019101611381565b51815160209384036101000a600019018019909216911617905286519190930192860191508083835b602083106113e85780518252601f1990920191602091820191016113c9565b51815160209384036101000a600019018019909216911617905285519190930192850191508083835b602083106114305780518252601f199092019160209182019101611411565b5181516020939093036101000a60001901801990911692169190911790527f3c2f7376673e000000000000000000000000000000000000000000000000000092019182525060408051808303601919018152600690920190529998505050505050505050565b60008060008360020b126114ad578260020b6114b5565b8260020b6000035b9050620d89e881111561150f576040805162461bcd60e51b815260206004820152600160248201527f5400000000000000000000000000000000000000000000000000000000000000604482015290519081900360640190fd5b60006001821661152357600160801b611535565b6ffffcb933bd6fad37aa2d162d1a5940015b70ffffffffffffffffffffffffffffffffff1690506002821615611569576ffff97272373d413259a46990580e213a0260801c5b6004821615611588576ffff2e50f5f656932ef12357cf3c7fdcc0260801c5b60088216156115a7576fffe5caca7e10e4e61c3624eaa0941cd00260801c5b60108216156115c6576fffcb9843d60f6159c9db58835c9266440260801c5b60208216156115e5576fff973b41fa98c081472e6896dfb254c00260801c5b6040821615611604576fff2ea16466c96a3843ec78b326b528610260801c5b6080821615611623576ffe5dee046a99a2a811c461f1969c30530260801c5b610100821615611643576ffcbe86c7900a88aedcffc83b479aa3a40260801c5b610200821615611663576ff987a7253ac413176f2b074cf7815e540260801c5b610400821615611683576ff3392b0822b70005940c7a398e4b70f30260801c5b6108008216156116a3576fe7159475a2c29b7443b29c7fa6e889d90260801c5b6110008216156116c3576fd097f3bdfd2022b8845ad8f792aa58250260801c5b6120008216156116e3576fa9f746462d870fdf8a65dc1f90e061e50260801c5b614000821615611703576f70d869a156d2a1b890bb3df62baf32f70260801c5b618000821615611723576f31be135f97d08fd981231505542fcfa60260801c5b62010000821615611744576f09aa508b5b7a84e1c677de54f3e99bc90260801c5b62020000821615611764576e5d6af8dedb81196699c329225ee6040260801c5b62040000821615611783576d2216e584f5fa1ea926041bedfe980260801c5b620800008216156117a0576b048a170391f7dc42444e8fa20260801c5b60008460020b13156117bb5780600019816117b757fe5b0490505b6401000000008106156117cf5760016117d2565b60005b60ff16602082901c0192505050919050565b606060006117f3858585612e04565b9050600061180b828368010000000000000000612f06565b90506c010000000000000000000000008210801561184c576118458272047bf19673df52e37f2410011d100000000000600160801b612f06565b9150611861565b61185e82620186a0600160801b612f06565b91505b8160005b811561187957600101600a82049150611865565b6000190160008061188a8684612fb5565b91509150801561189b576001909201915b6118a3613e02565b8515611910576118c26118ba602b60ff8716610b5d565b600790610bba565b60ff9081166020830152600260808301526118e8906001906102c790602b908816610b5d565b60ff90811660a0830152602082015161190391166001610b5d565b60ff166040820152611987565b60098460ff16106119595761192960ff85166004610b5d565b60ff166020820181905260056080830152611945906001610b5d565b60ff1660a082015260046040820152611987565b6006602082015260056040820181905261197e906001906102c79060ff881690610b5d565b60ff1660608201525b82815285151560c0820152600060e08201526119a281610c7b565b9c9b505050505050505050505050565b606060008260020267ffffffffffffffff811180156119d057600080fd5b506040519080825280601f01601f1916602001820160405280156119fb576020820181803683370190505b5080519091505b8015611a71577f303132333435363738396162636465660000000000000000000000000000000085600f1660108110611a3757fe5b1a60f81b826001830381518110611a4a57fe5b60200101906001600160f81b031916908160001a90535060049490941c9360001901611a02565b509392505050565b1c60ff1690565b600082611a8f57506000610486565b82820282848281611a9c57fe5b04146106855760405162461bcd60e51b815260040180806020018281038252602181526020018061548a6021913960400191505060405180910390fd5b6060611b6e82610160015160405160200180806150446081913960810182805190602001908083835b60208310611b215780518252601f199092019160209182019101611b02565b6001836020036101000a038019825116818451168082178552505050505050905001806813979f1e17b9bb339f60b91b8152506009019150506040516020818303038152906040526109d8565b611cda836101e001518461020001518561018001516040516020018080614b816063913960630184805190602001908083835b60208310611bc05780518252601f199092019160209182019101611ba1565b51815160209384036101000a600019018019909216911617905265272063793d2760d01b919093019081528551600690910192860191508083835b60208310611c1a5780518252601f199092019160209182019101611bfb565b51815160209384036101000a60001901801990921691161790527f2720723d273132307078272066696c6c3d272300000000000000000000000000919093019081528451601390910192850191508083835b60208310611c8b5780518252601f199092019160209182019101611c6c565b6001836020036101000a038019825116818451168082178552505050505050905001806813979f1e17b9bb339f60b91b81525060090193505050506040516020818303038152906040526109d8565b611d2b846102200151856102400151866101a001516040516020018080614b8160639139606301848051906020019080838360208310611bc05780518252601f199092019160209182019101611ba1565b611e4a856102600151866102800151876101c001516040516020018080614b816063913960630184805190602001908083835b60208310611d7d5780518252601f199092019160209182019101611d5e565b51815160209384036101000a600019018019909216911617905265272063793d2760d01b919093019081528551600690910192860191508083835b60208310611dd75780518252601f199092019160209182019101611db8565b51815160001960209485036101000a019081169019919091161790527f2720723d273130307078272066696c6c3d272300000000000000000000000000939091019283528451601390930192908501915080838360208310611c8b5780518252601f199092019160209182019101611c6c565b6101608601516040516020018060566148fc8239605601602c6152ab82397f3c646566733e0000000000000000000000000000000000000000000000000000602c820152603201604b614ff98239604b0186805190602001908083835b60208310611ec65780518252601f199092019160209182019101611ea7565b6001836020036101000a03801982511681845116808217855250505050505090500180615b31603e9139603e0185805190602001908083835b60208310611f1e5780518252601f199092019160209182019101611eff565b6001836020036101000a038019825116818451168082178552505050505050905001806150c5603e9139603e0184805190602001908083835b60208310611f765780518252601f199092019160209182019101611f57565b5181516020939093036101000a60001901801990911692169190911790527f22202f3e00000000000000000000000000000000000000000000000000000000920191825250600401603b6147f48239603b0183805190602001908083835b60208310611ff35780518252601f199092019160209182019101611fd4565b6001836020036101000a03801982511681845116808217855250505050505090500180614c4160999139609901607f6156e28239607f016088615aa982396088016041614cda8239604101605d615c698239605d01607261578e8239607201604961475d823960490160be614f3b823960be016071614a0d8239607101607561562582396075016066614d1b823960660160a46152d7823960a4016085615b6f82397f3c6720636c69702d706174683d2275726c2823636f726e65727329223e00000060858201527f3c726563742066696c6c3d22000000000000000000000000000000000000000060a2820152825160ae9091019060208401908083835b602083106121115780518252601f1990920191602091820191016120f2565b6001836020036101000a03801982511681845116808217855250505050505090500180614d8160319139603101604e6147a68239604e01605d614be48239605d01604161522a8239604101605261510382396052016075615bf48239607501955050505050506040516020818303038152906040529050919050565b60608382858488878a896040516020018080615d4c60259139602501607d614ebe8239607d0189805190602001908083835b602083106121de5780518252601f1990920191602091820191016121bf565b51815160209384036101000a600019018019909216911617905264010714051160dd1b919093019081528a516005909101928b0191508083835b602083106122375780518252601f199092019160209182019101612218565b6001836020036101000a03801982511681845116808217855250505050505090500180614db2607991396079016086615cc6823960860187805190602001908083835b602083106122995780518252601f19909201916020918201910161227a565b51815160209384036101000a600019018019909216911617905264010714051160dd1b919093019081528851600590910192890191508083835b602083106122f25780518252601f1990920191602091820191016122d3565b6001836020036101000a0380198251168184511680821785525050505050509050018061498860859139608501607b6159178239607b0185805190602001908083835b602083106123545780518252601f199092019160209182019101612335565b51815160209384036101000a600019018019909216911617905264010714051160dd1b919093019081528651600590910192870191508083835b602083106123ad5780518252601f19909201916020918201910161238e565b6001836020036101000a03801982511681845116808217855250505050505090500180614ad2605d9139605d0160a3615582823960a30183805190602001908083835b6020831061240f5780518252601f1990920191602091820191016123f0565b51815160209384036101000a600019018019909216911617905264010714051160dd1b919093019081528451600590910192850191508083835b602083106124685780518252601f199092019160209182019101612449565b6001836020036101000a038019825116818451168082178552505050505050905001806146d2608b9139608b01985050505050505050506040516020818303038152906040529050949350505050565b6060838383604051602001808061482f60cd913960cd0184805190602001908083835b602083106124fa5780518252601f1990920191602091820191016124db565b6001836020036101000a03801982511681845116808217855250505050505090500180602f60f81b81525060010183805190602001908083835b602083106125535780518252601f199092019160209182019101612534565b6001836020036101000a03801982511681845116808217855250505050505090500180615ef56077913960770182805190602001908083835b602083106125ab5780518252601f19909201916020918201910161258c565b5181516020939093036101000a60001901801990911692169190911790526a1e17ba32bc3a1f1e17b39f60a91b920191825250600b016073615d958239607301935050505060405160208183030381529060405290509392505050565b606060008260000b60011461269a578260000b6000191461265e576040518060400160405280600581526020017f236e6f6e65000000000000000000000000000000000000000000000000000000815250612695565b6040518060400160405280600a81526020017f23666164652d646f776e000000000000000000000000000000000000000000008152505b6126d1565b6040518060400160405280600881526020017f23666164652d75700000000000000000000000000000000000000000000000008152505b905060006126e0878787613026565b9050818183836126ef88613274565b60405160200180807f3c67206d61736b3d2275726c2800000000000000000000000000000000000000815250600d0186805190602001908083835b602083106127495780518252601f19909201916020918201910161272a565b5181516020939093036101000a600019018019909116921691909117905261149160f11b920191825250600201607761537b823960770185805190602001908083835b602083106127ab5780518252601f19909201916020918201910161278c565b6001836020036101000a03801982511681845116808217855250505050505090500180614a7e60549139605401807f3c2f673e3c67206d61736b3d2275726c2800000000000000000000000000000081525060110184805190602001908083835b6020831061282b5780518252601f19909201916020918201910161280c565b5181516020939093036101000a600019018019909116921691909117905261149160f11b92019182525060020160296153f2823960290160456154458239604501807f3c7061746820643d22000000000000000000000000000000000000000000000081525060090183805190602001908083835b602083106128bf5780518252601f1990920191602091820191016128a0565b6001836020036101000a0380198251168184511680821785525050505050509050018061569a6048913960480182805190602001908083835b602083106129175780518252601f1990920191602091820191016128f8565b6001836020036101000a0380198251168184511680821785525050505050509050019550505050505060405160208183030381529060405292505050949350505050565b6060600061296884613748565b9050600061297584613748565b865183518251929350600490910191600a91820191016000806129988a8a613852565b915091506129ab8560040160070261068c565b8b6129bb8660040160070261068c565b896129cb8760040160070261068c565b8a87876040516020018080615761602d9139602d01806c1e3932b1ba103bb4b23a341e9160991b815250600d0189805190602001908083835b60208310612a235780518252601f199092019160209182019101612a04565b6001836020036101000a03801982511681845116808217855250505050505090500180615155603d9139603d01608d615e088239608d0188805190602001908083835b60208310612a855780518252601f199092019160209182019101612a66565b5181516020939093036101000a60001901801990911692169190911790526a1e17ba32bc3a1f1e17b39f60a91b920191825250600b01602d615fa48239602d01806c1e3932b1ba103bb4b23a341e9160991b815250600d0187805190602001908083835b60208310612b085780518252601f199092019160209182019101612ae9565b6001836020036101000a03801982511681845116808217855250505050505090500180615155603d9139603d016093614e2b823960930186805190602001908083835b60208310612b6a5780518252601f199092019160209182019101612b4b565b5181516020939093036101000a60001901801990911692169190911790526a1e17ba32bc3a1f1e17b39f60a91b920191825250600b01602d614b2f8239602d01806c1e3932b1ba103bb4b23a341e9160991b815250600d0185805190602001908083835b60208310612bed5780518252601f199092019160209182019101612bce565b6001836020036101000a03801982511681845116808217855250505050505090500180615155603d9139603d016093615992823960930184805190602001908083835b60208310612c4f5780518252601f199092019160209182019101612c30565b6001836020036101000a03801982511681845116808217855250505050505090500180615f6c603891396038016060615e958239606001606461551e82396064016025614b5c823960250183805190602001908083835b60208310612cc55780518252601f199092019160209182019101612ca6565b51815160209384036101000a60001901801990921691161790527f70782c2000000000000000000000000000000000000000000000000000000000919093019081528451600490910192850191508083835b60208310612d365780518252601f199092019160209182019101612d17565b6001836020036101000a0380198251168184511680821785525050505050509050018061495260369139603601985050505050505050506040516020818303038152906040529750505050505050509392505050565b6060612d988383613c83565b15612dee5760405160200180608d61588a8239608d0160736154ab823960730160716151b98239607101608a6158008239608a016084615a25823960840190506040516020818303038152906040529050610486565b5060408051602081019091526000815292915050565b600080612e1f612e1a60ff868116908616613ce6565b613d4b565b9050600081118015612e32575060128111155b15612ef3578260ff168460ff161115612e9c57612e66612e53826002610c14565b6001600160a01b03871690600a0a611a80565b91506002810660011415612e9757612e94827003298b075b4b6a5240945790619b37fd4a600160801b612f06565b91505b612eee565b612ebd612eaa826002610c14565b6001600160a01b03871690600a0a610c14565b91506002810660011415612eee57612eeb82600160801b7003298b075b4b6a5240945790619b37fd4a612f06565b91505b611a71565b50506001600160a01b0390921692915050565b6000808060001985870986860292508281109083900303905080612f3c5760008411612f3157600080fd5b508290049050610685565b808411612f4857600080fd5b6000848688096000868103871696879004966002600389028118808a02820302808a02820302808a02820302808a02820302808a02820302808a02909103029181900381900460010186841190950394909402919094039290920491909117919091029150509392505050565b600080600060058460ff161115612fdd57612fda8560ff600419870116600a0a610c14565b94505b60006004600a8706119050612ff386600a610c14565b95508015613002578560010195505b85620186a0141561301857600a86049550600191505b5084925090505b9250929050565b606060008260020b85850360020b8161303b57fe5b05905060048160020b13613086576040518060400160405280601a81526020017f4d312031433431203431203130352031303520313435203134350000000000008152509150611a71565b60088160020b136130ce576040518060400160405280601981526020017f4d312031433333203439203937203131332031343520313435000000000000008152509150611a71565b60108160020b13613116576040518060400160405280601981526020017f4d312031433333203537203839203131332031343520313435000000000000008152509150611a71565b60208160020b1361315e576040518060400160405280601981526020017f4d312031433235203635203831203132312031343520313435000000000000008152509150611a71565b60408160020b136131a6576040518060400160405280601981526020017f4d312031433137203733203733203132392031343520313435000000000000008152509150611a71565b60808160020b136131ee576040518060400160405280601881526020017f4d312031433920383120363520313337203134352031343500000000000000008152509150611a71565b6101008160020b13613237576040518060400160405280601a81526020017f4d31203143312038392035372e352031343520313435203134350000000000008152509150611a71565b505060408051808201909152601881527f4d3120314331203937203439203134352031343520313435000000000000000060208201529392505050565b604080518082018252600281527f37330000000000000000000000000000000000000000000000000000000000006020808301919091528251808401845260038082527f313930000000000000000000000000000000000000000000000000000000000082840152845180860186528181527f32313700000000000000000000000000000000000000000000000000000000008185015285518087019096529085527f3333340000000000000000000000000000000000000000000000000000000000928501929092526060939091906001600087900b148061335b57508560000b600019145b15613552578560000b600019146133725781613374565b835b8660000b600019146133865781613388565b835b8760000b6000191461339a578361339c565b855b8860000b600019146133ae57836133b0565b855b60405160200180806b1e31b4b931b6329031bc1e9160a11b815250600c0185805190602001908083835b602083106133f95780518252601f1990920191602091820191016133da565b51815160209384036101000a600019018019909216911617905267383c111031bc9e9160c11b919093019081528651600890910192870191508083835b602083106134555780518252601f199092019160209182019101613436565b6001836020036101000a038019825116818451168082178552505050505050905001806151926027913960270183805190602001908083835b602083106134ad5780518252601f19909201916020918201910161348e565b51815160209384036101000a600019018019909216911617905267383c111031bc9e9160c11b919093019081528451600890910192850191508083835b602083106135095780518252601f1990920191602091820191016134ea565b6001836020036101000a0380198251168184511680821785525050505050509050018061541b602a9139602a01945050505050604051602081830303815290604052945061373f565b8383838360405160200180806b1e31b4b931b6329031bc1e9160a11b815250600c0185805190602001908083835b6020831061359f5780518252601f199092019160209182019101613580565b51815160209384036101000a600019018019909216911617905267383c111031bc9e9160c11b919093019081528651600890910192870191508083835b602083106135fb5780518252601f1990920191602091820191016135dc565b51815160209384036101000a60001901801990921691161790527f70782220723d22347078222066696c6c3d22776869746522202f3e0000000000919093019081526b1e31b4b931b6329031bc1e9160a11b601b8201528551602790910192860191508083835b602083106136815780518252601f199092019160209182019101613662565b51815160209384036101000a600019018019909216911617905267383c111031bc9e9160c11b919093019081528451600890910192850191508083835b602083106136dd5780518252601f1990920191602091820191016136be565b6001836020036101000a038019825116818451168082178552505050505050905001807f70782220723d22347078222066696c6c3d22776869746522202f3e0000000000815250601b0194505050505060405160208183030381529060405294505b50505050919050565b6060600060405180602001604052806000815250905060008360020b121561378e5782600019029250604051806040016040528060018152602001602d60f81b81525090505b8061379b8460020b61068c565b6040516020018083805190602001908083835b602083106137cd5780518252601f1990920191602091820191016137ae565b51815160209384036101000a600019018019909216911617905285519190930192850191508083835b602083106138155780518252601f1990920191602091820191016137f6565b6001836020036101000a03801982511681845116808217855250505050505090500192505050604051602081830303815290604052915050919050565b60608060006002858501810b0590506201e847198160020b12156138ca57604051806040016040528060018152602001600760fb1b8152506040518060400160405280600181526020017f3700000000000000000000000000000000000000000000000000000000000000815250925092505061301f565b620124f7198160020b121561393357604051806040016040528060018152602001600760fb1b8152506040518060400160405280600481526020017f31302e3500000000000000000000000000000000000000000000000000000000815250925092505061301f565b6161a7198160020b121561399b57604051806040016040528060018152602001600760fb1b8152506040518060400160405280600581526020017f31342e3235000000000000000000000000000000000000000000000000000000815250925092505061301f565b611387198160020b1215613a04576040518060400160405280600281526020017f313000000000000000000000000000000000000000000000000000000000000081525060405180604001604052806002815260200161062760f31b815250925092505061301f565b60008160020b1215613a6b576040518060400160405280600281526020017f313100000000000000000000000000000000000000000000000000000000000081525060405180604001604052806002815260200161323160f01b815250925092505061301f565b6113888160020b1215613aee576040518060400160405280600281526020017f31330000000000000000000000000000000000000000000000000000000000008152506040518060400160405280600281526020017f3233000000000000000000000000000000000000000000000000000000000000815250925092505061301f565b6161a88160020b1215613b71576040518060400160405280600281526020017f31350000000000000000000000000000000000000000000000000000000000008152506040518060400160405280600281526020017f3235000000000000000000000000000000000000000000000000000000000000815250925092505061301f565b620124f88160020b1215613bda5760405180604001604052806002815260200161062760f31b8152506040518060400160405280600281526020017f3236000000000000000000000000000000000000000000000000000000000000815250925092505061301f565b6201e8488160020b1215613c285760405180604001604052806002815260200161323160f01b81525060405180604001604052806002815260200161323760f01b815250925092505061301f565b6040518060400160405280600281526020017f323400000000000000000000000000000000000000000000000000000000000081525060405180604001604052806002815260200161323760f01b815250925092505061301f565b6040805160208082018590526bffffffffffffffffffffffff19606085901b16828401528251603481840301815260549092019092528051910120600090613cca84613d62565b60020260010160ff1660001981613cdd57fe5b04119392505050565b6000818303818312801590613cfb5750838113155b80613d105750600083128015613d1057508381135b6106855760405162461bcd60e51b8152600401808060200182810382526024815260200180615d716024913960400191505060405180910390fd5b600080821215613d5e5781600003610486565b5090565b6000808211613d7057600080fd5b600160801b8210613d8357608091821c91015b680100000000000000008210613d9b57604091821c91015b6401000000008210613daf57602091821c91015b620100008210613dc157601091821c91015b6101008210613dd257600891821c91015b60108210613de257600491821c91015b60048210613df257600291821c91015b6002821061016b57600101919050565b6040805161010081018252600080825260208201819052918101829052606081018290526080810182905260a0810182905260c0810182905260e081019190915290565b80356001600160a01b038116811461016b57600080fd5b8035801515811461016b57600080fd5b8035600281900b811461016b57600080fd5b600082601f830112613e8f578081fd5b813567ffffffffffffffff811115613ea357fe5b613eb6601f8201601f191660200161467d565b818152846020838601011115613eca578283fd5b816020850160208301379081016020019190915292915050565b803562ffffff8116811461016b57600080fd5b803560ff8116811461016b57600080fd5b600060208284031215613f19578081fd5b813567ffffffffffffffff80821115613f30578283fd5b81840191506101c0808387031215613f46578384fd5b613f4f8161467d565b905082358152613f6160208401613e46565b6020820152613f7260408401613e46565b6040820152606083013582811115613f88578485fd5b613f9487828601613e7f565b606083015250608083013582811115613fab578485fd5b613fb787828601613e7f565b608083015250613fc960a08401613ef7565b60a0820152613fda60c08401613ef7565b60c0820152613feb60e08401613e5d565b60e08201526101009150614000828401613e6d565b828201526101209150614014828401613e6d565b828201526101409150614028828401613e6d565b82820152610160915061403c828401613e6d565b828201526101809150614050828401613ee4565b828201526101a09150614064828401613e46565b91810191909152949350505050565b600081516140858185602086016146a1565b9290920192915050565b7fe29aa0efb88f20444953434c41494d45523a204475652064696c6967656e636581527f20697320696d7065726174697665207768656e20617373657373696e6720746860208201527f6973204e46542e204d616b65207375726520746f6b656e20616464726573736560408201527f73206d617463682074686520657870656374656420746f6b656e732c2061732060608201527f746f6b656e2073796d626f6c73206d617920626520696d6974617465642e00006080820152609e0190565b7f5c6e5c6e00000000000000000000000000000000000000000000000000000000815260040190565b60007f54686973204e465420726570726573656e74732061206c69717569646974792082527f706f736974696f6e20696e206120556e69737761702056332000000000000000602083015285516141d7816039850160208a016146a1565b602d60f81b60399184019182015285516141f881603a840160208a016146a1565b7f20706f6f6c2e2000000000000000000000000000000000000000000000000000603a92909101918201527f546865206f776e6572206f662074686973204e46542063616e206d6f6469667960418201527f206f722072656465656d2074686520706f736974696f6e2e5c6e00000000000060618201527f5c6e506f6f6c20416464726573733a2000000000000000000000000000000000607b82015284516142a881608b8401602089016146a1565b612e3760f11b608b92909101918201526103c6608d820185614073565b60007f7b226e616d65223a220000000000000000000000000000000000000000000000825285516142fd816009850160208a016146a1565b7f222c20226465736372697074696f6e223a220000000000000000000000000000600991840191820152855161433a81601b840160208a016146a1565b855191019061435081601b8401602089016146a1565b7f222c2022696d616765223a202200000000000000000000000000000000000000601b92909101918201527f646174613a696d6167652f7376672b786d6c3b6261736536342c000000000000602882015283516143b48160428401602088016146a1565b7f227d000000000000000000000000000000000000000000000000000000000000604292909101918201526044019695505050505050565b60007f556e6973776170202d20000000000000000000000000000000000000000000008252865161442481600a850160208b016146a1565b80830190507f202d20000000000000000000000000000000000000000000000000000000000080600a830152875161446381600d850160208c016146a1565b602f60f81b600d9390910192830152865161448581600e850160208b016146a1565b600e92019182015284516144a08160118401602089016146a1565b7f3c3e0000000000000000000000000000000000000000000000000000000000006011929091019182015283516144de8160138401602088016146a1565b01601301979650505050505050565b60007f20416464726573733a2000000000000000000000000000000000000000000000808352875161452681600a860160208c016146a1565b612e3760f11b600a91850191820152875161454881600c840160208c016146a1565b01600c810191909152855190614565826016830160208a016146a1565b8181019150507f5c6e46656520546965723a200000000000000000000000000000000000000000601682015284516145a48160228401602089016146a1565b7f5c6e546f6b656e2049443a2000000000000000000000000000000000000000006022929091019182015283516145e281602e8401602088016146a1565b6145f86145f3602e83850101614150565b61408f565b9998505050505050505050565b60007f646174613a6170706c69636174696f6e2f6a736f6e3b6261736536342c0000008252825161463d81601d8501602087016146a1565b91909101601d0192915050565b60006020825282518060208401526146698160408501602087016146a1565b601f01601f19169190910160400192915050565b60405181810167ffffffffffffffff8111828210171561469957fe5b604052919050565b60005b838110156146bc5781810151838201526020016146a4565b838111156146cb576000848401525b5050505056fe203c616e696d6174652061646469746976653d2273756d22206174747269627574654e616d653d2273746172744f6666736574222066726f6d3d2230252220746f3d22313030252220626567696e3d22307322206475723d223330732220726570656174436f756e743d22696e646566696e69746522202f3e3c2f74657874506174683e3c2f746578743e3c73746f70206f66667365743d222e39222073746f702d636f6c6f723d227768697465222073746f702d6f7061636974793d223022202f3e3c2f6c696e6561724772616469656e743e3c72656374207374796c653d2266696c7465723a2075726c28236631292220783d223070782220793d22307078222077696474683d22323930707822206865696768743d22353030707822202f3e3c6665496d61676520726573756c743d2270332220786c696e6b3a687265663d22646174613a696d6167652f7376672b786d6c3b6261736536342c3c67206d61736b3d2275726c2823666164652d73796d626f6c29223e3c726563742066696c6c3d226e6f6e652220783d223070782220793d22307078222077696474683d22323930707822206865696768743d22323030707822202f3e203c7465787420793d22373070782220783d2233327078222066696c6c3d2277686974652220666f6e742d66616d696c793d2227436f7572696572204e6577272c206d6f6e6f73706163652220666f6e742d7765696768743d223230302220666f6e742d73697a653d2233367078223e3c7376672077696474683d2232393022206865696768743d22353030222076696577426f783d2230203020323930203530302220786d6c6e733d22687474703a2f2f7777772e77332e6f72672f323030302f7376672270782c2030707829222063783d22307078222063793d223070782220723d22347078222066696c6c3d227768697465222f3e3c2f673e203c616e696d6174652061646469746976653d2273756d22206174747269627574654e616d653d2273746172744f6666736574222066726f6d3d2230252220746f3d22313030252220626567696e3d22307322206475723d223330732220726570656174436f756e743d22696e646566696e69746522202f3e203c2f74657874506174683e3c6d61736b2069643d22666164652d757022206d61736b436f6e74656e74556e6974733d226f626a656374426f756e64696e67426f78223e3c726563742077696474683d223122206865696768743d2231222066696c6c3d2275726c2823677261642d75702922202f3e3c2f6d61736b3e22207374726f6b653d227267626128302c302c302c302e332922207374726f6b652d77696474683d2233327078222066696c6c3d226e6f6e6522207374726f6b652d6c696e656361703d22726f756e6422202f3e203c616e696d6174652061646469746976653d2273756d22206174747269627574654e616d653d2273746172744f6666736574222066726f6d3d2230252220746f3d22313030252220626567696e3d22307322206475723d2233307322203c67207374796c653d227472616e73666f726d3a7472616e736c61746528323970782c20343434707829223e3c636972636c65207374796c653d227472616e73666f726d3a7472616e736c6174653364283c7376672077696474683d2732393027206865696768743d27353030272076696577426f783d2730203020323930203530302720786d6c6e733d27687474703a2f2f7777772e77332e6f72672f323030302f737667273e3c636972636c652063783d27203c67207374796c653d2266696c7465723a75726c2823746f702d726567696f6e2d626c7572293b207472616e73666f726d3a7363616c6528312e35293b207472616e73666f726d2d6f726967696e3a63656e74657220746f703b223e22202f3e3c6665426c656e64206d6f64653d226f7665726c61792220696e3d2270302220696e323d22703122202f3e3c6665426c656e64206d6f64653d226578636c7573696f6e2220696e323d22703222202f3e3c6665426c656e64206d6f64653d226f7665726c61792220696e323d2270332220726573756c743d22626c656e644f757422202f3e3c6665476175737369616e426c7572203c706174682069643d226d696e696d61702220643d224d3233342034343443323334203435372e393439203234322e323120343633203235332034363322202f3e3c6d61736b2069643d226e6f6e6522206d61736b436f6e74656e74556e6974733d226f626a656374426f756e64696e67426f78223e3c726563742077696474683d223122206865696768743d2231222066696c6c3d22776869746522202f3e3c2f6d61736b3e2220783d223070782220793d22307078222077696474683d22323930707822206865696768743d22353030707822202f3e203c616e696d6174652061646469746976653d2273756d22206174747269627574654e616d653d2273746172744f6666736574222066726f6d3d2230252220746f3d22313030252220626567696e3d22307322206475723d223330732220726570656174436f756e743d22696e646566696e69746522202f3e3c7465787420783d22313270782220793d22313770782220666f6e742d66616d696c793d2227436f7572696572204e6577272c206d6f6e6f73706163652220666f6e742d73697a653d2231327078222066696c6c3d227768697465223e3c747370616e2066696c6c3d2272676261283235352c3235352c3235352c302e3629223e4d696e205469636b3a203c2f747370616e3e3c74657874506174682073746172744f66667365743d222d31303025222066696c6c3d2277686974652220666f6e742d66616d696c793d2227436f7572696572204e6577272c206d6f6e6f73706163652220666f6e742d73697a653d22313070782220786c696e6b3a687265663d2223746578742d706174682d61223e3c6c696e6561724772616469656e742069643d22677261642d646f776e222078313d2230222078323d2231222079313d2230222079323d2231223e3c73746f70206f66667365743d22302e30222073746f702d636f6c6f723d227768697465222073746f702d6f7061636974793d223122202f3e3c73746f70206f66667365743d22302e39222073746f702d636f6c6f723d227768697465222073746f702d6f7061636974793d223022202f3e3c2f6c696e6561724772616469656e743e3c66696c7465722069643d226631223e3c6665496d61676520726573756c743d2270302220786c696e6b3a687265663d22646174613a696d6167652f7376672b786d6c3b6261736536342c3c7376672077696474683d2732393027206865696768743d27353030272076696577426f783d2730203020323930203530302720786d6c6e733d27687474703a2f2f7777772e77332e6f72672f323030302f737667273e3c726563742077696474683d27323930707827206865696768743d273530307078272066696c6c3d2723222f3e3c6665496d61676520726573756c743d2270322220786c696e6b3a687265663d22646174613a696d6167652f7376672b786d6c3b6261736536342c3c656c6c697073652063783d22353025222063793d22307078222072783d223138307078222072793d223132307078222066696c6c3d222330303022206f7061636974793d22302e383522202f3e3c2f673e707822206865696768743d2232367078222072783d22387078222072793d22387078222066696c6c3d227267626128302c302c302c302e362922202f3e70782220723d22347078222066696c6c3d22776869746522202f3e3c636972636c652063783d2231312e333437384c32342031324c31342e343334312031322e363532324c32322e333932332031384c31332e373831392031332e373831394c31382032322e333932334c31322e363532322031342e343334314c31322032344c31312e333437382031342e343334314c362032322e33393c726563742066696c6c3d226e6f6e652220783d223070782220793d22307078222077696474683d22323930707822206865696768743d22353030707822202f3e4142434445464748494a4b4c4d4e4f505152535455565758595a6162636465666768696a6b6c6d6e6f707172737475767778797a303132333435363738392b2f20786d6c6e733a786c696e6b3d27687474703a2f2f7777772e77332e6f72672f313939392f786c696e6b273e3c6c696e6561724772616469656e742069643d22677261642d73796d626f6c223e3c73746f70206f66667365743d22302e37222073746f702d636f6c6f723d227768697465222073746f702d6f7061636974793d223122202f3e3c73746f70206f66667365743d222e3935222073746f702d636f6c6f723d227768697465222073746f702d6f7061636974793d223022202f3e3c2f6c696e6561724772616469656e743e207374796c653d227472616e73666f726d3a7472616e736c61746528373270782c313839707829223e3c7265637420783d222d313670782220793d222d31367078222077696474683d22313830707822206865696768743d223138307078222066696c6c3d226e6f6e6522202f3e3c7061746820643d22207374796c653d227472616e73666f726d3a7472616e736c61746528373270782c313839707829223e70782220723d2232347078222066696c6c3d226e6f6e6522207374726f6b653d22776869746522202f3e3c7265637420783d222d313670782220793d222d31367078222077696474683d22313830707822206865696768743d223138307078222066696c6c3d226e6f6e6522202f3e536166654d6174683a206d756c7469706c69636174696f6e206f766572666c6f773c673e3c70617468207374796c653d227472616e73666f726d3a7472616e736c617465283670782c367078292220643d224d313220304c31322e3635323220392e35363538374c313820312e363037374c31332e373831392031302e323138314c32322e3339323320364c31342e34333431203c70617468207374726f6b652d6c696e656361703d22726f756e642220643d224d38203943382e30303030342032322e393439342031362e32303939203238203237203238222066696c6c3d226e6f6e6522207374726f6b653d22776869746522202f3e20726570656174436f756e743d22696e646566696e69746522202f3e3c2f74657874506174683e3c74657874506174682073746172744f66667365743d222d353025222066696c6c3d2277686974652220666f6e742d66616d696c793d2227436f7572696572204e6577272c206d6f6e6f73706163652220666f6e742d73697a653d22313070782220786c696e6b3a687265663d2223746578742d706174682d61223e3c6d61736b2069643d22666164652d646f776e22206d61736b436f6e74656e74556e6974733d226f626a656374426f756e64696e67426f78223e3c726563742077696474683d223122206865696768743d2231222066696c6c3d2275726c2823677261642d646f776e2922202f3e3c2f6d61736b3e22207374726f6b653d2272676261283235352c3235352c3235352c3129222066696c6c3d226e6f6e6522207374726f6b652d6c696e656361703d22726f756e6422202f3e3c2f673e696e3d22626c656e644f75742220737464446576696174696f6e3d22343222202f3e3c2f66696c7465723e203c636c6970506174682069643d22636f726e657273223e3c726563742077696474683d2232393022206865696768743d22353030222072783d223432222072793d22343222202f3e3c2f636c6970506174683e203c67207374796c653d227472616e73666f726d3a7472616e736c61746528323970782c20333834707829223e3c6c696e6561724772616469656e742069643d22677261642d7570222078313d2231222078323d2230222079313d2231222079323d2230223e3c73746f70206f66667365743d22302e30222073746f702d636f6c6f723d227768697465222073746f702d6f7061636974793d223122202f3e32334c31302e323138312031332e373831394c312e363037372031384c392e35363538372031322e363532324c302031324c392e35363538372031312e333437384c312e3630373720364c31302e323138312031302e323138314c3620312e363037374c31312e3334373820392e35363538374c313220305a222066696c6c3d22776869746522202f3e3c67207374796c653d227472616e73666f726d3a7472616e736c6174652832323670782c20333932707829223e3c726563742077696474683d223336707822206865696768743d2233367078222072783d22387078222072793d22387078222066696c6c3d226e6f6e6522207374726f6b653d2272676261283235352c3235352c3235352c302e322922202f3e3c74657874506174682073746172744f66667365743d22353025222066696c6c3d2277686974652220666f6e742d66616d696c793d2227436f7572696572204e6577272c206d6f6e6f73706163652220666f6e742d73697a653d22313070782220786c696e6b3a687265663d2223746578742d706174682d61223e3c7465787420783d22313270782220793d22313770782220666f6e742d66616d696c793d2227436f7572696572204e6577272c206d6f6e6f73706163652220666f6e742d73697a653d2231327078222066696c6c3d227768697465223e3c747370616e2066696c6c3d2272676261283235352c3235352c3235352c302e3629223e4d6178205469636b3a203c2f747370616e3e3c616e696d6174655472616e73666f726d206174747269627574654e616d653d227472616e73666f726d2220747970653d22726f74617465222066726f6d3d22302031382031382220746f3d2233363020313820313822206475723d223130732220726570656174436f756e743d22696e646566696e697465222f3e3c2f673e3c2f673e3c706174682069643d22746578742d706174682d612220643d224d34302031322048323530204132382032382030203020312032373820343020563436302041323820323820302030203120323530203438382048343020413238203238203020302031203132203436302056343020413238203238203020302031203430203132207a22202f3e222f3e3c6665496d61676520726573756c743d2270312220786c696e6b3a687265663d22646174613a696d6167652f7376672b786d6c3b6261736536342c3c6d61736b2069643d22666164652d73796d626f6c22206d61736b436f6e74656e74556e6974733d227573657253706163654f6e557365223e3c726563742077696474683d22323930707822206865696768743d223230307078222066696c6c3d2275726c2823677261642d73796d626f6c2922202f3e3c2f6d61736b3e3c2f646566733e3c7265637420783d22302220793d2230222077696474683d2232393022206865696768743d22353030222072783d223432222072793d223432222066696c6c3d227267626128302c302c302c302922207374726f6b653d2272676261283235352c3235352c3235352c302e322922202f3e3c2f673e3c66696c7465722069643d22746f702d726567696f6e2d626c7572223e3c6665476175737369616e426c757220696e3d22536f75726365477261706869632220737464446576696174696f6e3d22323422202f3e3c2f66696c7465723e3c2f74657874506174683e203c74657874506174682073746172744f66667365743d223025222066696c6c3d2277686974652220666f6e742d66616d696c793d2227436f7572696572204e6577272c206d6f6e6f73706163652220666f6e742d73697a653d22313070782220786c696e6b3a687265663d2223746578742d706174682d61223e3c7465787420746578742d72656e646572696e673d226f7074696d697a655370656564223e5369676e6564536166654d6174683a207375627472616374696f6e206f766572666c6f773c7265637420783d2231362220793d223136222077696474683d2232353822206865696768743d22343638222072783d223236222072793d223236222066696c6c3d227267626128302c302c302c302922207374726f6b653d2272676261283235352c3235352c3235352c302e322922202f3e3c7465787420783d22313270782220793d22313770782220666f6e742d66616d696c793d2227436f7572696572204e6577272c206d6f6e6f73706163652220666f6e742d73697a653d2231327078222066696c6c3d227768697465223e3c747370616e2066696c6c3d2272676261283235352c3235352c3235352c302e3629223e49443a203c2f747370616e3e3c726563742077696474683d223336707822206865696768743d2233367078222072783d22387078222072793d22387078222066696c6c3d226e6f6e6522207374726f6b653d2272676261283235352c3235352c3235352c302e322922202f3e3c2f746578743e3c7465787420793d2231313570782220783d2233327078222066696c6c3d2277686974652220666f6e742d66616d696c793d2227436f7572696572204e6577272c206d6f6e6f73706163652220666f6e742d7765696768743d223230302220666f6e742d73697a653d2233367078223e3c2f746578743e3c2f673e3c67207374796c653d227472616e73666f726d3a7472616e736c6174652832323670782c20343333707829223e203c67207374796c653d227472616e73666f726d3a7472616e736c61746528323970782c20343134707829223ea164736f6c6343000706000a8202c4a0d52b97735fd93c8ac1f9f7dd5abd236891563b69bfc7d07ae68cbb7ea48c6452a07de6f65bf31220fa62f7b1bddc2f5feb1321a1be144f987d79cd998aeb7326cf";
        // send_tx(&evm, sender, tx, u256_to_data(21000), 1);

        coin::destroy_freeze_cap(freeze_cap);
        coin::destroy_burn_cap(burn_cap);
        coin::destroy_mint_cap(mint_cap);
    }
}
