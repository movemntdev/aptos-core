module aptos_framework::evm {
    #[test_only]
    use aptos_framework::account;
    // use std::vector;
    use aptos_framework::account::{create_resource_address, exists_at, new_event_handle};
    use std::vector;
    use aptos_framework::coin;
    use aptos_framework::aptos_coin::AptosCoin;
    use aptos_std::secp256k1::{ecdsa_recover, ecdsa_signature_from_bytes, ecdsa_raw_public_key_to_bytes};
    use std::option::borrow;
    use aptos_std::aptos_hash::keccak256;
    use aptos_framework::create_signer::create_signer;
    #[test_only]
    use std::string;
    use aptos_framework::aptos_account::create_account;
    use aptos_std::debug;
    use std::signer::address_of;
    use aptos_framework::evm_util::{slice, to_32bit, get_contract_address, power, to_int256, data_to_u256, u256_to_data, mstore, u256_to_trimed_data, to_u256};
    use aptos_framework::timestamp::now_microseconds;
    use aptos_framework::block;
    use std::string::utf8;
    use aptos_framework::event::EventHandle;
    use aptos_framework::event;
    use aptos_std::table;
    use aptos_std::table::Table;
    use aptos_framework::rlp_decode::{decode_bytes_list};
    use aptos_std::from_bcs::{to_address};
    use std::bcs::to_bytes;
    use aptos_framework::rlp_encode::encode_bytes_list;

    const TX_TYPE_LEGACY: u64 = 1;

    const ADDR_LENGTH: u64 = 10001;
    const SIGNATURE: u64 = 10002;
    const INSUFFIENT_BALANCE: u64 = 10003;
    const NONCE: u64 = 10004;
    const CONTRACT_READ_ONLY: u64 = 10005;
    const CONTRACT_DEPLOYED: u64 = 10006;
    const TX_NOT_SUPPORT: u64 = 10007;
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

    public entry fun send_tx(
        sender: &signer,
        evm_from: vector<u8>,
        tx: vector<u8>,
        gas_bytes: vector<u8>,
        tx_type: u64,
    ) acquires Account, ContractEvent {
        let gas = to_u256(gas_bytes);
        if(tx_type == TX_TYPE_LEGACY) {
            let decoded = decode_bytes_list(&tx);
            let nonce = to_u256(*vector::borrow(&decoded, 0));
            let gas_price = to_u256(*vector::borrow(&decoded, 1));
            let gas_limit = to_u256(*vector::borrow(&decoded, 2));
            let evm_to = *vector::borrow(&decoded, 3);
            let value = to_u256(*vector::borrow(&decoded, 4));
            let data = *vector::borrow(&decoded, 5);
            let v = (to_u256(*vector::borrow(&decoded, 6)) as u64);
            let r = *vector::borrow(&decoded, 7);
            let s = *vector::borrow(&decoded, 8);

            let message = encode_bytes_list(vector[
                u256_to_trimed_data(nonce),
                u256_to_trimed_data(gas_price),
                u256_to_trimed_data(gas_limit),
                evm_to,
                u256_to_trimed_data(value),
                data,
                CHAIN_ID_BYTES,
                x"",
                x""
                ]);
            let message_hash = keccak256(message);
            verify_signature(evm_from, message_hash, r, s, v);
            execute(to_32bit(evm_from), to_32bit(evm_to), (nonce as u64), data, value);
            transfer_to_move_addr(to_32bit(evm_from), address_of(sender), gas * CONVERT_BASE);
        } else {
            assert!(false, TX_NOT_SUPPORT);
        }
    }

    public entry fun estimate_tx_gas(
        evm_from: vector<u8>,
        evm_to: vector<u8>,
        data: vector<u8>,
        value_bytes: vector<u8>,
        tx_type: u64,
    ) acquires Account, ContractEvent {
        let value = to_u256(value_bytes);
        if(tx_type == TX_TYPE_LEGACY) {
            let nonce = borrow_global<Account>(create_resource_address(&@aptos_framework, to_32bit(evm_from))).nonce;
            execute(to_32bit(evm_from), to_32bit(evm_to), nonce, data, value);
        } else {
            assert!(false, TX_NOT_SUPPORT);
        }
    }

    public entry fun deposit(sender: &signer, evm_addr: vector<u8>, amount_bytes: vector<u8>) acquires Account {
        let amount = to_u256(amount_bytes);
        assert!(vector::length(&evm_addr) == 20, ADDR_LENGTH);
        transfer_from_move_addr(sender, to_32bit(evm_addr), amount);
    }

    #[view]
    public fun get_move_address(evm_addr: vector<u8>): address {
        create_resource_address(&@aptos_framework, to_32bit(evm_addr))
    }

    #[view]
    public fun query(sender:vector<u8>, contract_addr: vector<u8>, data: vector<u8>): vector<u8> acquires Account, ContractEvent {
        contract_addr = to_32bit(contract_addr);
        let contract_store = borrow_global_mut<Account>(create_resource_address(&@aptos_framework, contract_addr));
        run(sender, sender, contract_addr, contract_store.code, data, true, 0)
    }

    #[view]
    public fun get_storage_at(addr: vector<u8>, slot: vector<u8>): vector<u8> acquires Account {
        let move_address = create_resource_address(&@aptos_framework, addr);
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

    fun execute(evm_from: vector<u8>, evm_to: vector<u8>, nonce: u64, data: vector<u8>, value: u256): vector<u8> acquires Account, ContractEvent {
        let address_from = create_resource_address(&@aptos_framework, evm_from);
        verify_nonce(address_from, nonce);
        let address_to = create_resource_address(&@aptos_framework, evm_to);
        create_account_if_not_exist(address_from);
        create_account_if_not_exist(address_to);
        let account_store_to = borrow_global_mut<Account>(address_to);
        if(evm_to == ZERO_ADDR) {
            let evm_contract = get_contract_address(evm_from, nonce);
            let address_contract = create_resource_address(&@aptos_framework, evm_contract);
            create_account_if_not_exist(address_contract);
            create_event_if_not_exist(address_contract);
            borrow_global_mut<Account>(address_contract).is_contract = true;
            borrow_global_mut<Account>(address_contract).code = run(evm_from, evm_from, evm_contract, data, x"", false, value);
            evm_contract
        } else if(evm_to == ONE_ADDR) {
            let amount = data_to_u256(data, 36, 32);
            let to = to_address(slice(data, 100, 32));
            transfer_to_move_addr(evm_from, to, amount);
            x""
        } else {
            if(account_store_to.is_contract) {
                run(evm_from, evm_from, evm_to, account_store_to.code, data, false, value)
            } else {
                transfer_to_evm_addr(evm_from, evm_to, value);
                x""
            }
        }
    }

    fun run(sender: vector<u8>, origin: vector<u8>, evm_contract_address: vector<u8>, code: vector<u8>, data: vector<u8>, readOnly: bool, value: u256): vector<u8> acquires Account, ContractEvent {
        let move_contract_address = create_resource_address(&@aptos_framework, evm_contract_address);
        transfer_to_evm_addr(sender, evm_contract_address, value);

        let stack = &mut vector::empty<u256>();
        let memory = &mut vector::empty<u8>();
        // let contract_store = borrow_global_mut<Account>(move_contract_address);
        // let event_store = borrow_global_mut<ContractEvent>(move_contract_address);
        // let storage = simple_map::borrow_mut<vector<u8>, T>(&mut global.contracts, &contract_addr).storage;
        let len = vector::length(&code);
        let runtime_code = vector::empty<u8>();
        let i = 0;
        let ret_size = 0;
        let ret_bytes = vector::empty<u8>();

        while (i < len) {
            let opcode = *vector::borrow(&code, i);
            // debug::print(&i);
            // debug::print(&opcode);
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
                vector::push_back(stack, a * b);
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
                //div && sdiv
            else if(opcode == 0x04 || opcode == 0x05) {
                let a = vector::pop_back(stack);
                let b = vector::pop_back(stack);
                vector::push_back(stack, a / b);
                i = i + 1;
            }
                //mod && smod
            else if(opcode == 0x06 || opcode == 0x07) {
                let a = vector::pop_back(stack);
                let b = vector::pop_back(stack);
                vector::push_back(stack, a % b);
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
                vector::push_back(stack, (a * b) % n);
                i = i + 1;
            }
                //exp
            else if(opcode == 0x0a) {
                let a = vector::pop_back(stack);
                let b = vector::pop_back(stack);
                vector::push_back(stack, power(a, b));
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
                let(sg_a, num_a) = to_int256(a);
                let(sg_b, num_b) = to_int256(b);
                let value = 0;
                if((sg_a && !sg_b) || (sg_a && sg_b && num_a > num_b) || (!sg_a && !sg_b && num_a < num_b)) {
                    value = 1
                };
                vector::push_back(stack, value);
                i = i + 1;
            }
                //sgt
            else if(opcode == 0x13) {
                let a = vector::pop_back(stack);
                let b = vector::pop_back(stack);
                let(sg_a, num_a) = to_int256(a);
                let(sg_b, num_b) = to_int256(b);
                let value = 0;
                if((sg_a && !sg_b) || (sg_a && sg_b && num_a < num_b) || (!sg_a && !sg_b && num_a > num_b)) {
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
                //push0
            else if(opcode == 0x5f) {
                vector::push_back(stack, 0);
                i = i + 1;
            }
                // push1 -> push32
            else if(opcode >= 0x60 && opcode <= 0x7f)  {
                let n = ((opcode - 0x60) as u64);
                let number = data_to_u256(code, ((i + 1) as u256), ((n + 1) as u256));
                vector::push_back(stack, (number as u256));
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
                let addr = u256_to_data(vector::pop_back(stack));
                let account_store = borrow_global<Account>(create_resource_address(&@aptos_framework, addr));
                vector::push_back(stack, account_store.balance);
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
                if(exists<Account>(target_address)) {
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
                //sha3
            else if(opcode == 0x20) {
                let pos = vector::pop_back(stack);
                let len = vector::pop_back(stack);
                let bytes = slice(*memory, pos, len);
                // debug::print(&utf8(b"sha3"));
                // debug::print(&bytes);
                let value = data_to_u256(keccak256(bytes), 0, 32);
                // debug::print(&value);
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


                // debug::print(&utf8(b"call 222"));
                // debug::print(&opcode);
                // debug::print(&dest_addr);
                if (exists<Account>(move_dest_addr)) {
                    let ret_end = ret_len + ret_pos;
                    let params = slice(*memory, m_pos, m_len);
                    let account_store_dest = borrow_global_mut<Account>(move_dest_addr);

                    let target = if (opcode == 0xf4) evm_contract_address else evm_dest_addr;
                    let from = if (opcode == 0xf4) sender else evm_contract_address;
                    // debug::print(&utf8(b"call"));
                    // debug::print(&params);
                    // if(opcode == 0xf4) {
                    //     debug::print(&utf8(b"delegate call"));
                    //     debug::print(&sender);
                    //     debug::print(&target);
                    // };
                    ret_bytes = run(from, sender, target, account_store_dest.code, params, readOnly, msg_value);
                    ret_size = (vector::length(&ret_bytes) as u256);
                    let index = 0;
                    // if(opcode == 0xf4) {
                    //     storage = simple_map::borrow_mut<vector<u8>, T>(&mut global.contracts, &contract_addr).storage;
                    // };
                    while (ret_pos < ret_end) {
                        let bytes = if (ret_end - ret_pos >= 32) {
                            slice(ret_bytes, index, 32)
                        } else {
                            slice(ret_bytes, index, ret_end - ret_pos)
                        };
                        mstore(memory, ret_pos, bytes);
                        ret_pos = ret_pos + 32;
                        index = index + 32;
                    };
                    vector::push_back(stack, 1);
                } else {
                    if (opcode == 0xfa) {
                        vector::push_back(stack, 0);
                    } else {
                        transfer_to_evm_addr(evm_contract_address, evm_dest_addr, msg_value);
                    }
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
                debug::print(&utf8(b"create start"));
                debug::print(&new_evm_contract_addr);
                let new_move_contract_addr = create_resource_address(&@aptos_framework, new_evm_contract_addr);
                contract_store.nonce = contract_store.nonce + 1;

                debug::print(&exists<Account>(new_move_contract_addr));
                assert!(!exist_contract(new_move_contract_addr), CONTRACT_DEPLOYED);
                create_account_if_not_exist(new_move_contract_addr);
                create_event_if_not_exist(new_move_contract_addr);

                // let new_contract_store = borrow_global_mut<Account>(new_move_contract_addr);
                borrow_global_mut<Account>(move_contract_address).nonce = 1;
                borrow_global_mut<Account>(move_contract_address).is_contract = true;
                borrow_global_mut<Account>(move_contract_address).code = run(evm_contract_address, sender, new_evm_contract_addr, new_codes, x"", false, msg_value);

                debug::print(&utf8(b"create end"));
                ret_size = 32;
                ret_bytes = new_evm_contract_addr;
                vector::push_back(stack, data_to_u256(new_evm_contract_addr, 0, 32));
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
                debug::print(&new_evm_contract_addr);
                debug::print(&exists<Account>(new_move_contract_addr));
                assert!(!exist_contract(new_move_contract_addr), CONTRACT_DEPLOYED);
                create_account_if_not_exist(new_move_contract_addr);
                create_event_if_not_exist(new_move_contract_addr);

                // debug::print(&p);
                // debug::print(&new_codes);
                // debug::print(&new_contract_addr);
                borrow_global_mut<Account>(move_contract_address).nonce = borrow_global_mut<Account>(move_contract_address).nonce + 1;
                // let new_contract_store = borrow_global_mut<Account>(new_move_contract_addr);
                borrow_global_mut<Account>(new_move_contract_addr).nonce = 1;
                borrow_global_mut<Account>(new_move_contract_addr).is_contract = true;
                borrow_global_mut<Account>(new_move_contract_addr).code = run(evm_contract_address, sender, new_evm_contract_addr, new_codes, x"", false, msg_value);
                // new_contract_store.code = code;
                ret_size = 32;
                ret_bytes = new_evm_contract_addr;
                vector::push_back(stack, data_to_u256(new_evm_contract_addr,0, 32));
                i = i + 1
            }
                //revert
            else if(opcode == 0xfd) {
                let pos = vector::pop_back(stack);
                let len = vector::pop_back(stack);
                let bytes = slice(*memory, pos, len);
                debug::print(&bytes);
                // debug::print(&pos);
                // debug::print(&len);
                // debug::print(memory);
                i = i + 1;
                assert!(false, (opcode as u64));
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
        ret_bytes
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
            let account_store_from = borrow_global_mut<Account>(move_from);
            assert!(account_store_from.balance >= amount, INSUFFIENT_BALANCE);
            account_store_from.balance = account_store_from.balance - amount;

            let account_store_to = borrow_global_mut<Account>(move_to);
            account_store_to.balance = account_store_to.balance + amount;
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
        let recovery_id = ((v - (CHAIN_ID * 2) - 35) as u8);
        let pk_recover = ecdsa_recover(message_hash, recovery_id, &signature);
        let pk = keccak256(ecdsa_raw_public_key_to_bytes(borrow(&pk_recover)));
        // debug::print(&slice(pk, 12, 20));
        assert!(slice(pk, 12, 20) == from, SIGNATURE);
    }

    // #[test(evm = @0x2)]
    // fun test_execute_contract() acquires Account, ContractEvent {
    //     let sender = to_32bit(x"892a2b7cF919760e148A0d33C1eb0f44D3b383f8");
    //     create_account_if_not_exist(create_resource_address(&@aptos_framework, sender));
    //
    //     let aptos = account::create_account_for_test(@0x1);
    //     set_time_has_started_for_testing(&aptos);
    //     block::initialize_for_test(&aptos, 500000000);
    //
    //     //USDC
    //     let usdc_init_code = x"60806040526005805460ff191660121790553480156200001d575f80fd5b5060405162000c6a38038062000c6a83398101604081905262000040916200013e565b8282600362000050838262000249565b5060046200005f828262000249565b50506005805460ff191660ff93909316929092179091555062000311915050565b634e487b7160e01b5f52604160045260245ffd5b5f82601f830112620000a4575f80fd5b81516001600160401b0380821115620000c157620000c162000080565b604051601f8301601f19908116603f01168101908282118183101715620000ec57620000ec62000080565b8160405283815260209250868385880101111562000108575f80fd5b5f91505b838210156200012b57858201830151818301840152908201906200010c565b5f93810190920192909252949350505050565b5f805f6060848603121562000151575f80fd5b83516001600160401b038082111562000168575f80fd5b620001768783880162000094565b945060208601519150808211156200018c575f80fd5b506200019b8682870162000094565b925050604084015160ff81168114620001b2575f80fd5b809150509250925092565b600181811c90821680620001d257607f821691505b602082108103620001f157634e487b7160e01b5f52602260045260245ffd5b50919050565b601f82111562000244575f81815260208120601f850160051c810160208610156200021f5750805b601f850160051c820191505b8181101562000240578281556001016200022b565b5050505b505050565b81516001600160401b0381111562000265576200026562000080565b6200027d81620002768454620001bd565b84620001f7565b602080601f831160018114620002b3575f84156200029b5750858301515b5f19600386901b1c1916600185901b17855562000240565b5f85815260208120601f198616915b82811015620002e357888601518255948401946001909101908401620002c2565b50858210156200030157878501515f19600388901b60f8161c191681555b5050505050600190811b01905550565b61094b806200031f5f395ff3fe608060405234801561000f575f80fd5b50600436106100cb575f3560e01c806340c10f1911610088578063a457c2d711610063578063a457c2d7146101a6578063a9059cbb146101b9578063ace28fa5146101cc578063dd62ed3e146101d9575f80fd5b806340c10f191461016157806370a082311461017657806395d89b411461019e575f80fd5b806306fdde03146100cf578063095ea7b3146100ed57806318160ddd1461011057806323b872dd14610122578063313ce56714610135578063395093511461014e575b5f80fd5b6100d76101ec565b6040516100e491906107a6565b60405180910390f35b6101006100fb36600461080c565b61027c565b60405190151581526020016100e4565b6002545b6040519081526020016100e4565b610100610130366004610834565b610295565b60055460ff165b60405160ff90911681526020016100e4565b61010061015c36600461080c565b6102b8565b61017461016f36600461080c565b6102d9565b005b61011461018436600461086d565b6001600160a01b03165f9081526020819052604090205490565b6100d76102e7565b6101006101b436600461080c565b6102f6565b6101006101c736600461080c565b610375565b60055461013c9060ff1681565b6101146101e736600461088d565b610382565b6060600380546101fb906108be565b80601f0160208091040260200160405190810160405280929190818152602001828054610227906108be565b80156102725780601f1061024957610100808354040283529160200191610272565b820191905f5260205f20905b81548152906001019060200180831161025557829003601f168201915b5050505050905090565b5f336102898185856103ac565b60019150505b92915050565b5f336102a28582856104cf565b6102ad858585610547565b506001949350505050565b5f336102898185856102ca8383610382565b6102d491906108f6565b6103ac565b6102e382826106e9565b5050565b6060600480546101fb906108be565b5f33816103038286610382565b9050838110156103685760405162461bcd60e51b815260206004820152602560248201527f45524332303a2064656372656173656420616c6c6f77616e63652062656c6f77604482015264207a65726f60d81b60648201526084015b60405180910390fd5b6102ad82868684036103ac565b5f33610289818585610547565b6001600160a01b039182165f90815260016020908152604080832093909416825291909152205490565b6001600160a01b03831661040e5760405162461bcd60e51b8152602060048201526024808201527f45524332303a20617070726f76652066726f6d20746865207a65726f206164646044820152637265737360e01b606482015260840161035f565b6001600160a01b03821661046f5760405162461bcd60e51b815260206004820152602260248201527f45524332303a20617070726f766520746f20746865207a65726f206164647265604482015261737360f01b606482015260840161035f565b6001600160a01b038381165f8181526001602090815260408083209487168084529482529182902085905590518481527f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925910160405180910390a3505050565b5f6104da8484610382565b90505f19811461054157818110156105345760405162461bcd60e51b815260206004820152601d60248201527f45524332303a20696e73756666696369656e7420616c6c6f77616e6365000000604482015260640161035f565b61054184848484036103ac565b50505050565b6001600160a01b0383166105ab5760405162461bcd60e51b815260206004820152602560248201527f45524332303a207472616e736665722066726f6d20746865207a65726f206164604482015264647265737360d81b606482015260840161035f565b6001600160a01b03821661060d5760405162461bcd60e51b815260206004820152602360248201527f45524332303a207472616e7366657220746f20746865207a65726f206164647260448201526265737360e81b606482015260840161035f565b6001600160a01b0383165f90815260208190526040902054818110156106845760405162461bcd60e51b815260206004820152602660248201527f45524332303a207472616e7366657220616d6f756e7420657863656564732062604482015265616c616e636560d01b606482015260840161035f565b6001600160a01b038481165f81815260208181526040808320878703905593871680835291849020805487019055925185815290927fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef910160405180910390a3610541565b6001600160a01b03821661073f5760405162461bcd60e51b815260206004820152601f60248201527f45524332303a206d696e7420746f20746865207a65726f206164647265737300604482015260640161035f565b8060025f82825461075091906108f6565b90915550506001600160a01b0382165f81815260208181526040808320805486019055518481527fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef910160405180910390a35050565b5f6020808352835180828501525f5b818110156107d1578581018301518582016040015282016107b5565b505f604082860101526040601f19601f8301168501019250505092915050565b80356001600160a01b0381168114610807575f80fd5b919050565b5f806040838503121561081d575f80fd5b610826836107f1565b946020939093013593505050565b5f805f60608486031215610846575f80fd5b61084f846107f1565b925061085d602085016107f1565b9150604084013590509250925092565b5f6020828403121561087d575f80fd5b610886826107f1565b9392505050565b5f806040838503121561089e575f80fd5b6108a7836107f1565b91506108b5602084016107f1565b90509250929050565b600181811c908216806108d257607f821691505b6020821081036108f057634e487b7160e01b5f52602260045260245ffd5b50919050565b8082018082111561028f57634e487b7160e01b5f52601160045260245ffdfea2646970667358221220a6d822ba29fb8310dc1aa94585bb37b546b3f28c10c4154952d71f49fb0d992264736f6c63430008150033000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000004555344430000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000045553444300000000000000000000000000000000000000000000000000000000";
    //     let usdc_addr = execute(sender, ZERO_ADDR, 0, usdc_init_code, 0);
    //     debug::print(&utf8(b"create usdc"));
    //     debug::print(&usdc_addr);
    //
    //     //USDT
    //     let usdt_init_code = x"60806040526005805460ff191660121790553480156200001d575f80fd5b5060405162000c6a38038062000c6a83398101604081905262000040916200013e565b8282600362000050838262000249565b5060046200005f828262000249565b50506005805460ff191660ff93909316929092179091555062000311915050565b634e487b7160e01b5f52604160045260245ffd5b5f82601f830112620000a4575f80fd5b81516001600160401b0380821115620000c157620000c162000080565b604051601f8301601f19908116603f01168101908282118183101715620000ec57620000ec62000080565b8160405283815260209250868385880101111562000108575f80fd5b5f91505b838210156200012b57858201830151818301840152908201906200010c565b5f93810190920192909252949350505050565b5f805f6060848603121562000151575f80fd5b83516001600160401b038082111562000168575f80fd5b620001768783880162000094565b945060208601519150808211156200018c575f80fd5b506200019b8682870162000094565b925050604084015160ff81168114620001b2575f80fd5b809150509250925092565b600181811c90821680620001d257607f821691505b602082108103620001f157634e487b7160e01b5f52602260045260245ffd5b50919050565b601f82111562000244575f81815260208120601f850160051c810160208610156200021f5750805b601f850160051c820191505b8181101562000240578281556001016200022b565b5050505b505050565b81516001600160401b0381111562000265576200026562000080565b6200027d81620002768454620001bd565b84620001f7565b602080601f831160018114620002b3575f84156200029b5750858301515b5f19600386901b1c1916600185901b17855562000240565b5f85815260208120601f198616915b82811015620002e357888601518255948401946001909101908401620002c2565b50858210156200030157878501515f19600388901b60f8161c191681555b5050505050600190811b01905550565b61094b806200031f5f395ff3fe608060405234801561000f575f80fd5b50600436106100cb575f3560e01c806340c10f1911610088578063a457c2d711610063578063a457c2d7146101a6578063a9059cbb146101b9578063ace28fa5146101cc578063dd62ed3e146101d9575f80fd5b806340c10f191461016157806370a082311461017657806395d89b411461019e575f80fd5b806306fdde03146100cf578063095ea7b3146100ed57806318160ddd1461011057806323b872dd14610122578063313ce56714610135578063395093511461014e575b5f80fd5b6100d76101ec565b6040516100e491906107a6565b60405180910390f35b6101006100fb36600461080c565b61027c565b60405190151581526020016100e4565b6002545b6040519081526020016100e4565b610100610130366004610834565b610295565b60055460ff165b60405160ff90911681526020016100e4565b61010061015c36600461080c565b6102b8565b61017461016f36600461080c565b6102d9565b005b61011461018436600461086d565b6001600160a01b03165f9081526020819052604090205490565b6100d76102e7565b6101006101b436600461080c565b6102f6565b6101006101c736600461080c565b610375565b60055461013c9060ff1681565b6101146101e736600461088d565b610382565b6060600380546101fb906108be565b80601f0160208091040260200160405190810160405280929190818152602001828054610227906108be565b80156102725780601f1061024957610100808354040283529160200191610272565b820191905f5260205f20905b81548152906001019060200180831161025557829003601f168201915b5050505050905090565b5f336102898185856103ac565b60019150505b92915050565b5f336102a28582856104cf565b6102ad858585610547565b506001949350505050565b5f336102898185856102ca8383610382565b6102d491906108f6565b6103ac565b6102e382826106e9565b5050565b6060600480546101fb906108be565b5f33816103038286610382565b9050838110156103685760405162461bcd60e51b815260206004820152602560248201527f45524332303a2064656372656173656420616c6c6f77616e63652062656c6f77604482015264207a65726f60d81b60648201526084015b60405180910390fd5b6102ad82868684036103ac565b5f33610289818585610547565b6001600160a01b039182165f90815260016020908152604080832093909416825291909152205490565b6001600160a01b03831661040e5760405162461bcd60e51b8152602060048201526024808201527f45524332303a20617070726f76652066726f6d20746865207a65726f206164646044820152637265737360e01b606482015260840161035f565b6001600160a01b03821661046f5760405162461bcd60e51b815260206004820152602260248201527f45524332303a20617070726f766520746f20746865207a65726f206164647265604482015261737360f01b606482015260840161035f565b6001600160a01b038381165f8181526001602090815260408083209487168084529482529182902085905590518481527f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925910160405180910390a3505050565b5f6104da8484610382565b90505f19811461054157818110156105345760405162461bcd60e51b815260206004820152601d60248201527f45524332303a20696e73756666696369656e7420616c6c6f77616e6365000000604482015260640161035f565b61054184848484036103ac565b50505050565b6001600160a01b0383166105ab5760405162461bcd60e51b815260206004820152602560248201527f45524332303a207472616e736665722066726f6d20746865207a65726f206164604482015264647265737360d81b606482015260840161035f565b6001600160a01b03821661060d5760405162461bcd60e51b815260206004820152602360248201527f45524332303a207472616e7366657220746f20746865207a65726f206164647260448201526265737360e81b606482015260840161035f565b6001600160a01b0383165f90815260208190526040902054818110156106845760405162461bcd60e51b815260206004820152602660248201527f45524332303a207472616e7366657220616d6f756e7420657863656564732062604482015265616c616e636560d01b606482015260840161035f565b6001600160a01b038481165f81815260208181526040808320878703905593871680835291849020805487019055925185815290927fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef910160405180910390a3610541565b6001600160a01b03821661073f5760405162461bcd60e51b815260206004820152601f60248201527f45524332303a206d696e7420746f20746865207a65726f206164647265737300604482015260640161035f565b8060025f82825461075091906108f6565b90915550506001600160a01b0382165f81815260208181526040808320805486019055518481527fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef910160405180910390a35050565b5f6020808352835180828501525f5b818110156107d1578581018301518582016040015282016107b5565b505f604082860101526040601f19601f8301168501019250505092915050565b80356001600160a01b0381168114610807575f80fd5b919050565b5f806040838503121561081d575f80fd5b610826836107f1565b946020939093013593505050565b5f805f60608486031215610846575f80fd5b61084f846107f1565b925061085d602085016107f1565b9150604084013590509250925092565b5f6020828403121561087d575f80fd5b610886826107f1565b9392505050565b5f806040838503121561089e575f80fd5b6108a7836107f1565b91506108b5602084016107f1565b90509250929050565b600181811c908216806108d257607f821691505b6020821081036108f057634e487b7160e01b5f52602260045260245ffd5b50919050565b8082018082111561028f57634e487b7160e01b5f52601160045260245ffdfea2646970667358221220a6d822ba29fb8310dc1aa94585bb37b546b3f28c10c4154952d71f49fb0d992264736f6c63430008150033000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000004555344540000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000045553445400000000000000000000000000000000000000000000000000000000";
    //     let usdt_addr = execute(sender, ZERO_ADDR, 1, usdt_init_code, 0);
    //     debug::print(&utf8(b"create usdt"));
    //     debug::print(&usdt_addr);
    //
    //     //WETH9
    //     let weth_init_code = x"60c0604052600d60808190526c2bb930b83832b21022ba3432b960991b60a090815261002e916000919061007a565b50604080518082019091526004808252630ae8aa8960e31b602090920191825261005a9160019161007a565b506002805460ff1916601217905534801561007457600080fd5b50610115565b828054600181600116156101000203166002900490600052602060002090601f016020900481019282601f106100bb57805160ff19168380011785556100e8565b828001600101855582156100e8579182015b828111156100e85782518255916020019190600101906100cd565b506100f49291506100f8565b5090565b61011291905b808211156100f457600081556001016100fe565b90565b61074f806101246000396000f3fe60806040526004361061009c5760003560e01c8063313ce56711610064578063313ce5671461020e57806370a082311461023957806395d89b411461026c578063a9059cbb14610281578063d0e30db0146102ba578063dd62ed3e146102c25761009c565b806306fdde03146100a1578063095ea7b31461012b57806318160ddd1461017857806323b872dd1461019f5780632e1a7d4d146101e2575b600080fd5b3480156100ad57600080fd5b506100b66102fd565b6040805160208082528351818301528351919283929083019185019080838360005b838110156100f05781810151838201526020016100d8565b50505050905090810190601f16801561011d5780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b34801561013757600080fd5b506101646004803603604081101561014e57600080fd5b506001600160a01b03813516906020013561038b565b604080519115158252519081900360200190f35b34801561018457600080fd5b5061018d6103f1565b60408051918252519081900360200190f35b3480156101ab57600080fd5b50610164600480360360608110156101c257600080fd5b506001600160a01b038135811691602081013590911690604001356103f5565b3480156101ee57600080fd5b5061020c6004803603602081101561020557600080fd5b503561056d565b005b34801561021a57600080fd5b50610223610624565b6040805160ff9092168252519081900360200190f35b34801561024557600080fd5b5061018d6004803603602081101561025c57600080fd5b50356001600160a01b031661062d565b34801561027857600080fd5b506100b661063f565b34801561028d57600080fd5b50610164600480360360408110156102a457600080fd5b506001600160a01b038135169060200135610699565b61020c6106ad565b3480156102ce57600080fd5b5061018d600480360360408110156102e557600080fd5b506001600160a01b03813581169160200135166106fc565b6000805460408051602060026001851615610100026000190190941693909304601f810184900484028201840190925281815292918301828280156103835780601f1061035857610100808354040283529160200191610383565b820191906000526020600020905b81548152906001019060200180831161036657829003601f168201915b505050505081565b3360008181526004602090815260408083206001600160a01b038716808552908352818420869055815186815291519394909390927f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925928290030190a350600192915050565b4790565b6001600160a01b03831660009081526003602052604081205482111561043c576040805162461bcd60e51b8152602060048201526000602482015290519081900360640190fd5b6001600160a01b038416331480159061047a57506001600160a01b038416600090815260046020908152604080832033845290915290205460001914155b156104fc576001600160a01b03841660009081526004602090815260408083203384529091529020548211156104d1576040805162461bcd60e51b8152602060048201526000602482015290519081900360640190fd5b6001600160a01b03841660009081526004602090815260408083203384529091529020805483900390555b6001600160a01b03808516600081815260036020908152604080832080548890039055938716808352918490208054870190558351868152935191937fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef929081900390910190a35060019392505050565b336000908152600360205260409020548111156105ab576040805162461bcd60e51b8152602060048201526000602482015290519081900360640190fd5b33600081815260036020526040808220805485900390555183156108fc0291849190818181858888f193505050501580156105ea573d6000803e3d6000fd5b5060408051828152905133917f7fcf532c15f0a6db0bd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65919081900360200190a250565b60025460ff1681565b60036020526000908152604090205481565b60018054604080516020600284861615610100026000190190941693909304601f810184900484028201840190925281815292918301828280156103835780601f1061035857610100808354040283529160200191610383565b60006106a63384846103f5565b9392505050565b33600081815260036020908152604091829020805434908101909155825190815291517fe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c9281900390910190a2565b60046020908152600092835260408084209091529082529020548156fea2646970667358221220da9c3a111ff307bcc21a489b63cc555d04d91b6d0ff23237180b67a42b605beb64736f6c63430006060033";
    //     let weth_addr = execute(sender, ZERO_ADDR, 2, weth_init_code, 0);
    //     debug::print(&utf8(b"create weth"));
    //     debug::print(&weth_addr);
    //
    //     //Factory
    //     let factory_code = x"608060405234801561001057600080fd5b50604051612aa9380380612aa98339818101604052602081101561003357600080fd5b5051600180546001600160a01b0319166001600160a01b03909216919091179055612a46806100636000396000f3fe608060405234801561001057600080fd5b50600436106100885760003560e01c8063a2e74af61161005b578063a2e74af6146100f0578063c9c6539614610118578063e6a4390514610146578063f46901ed1461017457610088565b8063017e7e581461008d578063094b7415146100b15780631e3dd18b146100b9578063574f2ba3146100d6575b600080fd5b61009561019a565b604080516001600160a01b039092168252519081900360200190f35b6100956101a9565b610095600480360360208110156100cf57600080fd5b50356101b8565b6100de6101df565b60408051918252519081900360200190f35b6101166004803603602081101561010657600080fd5b50356001600160a01b03166101e5565b005b6100956004803603604081101561012e57600080fd5b506001600160a01b038135811691602001351661025d565b6100956004803603604081101561015c57600080fd5b506001600160a01b038135811691602001351661058e565b6101166004803603602081101561018a57600080fd5b50356001600160a01b03166105b4565b6000546001600160a01b031681565b6001546001600160a01b031681565b600381815481106101c557fe5b6000918252602090912001546001600160a01b0316905081565b60035490565b6001546001600160a01b0316331461023b576040805162461bcd60e51b81526020600482015260146024820152732ab734b9bbb0b82b191d102327a92124a22222a760611b604482015290519081900360640190fd5b600180546001600160a01b0319166001600160a01b0392909216919091179055565b6000816001600160a01b0316836001600160a01b031614156102c6576040805162461bcd60e51b815260206004820152601e60248201527f556e697377617056323a204944454e544943414c5f4144445245535345530000604482015290519081900360640190fd5b600080836001600160a01b0316856001600160a01b0316106102e95783856102ec565b84845b90925090506001600160a01b03821661034c576040805162461bcd60e51b815260206004820152601760248201527f556e697377617056323a205a45524f5f41444452455353000000000000000000604482015290519081900360640190fd5b6001600160a01b038281166000908152600260209081526040808320858516845290915290205416156103bf576040805162461bcd60e51b8152602060048201526016602482015275556e697377617056323a20504149525f45584953545360501b604482015290519081900360640190fd5b6060604051806020016103d19061062c565b6020820181038252601f19601f8201166040525090506000838360405160200180836001600160a01b03166001600160a01b031660601b8152601401826001600160a01b03166001600160a01b031660601b815260140192505050604051602081830303815290604052805190602001209050808251602084016000f56040805163485cc95560e01b81526001600160a01b038781166004830152868116602483015291519297509087169163485cc9559160448082019260009290919082900301818387803b1580156104a457600080fd5b505af11580156104b8573d6000803e3d6000fd5b505050506001600160a01b0384811660008181526002602081815260408084208987168086529083528185208054978d166001600160a01b031998891681179091559383528185208686528352818520805488168517905560038054600181018255958190527fc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b90950180549097168417909655925483519283529082015281517f0d3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9929181900390910190a35050505092915050565b60026020908152600092835260408084209091529082529020546001600160a01b031681565b6001546001600160a01b0316331461060a576040805162461bcd60e51b81526020600482015260146024820152732ab734b9bbb0b82b191d102327a92124a22222a760611b604482015290519081900360640190fd5b600080546001600160a01b0319166001600160a01b0392909216919091179055565b6123d88061063a8339019056fe60806040526001600c5534801561001557600080fd5b5060405146908060526123868239604080519182900360520182208282018252600a8352692ab734b9bbb0b8102b1960b11b6020938401528151808301835260018152603160f81b908401528151808401919091527fbfcc8ef98ffbf7b6c3fec7bf5185b566b9863e35a9d83acd49ad6824b5969738818301527fc89efdaa54c0f20c7adf612882df0950f5a951637e0307cdcb4c672f298b8bc6606082015260808101949094523060a0808601919091528151808603909101815260c09094019052825192019190912060035550600580546001600160a01b03191633179055612281806101056000396000f3fe608060405234801561001057600080fd5b50600436106101a95760003560e01c80636a627842116100f9578063ba9a7a5611610097578063d21220a711610071578063d21220a714610534578063d505accf1461053c578063dd62ed3e1461058d578063fff6cae9146105bb576101a9565b8063ba9a7a56146104fe578063bc25cf7714610506578063c45a01551461052c576101a9565b80637ecebe00116100d35780637ecebe001461046557806389afcb441461048b57806395d89b41146104ca578063a9059cbb146104d2576101a9565b80636a6278421461041157806370a08231146104375780637464fc3d1461045d576101a9565b806323b872dd116101665780633644e515116101405780633644e515146103cb578063485cc955146103d35780635909c0d5146104015780635a3d549314610409576101a9565b806323b872dd1461036f57806330adf81f146103a5578063313ce567146103ad576101a9565b8063022c0d9f146101ae57806306fdde031461023c5780630902f1ac146102b9578063095ea7b3146102f15780630dfe16811461033157806318160ddd14610355575b600080fd5b61023a600480360360808110156101c457600080fd5b8135916020810135916001600160a01b0360408301351691908101906080810160608201356401000000008111156101fb57600080fd5b82018360208201111561020d57600080fd5b8035906020019184600183028401116401000000008311171561022f57600080fd5b5090925090506105c3565b005b610244610afe565b6040805160208082528351818301528351919283929083019185019080838360005b8381101561027e578181015183820152602001610266565b50505050905090810190601f1680156102ab5780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b6102c1610b24565b604080516001600160701b03948516815292909316602083015263ffffffff168183015290519081900360600190f35b61031d6004803603604081101561030757600080fd5b506001600160a01b038135169060200135610b4e565b604080519115158252519081900360200190f35b610339610b65565b604080516001600160a01b039092168252519081900360200190f35b61035d610b74565b60408051918252519081900360200190f35b61031d6004803603606081101561038557600080fd5b506001600160a01b03813581169160208101359091169060400135610b7a565b61035d610c14565b6103b5610c38565b6040805160ff9092168252519081900360200190f35b61035d610c3d565b61023a600480360360408110156103e957600080fd5b506001600160a01b0381358116916020013516610c43565b61035d610cc7565b61035d610ccd565b61035d6004803603602081101561042757600080fd5b50356001600160a01b0316610cd3565b61035d6004803603602081101561044d57600080fd5b50356001600160a01b0316610fd3565b61035d610fe5565b61035d6004803603602081101561047b57600080fd5b50356001600160a01b0316610feb565b6104b1600480360360208110156104a157600080fd5b50356001600160a01b0316610ffd565b6040805192835260208301919091528051918290030190f35b6102446113a3565b61031d600480360360408110156104e857600080fd5b506001600160a01b0381351690602001356113c5565b61035d6113d2565b61023a6004803603602081101561051c57600080fd5b50356001600160a01b03166113d8565b610339611543565b610339611552565b61023a600480360360e081101561055257600080fd5b506001600160a01b03813581169160208101359091169060408101359060608101359060ff6080820135169060a08101359060c00135611561565b61035d600480360360408110156105a357600080fd5b506001600160a01b0381358116916020013516611763565b61023a611780565b600c5460011461060e576040805162461bcd60e51b8152602060048201526011602482015270155b9a5cddd85c158c8e881313d0d2d151607a1b604482015290519081900360640190fd5b6000600c55841515806106215750600084115b61065c5760405162461bcd60e51b81526004018080602001828103825260258152602001806121936025913960400191505060405180910390fd5b600080610667610b24565b5091509150816001600160701b03168710801561068c5750806001600160701b031686105b6106c75760405162461bcd60e51b81526004018080602001828103825260218152602001806121dc6021913960400191505060405180910390fd5b60065460075460009182916001600160a01b039182169190811690891682148015906107055750806001600160a01b0316896001600160a01b031614155b61074e576040805162461bcd60e51b8152602060048201526015602482015274556e697377617056323a20494e56414c49445f544f60581b604482015290519081900360640190fd5b8a1561075f5761075f828a8d6118e2565b891561077057610770818a8c6118e2565b861561082b57886001600160a01b03166310d1e85c338d8d8c8c6040518663ffffffff1660e01b815260040180866001600160a01b03166001600160a01b03168152602001858152602001848152602001806020018281038252848482818152602001925080828437600081840152601f19601f8201169050808301925050509650505050505050600060405180830381600087803b15801561081257600080fd5b505af1158015610826573d6000803e3d6000fd5b505050505b604080516370a0823160e01b815230600482015290516001600160a01b038416916370a08231916024808301926020929190829003018186803b15801561087157600080fd5b505afa158015610885573d6000803e3d6000fd5b505050506040513d602081101561089b57600080fd5b5051604080516370a0823160e01b815230600482015290519195506001600160a01b038316916370a0823191602480820192602092909190829003018186803b1580156108e757600080fd5b505afa1580156108fb573d6000803e3d6000fd5b505050506040513d602081101561091157600080fd5b5051925060009150506001600160701b0385168a90038311610934576000610943565b89856001600160701b03160383035b9050600089856001600160701b031603831161096057600061096f565b89856001600160701b03160383035b905060008211806109805750600081115b6109bb5760405162461bcd60e51b81526004018080602001828103825260248152602001806121b86024913960400191505060405180910390fd5b60006109ef6109d184600363ffffffff611a7c16565b6109e3876103e863ffffffff611a7c16565b9063ffffffff611adf16565b90506000610a076109d184600363ffffffff611a7c16565b9050610a38620f4240610a2c6001600160701b038b8116908b1663ffffffff611a7c16565b9063ffffffff611a7c16565b610a48838363ffffffff611a7c16565b1015610a8a576040805162461bcd60e51b815260206004820152600c60248201526b556e697377617056323a204b60a01b604482015290519081900360640190fd5b5050610a9884848888611b2f565b60408051838152602081018390528082018d9052606081018c905290516001600160a01b038b169133917fd78ad95fa46c994b6551d0da85fc275fe613ce37657fb8d5e3d130840159d8229181900360800190a350506001600c55505050505050505050565b6040518060400160405280600a8152602001692ab734b9bbb0b8102b1960b11b81525081565b6008546001600160701b0380821692600160701b830490911691600160e01b900463ffffffff1690565b6000610b5b338484611cf4565b5060015b92915050565b6006546001600160a01b031681565b60005481565b6001600160a01b038316600090815260026020908152604080832033845290915281205460001914610bff576001600160a01b0384166000908152600260209081526040808320338452909152902054610bda908363ffffffff611adf16565b6001600160a01b03851660009081526002602090815260408083203384529091529020555b610c0a848484611d56565b5060019392505050565b7f6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c981565b601281565b60035481565b6005546001600160a01b03163314610c99576040805162461bcd60e51b81526020600482015260146024820152732ab734b9bbb0b82b191d102327a92124a22222a760611b604482015290519081900360640190fd5b600680546001600160a01b039384166001600160a01b03199182161790915560078054929093169116179055565b60095481565b600a5481565b6000600c54600114610d20576040805162461bcd60e51b8152602060048201526011602482015270155b9a5cddd85c158c8e881313d0d2d151607a1b604482015290519081900360640190fd5b6000600c81905580610d30610b24565b50600654604080516370a0823160e01b815230600482015290519395509193506000926001600160a01b03909116916370a08231916024808301926020929190829003018186803b158015610d8457600080fd5b505afa158015610d98573d6000803e3d6000fd5b505050506040513d6020811015610dae57600080fd5b5051600754604080516370a0823160e01b815230600482015290519293506000926001600160a01b03909216916370a0823191602480820192602092909190829003018186803b158015610e0157600080fd5b505afa158015610e15573d6000803e3d6000fd5b505050506040513d6020811015610e2b57600080fd5b505190506000610e4a836001600160701b03871663ffffffff611adf16565b90506000610e67836001600160701b03871663ffffffff611adf16565b90506000610e758787611e10565b60005490915080610eb257610e9e6103e86109e3610e99878763ffffffff611a7c16565b611f6e565b9850610ead60006103e8611fc0565b610f01565b610efe6001600160701b038916610ecf868463ffffffff611a7c16565b81610ed657fe5b046001600160701b038916610ef1868563ffffffff611a7c16565b81610ef857fe5b04612056565b98505b60008911610f405760405162461bcd60e51b81526004018080602001828103825260288152602001806122256028913960400191505060405180910390fd5b610f4a8a8a611fc0565b610f5686868a8a611b2f565b8115610f8657600854610f82906001600160701b0380821691600160701b90041663ffffffff611a7c16565b600b555b6040805185815260208101859052815133927f4c209b5fc8ad50758f13e2e1088ba56a560dff690a1c6fef26394f4c03821c4f928290030190a250506001600c5550949695505050505050565b60016020526000908152604090205481565b600b5481565b60046020526000908152604090205481565b600080600c5460011461104b576040805162461bcd60e51b8152602060048201526011602482015270155b9a5cddd85c158c8e881313d0d2d151607a1b604482015290519081900360640190fd5b6000600c8190558061105b610b24565b50600654600754604080516370a0823160e01b815230600482015290519496509294506001600160a01b039182169391169160009184916370a08231916024808301926020929190829003018186803b1580156110b757600080fd5b505afa1580156110cb573d6000803e3d6000fd5b505050506040513d60208110156110e157600080fd5b5051604080516370a0823160e01b815230600482015290519192506000916001600160a01b038516916370a08231916024808301926020929190829003018186803b15801561112f57600080fd5b505afa158015611143573d6000803e3d6000fd5b505050506040513d602081101561115957600080fd5b5051306000908152600160205260408120549192506111788888611e10565b6000549091508061118f848763ffffffff611a7c16565b8161119657fe5b049a50806111aa848663ffffffff611a7c16565b816111b157fe5b04995060008b1180156111c4575060008a115b6111ff5760405162461bcd60e51b81526004018080602001828103825260288152602001806121fd6028913960400191505060405180910390fd5b611209308461206e565b611214878d8d6118e2565b61121f868d8c6118e2565b604080516370a0823160e01b815230600482015290516001600160a01b038916916370a08231916024808301926020929190829003018186803b15801561126557600080fd5b505afa158015611279573d6000803e3d6000fd5b505050506040513d602081101561128f57600080fd5b5051604080516370a0823160e01b815230600482015290519196506001600160a01b038816916370a0823191602480820192602092909190829003018186803b1580156112db57600080fd5b505afa1580156112ef573d6000803e3d6000fd5b505050506040513d602081101561130557600080fd5b5051935061131585858b8b611b2f565b811561134557600854611341906001600160701b0380821691600160701b90041663ffffffff611a7c16565b600b555b604080518c8152602081018c905281516001600160a01b038f169233927fdccd412f0b1252819cb1fd330b93224ca42612892bb3f4f789976e6d81936496929081900390910190a35050505050505050506001600c81905550915091565b604051806040016040528060068152602001652aa72496ab1960d11b81525081565b6000610b5b338484611d56565b6103e881565b600c54600114611423576040805162461bcd60e51b8152602060048201526011602482015270155b9a5cddd85c158c8e881313d0d2d151607a1b604482015290519081900360640190fd5b6000600c55600654600754600854604080516370a0823160e01b815230600482015290516001600160a01b0394851694909316926114d292859287926114cd926001600160701b03169185916370a0823191602480820192602092909190829003018186803b15801561149557600080fd5b505afa1580156114a9573d6000803e3d6000fd5b505050506040513d60208110156114bf57600080fd5b50519063ffffffff611adf16565b6118e2565b600854604080516370a0823160e01b8152306004820152905161153992849287926114cd92600160701b90046001600160701b0316916001600160a01b038616916370a0823191602480820192602092909190829003018186803b15801561149557600080fd5b50506001600c5550565b6005546001600160a01b031681565b6007546001600160a01b031681565b428410156115ab576040805162461bcd60e51b8152602060048201526012602482015271155b9a5cddd85c158c8e881156141254915160721b604482015290519081900360640190fd5b6003546001600160a01b0380891660008181526004602090815260408083208054600180820190925582517f6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c98186015280840196909652958d166060860152608085018c905260a085019590955260c08085018b90528151808603909101815260e08501825280519083012061190160f01b6101008601526101028501969096526101228085019690965280518085039096018652610142840180825286519683019690962095839052610162840180825286905260ff89166101828501526101a284018890526101c28401879052519193926101e280820193601f1981019281900390910190855afa1580156116c6573d6000803e3d6000fd5b5050604051601f1901519150506001600160a01b038116158015906116fc5750886001600160a01b0316816001600160a01b0316145b61174d576040805162461bcd60e51b815260206004820152601c60248201527f556e697377617056323a20494e56414c49445f5349474e415455524500000000604482015290519081900360640190fd5b611758898989611cf4565b505050505050505050565b600260209081526000928352604080842090915290825290205481565b600c546001146117cb576040805162461bcd60e51b8152602060048201526011602482015270155b9a5cddd85c158c8e881313d0d2d151607a1b604482015290519081900360640190fd5b6000600c55600654604080516370a0823160e01b815230600482015290516118db926001600160a01b0316916370a08231916024808301926020929190829003018186803b15801561181c57600080fd5b505afa158015611830573d6000803e3d6000fd5b505050506040513d602081101561184657600080fd5b5051600754604080516370a0823160e01b815230600482015290516001600160a01b03909216916370a0823191602480820192602092909190829003018186803b15801561189357600080fd5b505afa1580156118a7573d6000803e3d6000fd5b505050506040513d60208110156118bd57600080fd5b50516008546001600160701b0380821691600160701b900416611b2f565b6001600c55565b604080518082018252601981527f7472616e7366657228616464726573732c75696e74323536290000000000000060209182015281516001600160a01b0385811660248301526044808301869052845180840390910181526064909201845291810180516001600160e01b031663a9059cbb60e01b1781529251815160009460609489169392918291908083835b6020831061198f5780518252601f199092019160209182019101611970565b6001836020036101000a0380198251168184511680821785525050505050509050019150506000604051808303816000865af19150503d80600081146119f1576040519150601f19603f3d011682016040523d82523d6000602084013e6119f6565b606091505b5091509150818015611a24575080511580611a245750808060200190516020811015611a2157600080fd5b50515b611a75576040805162461bcd60e51b815260206004820152601a60248201527f556e697377617056323a205452414e534645525f4641494c4544000000000000604482015290519081900360640190fd5b5050505050565b6000811580611a9757505080820282828281611a9457fe5b04145b610b5f576040805162461bcd60e51b815260206004820152601460248201527364732d6d6174682d6d756c2d6f766572666c6f7760601b604482015290519081900360640190fd5b80820382811115610b5f576040805162461bcd60e51b815260206004820152601560248201527464732d6d6174682d7375622d756e646572666c6f7760581b604482015290519081900360640190fd5b6001600160701b038411801590611b4d57506001600160701b038311155b611b94576040805162461bcd60e51b8152602060048201526013602482015272556e697377617056323a204f564552464c4f5760681b604482015290519081900360640190fd5b60085463ffffffff42811691600160e01b90048116820390811615801590611bc457506001600160701b03841615155b8015611bd857506001600160701b03831615155b15611c49578063ffffffff16611c0685611bf18661210c565b6001600160e01b03169063ffffffff61211e16565b600980546001600160e01b03929092169290920201905563ffffffff8116611c3184611bf18761210c565b600a80546001600160e01b0392909216929092020190555b600880546dffffffffffffffffffffffffffff19166001600160701b03888116919091176dffffffffffffffffffffffffffff60701b1916600160701b8883168102919091176001600160e01b0316600160e01b63ffffffff871602179283905560408051848416815291909304909116602082015281517f1c411e9a96e071241c2f21f7726b17ae89e3cab4c78be50e062b03a9fffbbad1929181900390910190a1505050505050565b6001600160a01b03808416600081815260026020908152604080832094871680845294825291829020859055815185815291517f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b9259281900390910190a3505050565b6001600160a01b038316600090815260016020526040902054611d7f908263ffffffff611adf16565b6001600160a01b038085166000908152600160205260408082209390935590841681522054611db4908263ffffffff61214316565b6001600160a01b0380841660008181526001602090815260409182902094909455805185815290519193928716927fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef92918290030190a3505050565b600080600560009054906101000a90046001600160a01b03166001600160a01b031663017e7e586040518163ffffffff1660e01b815260040160206040518083038186803b158015611e6157600080fd5b505afa158015611e75573d6000803e3d6000fd5b505050506040513d6020811015611e8b57600080fd5b5051600b546001600160a01b038216158015945091925090611f5a578015611f55576000611ece610e996001600160701b0388811690881663ffffffff611a7c16565b90506000611edb83611f6e565b905080821115611f52576000611f09611efa848463ffffffff611adf16565b6000549063ffffffff611a7c16565b90506000611f2e83611f2286600563ffffffff611a7c16565b9063ffffffff61214316565b90506000818381611f3b57fe5b0490508015611f4e57611f4e8782611fc0565b5050505b50505b611f66565b8015611f66576000600b555b505092915050565b60006003821115611fb1575080600160028204015b81811015611fab57809150600281828581611f9a57fe5b040181611fa357fe5b049050611f83565b50611fbb565b8115611fbb575060015b919050565b600054611fd3908263ffffffff61214316565b60009081556001600160a01b038316815260016020526040902054611ffe908263ffffffff61214316565b6001600160a01b03831660008181526001602090815260408083209490945583518581529351929391927fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef9281900390910190a35050565b60008183106120655781612067565b825b9392505050565b6001600160a01b038216600090815260016020526040902054612097908263ffffffff611adf16565b6001600160a01b038316600090815260016020526040812091909155546120c4908263ffffffff611adf16565b60009081556040805183815290516001600160a01b038516917fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef919081900360200190a35050565b6001600160701b0316600160701b0290565b60006001600160701b0382166001600160e01b0384168161213b57fe5b049392505050565b80820182811015610b5f576040805162461bcd60e51b815260206004820152601460248201527364732d6d6174682d6164642d6f766572666c6f7760601b604482015290519081900360640190fdfe556e697377617056323a20494e53554646494349454e545f4f55545055545f414d4f554e54556e697377617056323a20494e53554646494349454e545f494e5055545f414d4f554e54556e697377617056323a20494e53554646494349454e545f4c4951554944495459556e697377617056323a20494e53554646494349454e545f4c49515549444954595f4255524e4544556e697377617056323a20494e53554646494349454e545f4c49515549444954595f4d494e544544a265627a7a72315820ddcc57c37b5af411a8f0477680f3c9c1d3f65881aa751b2a5e1dcb9b7abe963464736f6c63430005100032454950373132446f6d61696e28737472696e67206e616d652c737472696e672076657273696f6e2c75696e7432353620636861696e49642c6164647265737320766572696679696e67436f6e747261637429a265627a7a723158205492bb75ed46914d8f5645fbd2cb22555ee464d2419f2ab29a7bb623b124926b64736f6c63430005100032";
    //     vector::append(&mut factory_code, sender);
    //     let factory_addr = execute(sender, ZERO_ADDR, 3, factory_code, 0);
    //     debug::print(&utf8(b"create factory"));
    //     debug::print(&factory_addr);
    //
    //     // x"c9c65396" + usdc_addr + usdt_addr
    //     let params = vector::empty<u8>();
    //     vector::append(&mut params, x"c9c65396");
    //     vector::append(&mut params, to_32bit(usdc_addr));
    //     vector::append(&mut params, to_32bit(usdt_addr));
    //     debug::print(&params);
    //     debug::print(&utf8(b"create pair"));
    //     debug::print(&utf8(b"params"));
    //     execute(sender, factory_addr, 4, params, 0);
    //
    //
    //     //allpair 0
    //     let calldata = x"1e3dd18b0000000000000000000000000000000000000000000000000000000000000000";
    //     debug::print(&query(x"", factory_addr, calldata));
    //
    //     //getpair
    //     debug::print(&utf8(b"get pair"));
    //     let params = vector::empty<u8>();
    //     vector::append(&mut params, x"e6a43905");
    //     vector::append(&mut params, to_32bit(usdt_addr));
    //     vector::append(&mut params, to_32bit(usdc_addr));
    //     let pair_addr = query(x"", factory_addr, params);
    //     debug::print(&pair_addr);
    //
    //     debug::print(&utf8(b"deploy router"));
    //     let router_code = x"60c060405234801561001057600080fd5b506040516200479d3803806200479d8339818101604052604081101561003557600080fd5b5080516020909101516001600160601b0319606092831b8116608052911b1660a05260805160601c60a05160601c614618620001856000398061015f5280610ce45280610d1f5280610e16528061103452806113be528061152452806118eb52806119e55280611a9b5280611b695280611caf5280611d375280611f7c5280611ff752806120a652806121725280612207528061227b528061277952806129ec5280612a425280612a765280612aea5280612c8a5280612dcd5280612e55525080610ea45280610f7b52806110fa5280611133528061126e528061144c528061150252806116725280611bfc5280611d695280611ecc52806122ad528061250652806126fe5280612727528061275752806128c45280612a205280612d1d5280612e875280613718528061375b5280613a3e5280613bbd5280613fed528061409b528061411b52506146186000f3fe60806040526004361061014f5760003560e01c80638803dbee116100b6578063c45a01551161006f578063c45a015514610a10578063d06ca61f14610a25578063ded9382a14610ada578063e8e3370014610b4d578063f305d71914610bcd578063fb3bdb4114610c1357610188565b80638803dbee146107df578063ad5c464814610875578063ad615dec146108a6578063af2979eb146108dc578063b6f9de951461092f578063baa2abde146109b357610188565b80634a25d94a116101085780634a25d94a146104f05780635b0d5984146105865780635c11d795146105f9578063791ac9471461068f5780637ff36ab51461072557806385f8c259146107a957610188565b806302751cec1461018d578063054d50d4146101f957806318cbafe5146102415780631f00ca74146103275780632195995c146103dc57806338ed17391461045a57610188565b3661018857336001600160a01b037f0000000000000000000000000000000000000000000000000000000000000000161461018657fe5b005b600080fd5b34801561019957600080fd5b506101e0600480360360c08110156101b057600080fd5b506001600160a01b0381358116916020810135916040820135916060810135916080820135169060a00135610c97565b6040805192835260208301919091528051918290030190f35b34801561020557600080fd5b5061022f6004803603606081101561021c57600080fd5b5080359060208101359060400135610db1565b60408051918252519081900360200190f35b34801561024d57600080fd5b506102d7600480360360a081101561026457600080fd5b813591602081013591810190606081016040820135600160201b81111561028a57600080fd5b82018360208201111561029c57600080fd5b803590602001918460208302840111600160201b831117156102bd57600080fd5b91935091506001600160a01b038135169060200135610dc6565b60408051602080825283518183015283519192839290830191858101910280838360005b838110156103135781810151838201526020016102fb565b505050509050019250505060405180910390f35b34801561033357600080fd5b506102d76004803603604081101561034a57600080fd5b81359190810190604081016020820135600160201b81111561036b57600080fd5b82018360208201111561037d57600080fd5b803590602001918460208302840111600160201b8311171561039e57600080fd5b9190808060200260200160405190810160405280939291908181526020018383602002808284376000920191909152509295506110f3945050505050565b3480156103e857600080fd5b506101e0600480360361016081101561040057600080fd5b506001600160a01b038135811691602081013582169160408201359160608101359160808201359160a08101359091169060c08101359060e081013515159060ff6101008201351690610120810135906101400135611129565b34801561046657600080fd5b506102d7600480360360a081101561047d57600080fd5b813591602081013591810190606081016040820135600160201b8111156104a357600080fd5b8201836020820111156104b557600080fd5b803590602001918460208302840111600160201b831117156104d657600080fd5b91935091506001600160a01b038135169060200135611223565b3480156104fc57600080fd5b506102d7600480360360a081101561051357600080fd5b813591602081013591810190606081016040820135600160201b81111561053957600080fd5b82018360208201111561054b57600080fd5b803590602001918460208302840111600160201b8311171561056c57600080fd5b91935091506001600160a01b03813516906020013561136e565b34801561059257600080fd5b5061022f60048036036101408110156105aa57600080fd5b506001600160a01b0381358116916020810135916040820135916060810135916080820135169060a08101359060c081013515159060ff60e082013516906101008101359061012001356114fa565b34801561060557600080fd5b50610186600480360360a081101561061c57600080fd5b813591602081013591810190606081016040820135600160201b81111561064257600080fd5b82018360208201111561065457600080fd5b803590602001918460208302840111600160201b8311171561067557600080fd5b91935091506001600160a01b038135169060200135611608565b34801561069b57600080fd5b50610186600480360360a08110156106b257600080fd5b813591602081013591810190606081016040820135600160201b8111156106d857600080fd5b8201836020820111156106ea57600080fd5b803590602001918460208302840111600160201b8311171561070b57600080fd5b91935091506001600160a01b03813516906020013561189d565b6102d76004803603608081101561073b57600080fd5b81359190810190604081016020820135600160201b81111561075c57600080fd5b82018360208201111561076e57600080fd5b803590602001918460208302840111600160201b8311171561078f57600080fd5b91935091506001600160a01b038135169060200135611b21565b3480156107b557600080fd5b5061022f600480360360608110156107cc57600080fd5b5080359060208101359060400135611e74565b3480156107eb57600080fd5b506102d7600480360360a081101561080257600080fd5b813591602081013591810190606081016040820135600160201b81111561082857600080fd5b82018360208201111561083a57600080fd5b803590602001918460208302840111600160201b8311171561085b57600080fd5b91935091506001600160a01b038135169060200135611e81565b34801561088157600080fd5b5061088a611f7a565b604080516001600160a01b039092168252519081900360200190f35b3480156108b257600080fd5b5061022f600480360360608110156108c957600080fd5b5080359060208101359060400135611f9e565b3480156108e857600080fd5b5061022f600480360360c08110156108ff57600080fd5b506001600160a01b0381358116916020810135916040820135916060810135916080820135169060a00135611fab565b6101866004803603608081101561094557600080fd5b81359190810190604081016020820135600160201b81111561096657600080fd5b82018360208201111561097857600080fd5b803590602001918460208302840111600160201b8311171561099957600080fd5b91935091506001600160a01b03813516906020013561212c565b3480156109bf57600080fd5b506101e0600480360360e08110156109d657600080fd5b506001600160a01b038135811691602081013582169160408201359160608101359160808201359160a08101359091169060c001356124b8565b348015610a1c57600080fd5b5061088a6126fc565b348015610a3157600080fd5b506102d760048036036040811015610a4857600080fd5b81359190810190604081016020820135600160201b811115610a6957600080fd5b820183602082011115610a7b57600080fd5b803590602001918460208302840111600160201b83111715610a9c57600080fd5b919080806020026020016040519081016040528093929190818152602001838360200280828437600092019190915250929550612720945050505050565b348015610ae657600080fd5b506101e06004803603610140811015610afe57600080fd5b506001600160a01b0381358116916020810135916040820135916060810135916080820135169060a08101359060c081013515159060ff60e0820135169061010081013590610120013561274d565b348015610b5957600080fd5b50610baf6004803603610100811015610b7157600080fd5b506001600160a01b038135811691602081013582169160408201359160608101359160808201359160a08101359160c0820135169060e00135612861565b60408051938452602084019290925282820152519081900360600190f35b610baf600480360360c0811015610be357600080fd5b506001600160a01b0381358116916020810135916040820135916060810135916080820135169060a0013561299d565b6102d760048036036080811015610c2957600080fd5b81359190810190604081016020820135600160201b811115610c4a57600080fd5b820183602082011115610c5c57600080fd5b803590602001918460208302840111600160201b83111715610c7d57600080fd5b91935091506001600160a01b038135169060200135612c42565b6000808242811015610cde576040805162461bcd60e51b815260206004820152601860248201526000805160206145c3833981519152604482015290519081900360640190fd5b610d0d897f00000000000000000000000000000000000000000000000000000000000000008a8a8a308a6124b8565b9093509150610d1d898685612fc4565b7f00000000000000000000000000000000000000000000000000000000000000006001600160a01b0316632e1a7d4d836040518263ffffffff1660e01b815260040180828152602001915050600060405180830381600087803b158015610d8357600080fd5b505af1158015610d97573d6000803e3d6000fd5b50505050610da58583613118565b50965096945050505050565b6000610dbe848484613210565b949350505050565b60608142811015610e0c576040805162461bcd60e51b815260206004820152601860248201526000805160206145c3833981519152604482015290519081900360640190fd5b6001600160a01b037f00000000000000000000000000000000000000000000000000000000000000001686866000198101818110610e4657fe5b905060200201356001600160a01b03166001600160a01b031614610e9f576040805162461bcd60e51b815260206004820152601d60248201526000805160206144fa833981519152604482015290519081900360640190fd5b610efd7f00000000000000000000000000000000000000000000000000000000000000008988888080602002602001604051908101604052809392919081815260200183836020028082843760009201919091525061330092505050565b91508682600184510381518110610f1057fe5b60200260200101511015610f555760405162461bcd60e51b815260040180806020018281038252602b815260200180614540602b913960400191505060405180910390fd5b610ff386866000818110610f6557fe5b905060200201356001600160a01b031633610fd97f00000000000000000000000000000000000000000000000000000000000000008a8a6000818110610fa757fe5b905060200201356001600160a01b03168b8b6001818110610fc457fe5b905060200201356001600160a01b031661344c565b85600081518110610fe657fe5b602002602001015161350c565b61103282878780806020026020016040519081016040528093929190818152602001838360200280828437600092019190915250309250613669915050565b7f00000000000000000000000000000000000000000000000000000000000000006001600160a01b0316632e1a7d4d8360018551038151811061107157fe5b60200260200101516040518263ffffffff1660e01b815260040180828152602001915050600060405180830381600087803b1580156110af57600080fd5b505af11580156110c3573d6000803e3d6000fd5b505050506110e884836001855103815181106110db57fe5b6020026020010151613118565b509695505050505050565b60606111207f000000000000000000000000000000000000000000000000000000000000000084846138af565b90505b92915050565b60008060006111597f00000000000000000000000000000000000000000000000000000000000000008f8f61344c565b9050600087611168578c61116c565b6000195b6040805163d505accf60e01b815233600482015230602482015260448101839052606481018c905260ff8a16608482015260a4810189905260c4810188905290519192506001600160a01b0384169163d505accf9160e48082019260009290919082900301818387803b1580156111e257600080fd5b505af11580156111f6573d6000803e3d6000fd5b505050506112098f8f8f8f8f8f8f6124b8565b809450819550505050509b509b9950505050505050505050565b60608142811015611269576040805162461bcd60e51b815260206004820152601860248201526000805160206145c3833981519152604482015290519081900360640190fd5b6112c77f00000000000000000000000000000000000000000000000000000000000000008988888080602002602001604051908101604052809392919081815260200183836020028082843760009201919091525061330092505050565b915086826001845103815181106112da57fe5b6020026020010151101561131f5760405162461bcd60e51b815260040180806020018281038252602b815260200180614540602b913960400191505060405180910390fd5b61132f86866000818110610f6557fe5b6110e882878780806020026020016040519081016040528093929190818152602001838360200280828437600092019190915250899250613669915050565b606081428110156113b4576040805162461bcd60e51b815260206004820152601860248201526000805160206145c3833981519152604482015290519081900360640190fd5b6001600160a01b037f000000000000000000000000000000000000000000000000000000000000000016868660001981018181106113ee57fe5b905060200201356001600160a01b03166001600160a01b031614611447576040805162461bcd60e51b815260206004820152601d60248201526000805160206144fa833981519152604482015290519081900360640190fd5b6114a57f0000000000000000000000000000000000000000000000000000000000000000898888808060200260200160405190810160405280939291908181526020018383602002808284376000920191909152506138af92505050565b915086826000815181106114b557fe5b60200260200101511115610f555760405162461bcd60e51b81526004018080602001828103825260278152602001806144d36027913960400191505060405180910390fd5b6000806115487f00000000000000000000000000000000000000000000000000000000000000008d7f000000000000000000000000000000000000000000000000000000000000000061344c565b9050600086611557578b61155b565b6000195b6040805163d505accf60e01b815233600482015230602482015260448101839052606481018b905260ff8916608482015260a4810188905260c4810187905290519192506001600160a01b0384169163d505accf9160e48082019260009290919082900301818387803b1580156115d157600080fd5b505af11580156115e5573d6000803e3d6000fd5b505050506115f78d8d8d8d8d8d611fab565b9d9c50505050505050505050505050565b804281101561164c576040805162461bcd60e51b815260206004820152601860248201526000805160206145c3833981519152604482015290519081900360640190fd5b6116c18585600081811061165c57fe5b905060200201356001600160a01b0316336116bb7f00000000000000000000000000000000000000000000000000000000000000008989600081811061169e57fe5b905060200201356001600160a01b03168a8a6001818110610fc457fe5b8a61350c565b6000858560001981018181106116d357fe5b905060200201356001600160a01b03166001600160a01b03166370a08231856040518263ffffffff1660e01b815260040180826001600160a01b03166001600160a01b0316815260200191505060206040518083038186803b15801561173857600080fd5b505afa15801561174c573d6000803e3d6000fd5b505050506040513d602081101561176257600080fd5b505160408051602088810282810182019093528882529293506117a49290918991899182918501908490808284376000920191909152508892506139e7915050565b8661185682888860001981018181106117b957fe5b905060200201356001600160a01b03166001600160a01b03166370a08231886040518263ffffffff1660e01b815260040180826001600160a01b03166001600160a01b0316815260200191505060206040518083038186803b15801561181e57600080fd5b505afa158015611832573d6000803e3d6000fd5b505050506040513d602081101561184857600080fd5b50519063ffffffff613cf216565b10156118935760405162461bcd60e51b815260040180806020018281038252602b815260200180614540602b913960400191505060405180910390fd5b5050505050505050565b80428110156118e1576040805162461bcd60e51b815260206004820152601860248201526000805160206145c3833981519152604482015290519081900360640190fd5b6001600160a01b037f0000000000000000000000000000000000000000000000000000000000000000168585600019810181811061191b57fe5b905060200201356001600160a01b03166001600160a01b031614611974576040805162461bcd60e51b815260206004820152601d60248201526000805160206144fa833981519152604482015290519081900360640190fd5b6119848585600081811061165c57fe5b6119c28585808060200260200160405190810160405280939291908181526020018383602002808284376000920191909152503092506139e7915050565b604080516370a0823160e01b815230600482015290516000916001600160a01b037f000000000000000000000000000000000000000000000000000000000000000016916370a0823191602480820192602092909190829003018186803b158015611a2c57600080fd5b505afa158015611a40573d6000803e3d6000fd5b505050506040513d6020811015611a5657600080fd5b5051905086811015611a995760405162461bcd60e51b815260040180806020018281038252602b815260200180614540602b913960400191505060405180910390fd5b7f00000000000000000000000000000000000000000000000000000000000000006001600160a01b0316632e1a7d4d826040518263ffffffff1660e01b815260040180828152602001915050600060405180830381600087803b158015611aff57600080fd5b505af1158015611b13573d6000803e3d6000fd5b505050506118938482613118565b60608142811015611b67576040805162461bcd60e51b815260206004820152601860248201526000805160206145c3833981519152604482015290519081900360640190fd5b7f00000000000000000000000000000000000000000000000000000000000000006001600160a01b031686866000818110611b9e57fe5b905060200201356001600160a01b03166001600160a01b031614611bf7576040805162461bcd60e51b815260206004820152601d60248201526000805160206144fa833981519152604482015290519081900360640190fd5b611c557f00000000000000000000000000000000000000000000000000000000000000003488888080602002602001604051908101604052809392919081815260200183836020028082843760009201919091525061330092505050565b91508682600184510381518110611c6857fe5b60200260200101511015611cad5760405162461bcd60e51b815260040180806020018281038252602b815260200180614540602b913960400191505060405180910390fd5b7f00000000000000000000000000000000000000000000000000000000000000006001600160a01b031663d0e30db083600081518110611ce957fe5b60200260200101516040518263ffffffff1660e01b81526004016000604051808303818588803b158015611d1c57600080fd5b505af1158015611d30573d6000803e3d6000fd5b50505050507f00000000000000000000000000000000000000000000000000000000000000006001600160a01b031663a9059cbb611d957f00000000000000000000000000000000000000000000000000000000000000008989600081811061169e57fe5b84600081518110611da257fe5b60200260200101516040518363ffffffff1660e01b815260040180836001600160a01b03166001600160a01b0316815260200182815260200192505050602060405180830381600087803b158015611df957600080fd5b505af1158015611e0d573d6000803e3d6000fd5b505050506040513d6020811015611e2357600080fd5b5051611e2b57fe5b611e6a82878780806020026020016040519081016040528093929190818152602001838360200280828437600092019190915250899250613669915050565b5095945050505050565b6000610dbe848484613d42565b60608142811015611ec7576040805162461bcd60e51b815260206004820152601860248201526000805160206145c3833981519152604482015290519081900360640190fd5b611f257f0000000000000000000000000000000000000000000000000000000000000000898888808060200260200160405190810160405280939291908181526020018383602002808284376000920191909152506138af92505050565b91508682600081518110611f3557fe5b6020026020010151111561131f5760405162461bcd60e51b81526004018080602001828103825260278152602001806144d36027913960400191505060405180910390fd5b7f000000000000000000000000000000000000000000000000000000000000000081565b6000610dbe848484613e32565b60008142811015611ff1576040805162461bcd60e51b815260206004820152601860248201526000805160206145c3833981519152604482015290519081900360640190fd5b612020887f000000000000000000000000000000000000000000000000000000000000000089898930896124b8565b604080516370a0823160e01b815230600482015290519194506120a492508a9187916001600160a01b038416916370a0823191602480820192602092909190829003018186803b15801561207357600080fd5b505afa158015612087573d6000803e3d6000fd5b505050506040513d602081101561209d57600080fd5b5051612fc4565b7f00000000000000000000000000000000000000000000000000000000000000006001600160a01b0316632e1a7d4d836040518263ffffffff1660e01b815260040180828152602001915050600060405180830381600087803b15801561210a57600080fd5b505af115801561211e573d6000803e3d6000fd5b505050506110e88483613118565b8042811015612170576040805162461bcd60e51b815260206004820152601860248201526000805160206145c3833981519152604482015290519081900360640190fd5b7f00000000000000000000000000000000000000000000000000000000000000006001600160a01b0316858560008181106121a757fe5b905060200201356001600160a01b03166001600160a01b031614612200576040805162461bcd60e51b815260206004820152601d60248201526000805160206144fa833981519152604482015290519081900360640190fd5b60003490507f00000000000000000000000000000000000000000000000000000000000000006001600160a01b031663d0e30db0826040518263ffffffff1660e01b81526004016000604051808303818588803b15801561226057600080fd5b505af1158015612274573d6000803e3d6000fd5b50505050507f00000000000000000000000000000000000000000000000000000000000000006001600160a01b031663a9059cbb6122d97f00000000000000000000000000000000000000000000000000000000000000008989600081811061169e57fe5b836040518363ffffffff1660e01b815260040180836001600160a01b03166001600160a01b0316815260200182815260200192505050602060405180830381600087803b15801561232957600080fd5b505af115801561233d573d6000803e3d6000fd5b505050506040513d602081101561235357600080fd5b505161235b57fe5b60008686600019810181811061236d57fe5b905060200201356001600160a01b03166001600160a01b03166370a08231866040518263ffffffff1660e01b815260040180826001600160a01b03166001600160a01b0316815260200191505060206040518083038186803b1580156123d257600080fd5b505afa1580156123e6573d6000803e3d6000fd5b505050506040513d60208110156123fc57600080fd5b5051604080516020898102828101820190935289825292935061243e9290918a918a9182918501908490808284376000920191909152508992506139e7915050565b87611856828989600019810181811061245357fe5b905060200201356001600160a01b03166001600160a01b03166370a08231896040518263ffffffff1660e01b815260040180826001600160a01b03166001600160a01b0316815260200191505060206040518083038186803b15801561181e57600080fd5b60008082428110156124ff576040805162461bcd60e51b815260206004820152601860248201526000805160206145c3833981519152604482015290519081900360640190fd5b600061252c7f00000000000000000000000000000000000000000000000000000000000000008c8c61344c565b604080516323b872dd60e01b81523360048201526001600160a01b03831660248201819052604482018d9052915192935090916323b872dd916064808201926020929091908290030181600087803b15801561258757600080fd5b505af115801561259b573d6000803e3d6000fd5b505050506040513d60208110156125b157600080fd5b50506040805163226bf2d160e21b81526001600160a01b03888116600483015282516000938493928616926389afcb44926024808301939282900301818787803b1580156125fe57600080fd5b505af1158015612612573d6000803e3d6000fd5b505050506040513d604081101561262857600080fd5b508051602090910151909250905060006126428e8e613ede565b509050806001600160a01b03168e6001600160a01b031614612665578183612668565b82825b90975095508a8710156126ac5760405162461bcd60e51b815260040180806020018281038252602681526020018061451a6026913960400191505060405180910390fd5b898610156126eb5760405162461bcd60e51b81526004018080602001828103825260268152602001806144606026913960400191505060405180910390fd5b505050505097509795505050505050565b7f000000000000000000000000000000000000000000000000000000000000000081565b60606111207f00000000000000000000000000000000000000000000000000000000000000008484613300565b600080600061279d7f00000000000000000000000000000000000000000000000000000000000000008e7f000000000000000000000000000000000000000000000000000000000000000061344c565b90506000876127ac578c6127b0565b6000195b6040805163d505accf60e01b815233600482015230602482015260448101839052606481018c905260ff8a16608482015260a4810189905260c4810188905290519192506001600160a01b0384169163d505accf9160e48082019260009290919082900301818387803b15801561282657600080fd5b505af115801561283a573d6000803e3d6000fd5b5050505061284c8e8e8e8e8e8e610c97565b909f909e509c50505050505050505050505050565b600080600083428110156128aa576040805162461bcd60e51b815260206004820152601860248201526000805160206145c3833981519152604482015290519081900360640190fd5b6128b88c8c8c8c8c8c613fbc565b909450925060006128ea7f00000000000000000000000000000000000000000000000000000000000000008e8e61344c565b90506128f88d33838861350c565b6129048c33838761350c565b806001600160a01b0316636a627842886040518263ffffffff1660e01b815260040180826001600160a01b03166001600160a01b03168152602001915050602060405180830381600087803b15801561295c57600080fd5b505af1158015612970573d6000803e3d6000fd5b505050506040513d602081101561298657600080fd5b5051949d939c50939a509198505050505050505050565b600080600083428110156129e6576040805162461bcd60e51b815260206004820152601860248201526000805160206145c3833981519152604482015290519081900360640190fd5b612a148a7f00000000000000000000000000000000000000000000000000000000000000008b348c8c613fbc565b90945092506000612a667f00000000000000000000000000000000000000000000000000000000000000008c7f000000000000000000000000000000000000000000000000000000000000000061344c565b9050612a748b33838861350c565b7f00000000000000000000000000000000000000000000000000000000000000006001600160a01b031663d0e30db0856040518263ffffffff1660e01b81526004016000604051808303818588803b158015612acf57600080fd5b505af1158015612ae3573d6000803e3d6000fd5b50505050507f00000000000000000000000000000000000000000000000000000000000000006001600160a01b031663a9059cbb82866040518363ffffffff1660e01b815260040180836001600160a01b03166001600160a01b0316815260200182815260200192505050602060405180830381600087803b158015612b6857600080fd5b505af1158015612b7c573d6000803e3d6000fd5b505050506040513d6020811015612b9257600080fd5b5051612b9a57fe5b806001600160a01b0316636a627842886040518263ffffffff1660e01b815260040180826001600160a01b03166001600160a01b03168152602001915050602060405180830381600087803b158015612bf257600080fd5b505af1158015612c06573d6000803e3d6000fd5b505050506040513d6020811015612c1c57600080fd5b5051925034841015612c3457612c3433853403613118565b505096509650969350505050565b60608142811015612c88576040805162461bcd60e51b815260206004820152601860248201526000805160206145c3833981519152604482015290519081900360640190fd5b7f00000000000000000000000000000000000000000000000000000000000000006001600160a01b031686866000818110612cbf57fe5b905060200201356001600160a01b03166001600160a01b031614612d18576040805162461bcd60e51b815260206004820152601d60248201526000805160206144fa833981519152604482015290519081900360640190fd5b612d767f0000000000000000000000000000000000000000000000000000000000000000888888808060200260200160405190810160405280939291908181526020018383602002808284376000920191909152506138af92505050565b91503482600081518110612d8657fe5b60200260200101511115612dcb5760405162461bcd60e51b81526004018080602001828103825260278152602001806144d36027913960400191505060405180910390fd5b7f00000000000000000000000000000000000000000000000000000000000000006001600160a01b031663d0e30db083600081518110612e0757fe5b60200260200101516040518263ffffffff1660e01b81526004016000604051808303818588803b158015612e3a57600080fd5b505af1158015612e4e573d6000803e3d6000fd5b50505050507f00000000000000000000000000000000000000000000000000000000000000006001600160a01b031663a9059cbb612eb37f00000000000000000000000000000000000000000000000000000000000000008989600081811061169e57fe5b84600081518110612ec057fe5b60200260200101516040518363ffffffff1660e01b815260040180836001600160a01b03166001600160a01b0316815260200182815260200192505050602060405180830381600087803b158015612f1757600080fd5b505af1158015612f2b573d6000803e3d6000fd5b505050506040513d6020811015612f4157600080fd5b5051612f4957fe5b612f8882878780806020026020016040519081016040528093929190818152602001838360200280828437600092019190915250899250613669915050565b81600081518110612f9557fe5b6020026020010151341115611e6a57611e6a3383600081518110612fb557fe5b60200260200101513403613118565b604080516001600160a01b038481166024830152604480830185905283518084039091018152606490920183526020820180516001600160e01b031663a9059cbb60e01b178152925182516000946060949389169392918291908083835b602083106130415780518252601f199092019160209182019101613022565b6001836020036101000a0380198251168184511680821785525050505050509050019150506000604051808303816000865af19150503d80600081146130a3576040519150601f19603f3d011682016040523d82523d6000602084013e6130a8565b606091505b50915091508180156130d65750805115806130d657508080602001905160208110156130d357600080fd5b50515b6131115760405162461bcd60e51b815260040180806020018281038252602d81526020018061456b602d913960400191505060405180910390fd5b5050505050565b604080516000808252602082019092526001600160a01b0384169083906040518082805190602001908083835b602083106131645780518252601f199092019160209182019101613145565b6001836020036101000a03801982511681845116808217855250505050505090500191505060006040518083038185875af1925050503d80600081146131c6576040519150601f19603f3d011682016040523d82523d6000602084013e6131cb565b606091505b505090508061320b5760405162461bcd60e51b81526004018080602001828103825260348152602001806144076034913960400191505060405180910390fd5b505050565b60008084116132505760405162461bcd60e51b815260040180806020018281038252602b815260200180614598602b913960400191505060405180910390fd5b6000831180156132605750600082115b61329b5760405162461bcd60e51b81526004018080602001828103825260288152602001806144866028913960400191505060405180910390fd5b60006132af856103e563ffffffff61423016565b905060006132c3828563ffffffff61423016565b905060006132e9836132dd886103e863ffffffff61423016565b9063ffffffff61429316565b90508082816132f457fe5b04979650505050505050565b6060600282511015613359576040805162461bcd60e51b815260206004820152601e60248201527f556e697377617056324c6962726172793a20494e56414c49445f504154480000604482015290519081900360640190fd5b815167ffffffffffffffff8111801561337157600080fd5b5060405190808252806020026020018201604052801561339b578160200160208202803683370190505b50905082816000815181106133ac57fe5b60200260200101818152505060005b6001835103811015613444576000806133fe878685815181106133da57fe5b60200260200101518786600101815181106133f157fe5b60200260200101516142e2565b9150915061342084848151811061341157fe5b60200260200101518383613210565b84846001018151811061342f57fe5b602090810291909101015250506001016133bb565b509392505050565b600080600061345b8585613ede565b604080516bffffffffffffffffffffffff19606094851b811660208084019190915293851b81166034830152825160288184030181526048830184528051908501206001600160f81b031960688401529a90941b9093166069840152607d8301989098527f7e94d55cb675b314384bbad42db81f28d6e23765aeb5e4f4d9fc32c135dba2d4609d808401919091528851808403909101815260bd909201909752805196019590952095945050505050565b604080516001600160a01b0385811660248301528481166044830152606480830185905283518084039091018152608490920183526020820180516001600160e01b03166323b872dd60e01b17815292518251600094606094938a169392918291908083835b602083106135915780518252601f199092019160209182019101613572565b6001836020036101000a0380198251168184511680821785525050505050509050019150506000604051808303816000865af19150503d80600081146135f3576040519150601f19603f3d011682016040523d82523d6000602084013e6135f8565b606091505b5091509150818015613626575080511580613626575080806020019051602081101561362357600080fd5b50515b6136615760405162461bcd60e51b81526004018080602001828103825260318152602001806143d66031913960400191505060405180910390fd5b505050505050565b60005b60018351038110156138a95760008084838151811061368757fe5b602002602001015185846001018151811061369e57fe5b60200260200101519150915060006136b68383613ede565b50905060008785600101815181106136ca57fe5b60200260200101519050600080836001600160a01b0316866001600160a01b0316146136f8578260006136fc565b6000835b91509150600060028a510388106137135788613754565b6137547f0000000000000000000000000000000000000000000000000000000000000000878c8b6002018151811061374757fe5b602002602001015161344c565b90506137817f0000000000000000000000000000000000000000000000000000000000000000888861344c565b6001600160a01b031663022c0d9f84848460006040519080825280601f01601f1916602001820160405280156137be576020820181803683370190505b506040518563ffffffff1660e01b815260040180858152602001848152602001836001600160a01b03166001600160a01b0316815260200180602001828103825283818151815260200191508051906020019080838360005b8381101561382f578181015183820152602001613817565b50505050905090810190601f16801561385c5780820380516001836020036101000a031916815260200191505b5095505050505050600060405180830381600087803b15801561387e57600080fd5b505af1158015613892573d6000803e3d6000fd5b50506001909901985061366c975050505050505050565b50505050565b6060600282511015613908576040805162461bcd60e51b815260206004820152601e60248201527f556e697377617056324c6962726172793a20494e56414c49445f504154480000604482015290519081900360640190fd5b815167ffffffffffffffff8111801561392057600080fd5b5060405190808252806020026020018201604052801561394a578160200160208202803683370190505b509050828160018351038151811061395e57fe5b60209081029190910101528151600019015b8015613444576000806139a08786600186038151811061398c57fe5b60200260200101518786815181106133f157fe5b915091506139c28484815181106139b357fe5b60200260200101518383613d42565b8460018503815181106139d157fe5b6020908102919091010152505060001901613970565b60005b600183510381101561320b57600080848381518110613a0557fe5b6020026020010151858460010181518110613a1c57fe5b6020026020010151915091506000613a348383613ede565b5090506000613a647f0000000000000000000000000000000000000000000000000000000000000000858561344c565b9050600080600080846001600160a01b0316630902f1ac6040518163ffffffff1660e01b815260040160606040518083038186803b158015613aa557600080fd5b505afa158015613ab9573d6000803e3d6000fd5b505050506040513d6060811015613acf57600080fd5b5080516020909101516001600160701b0391821693501690506000806001600160a01b038a811690891614613b05578284613b08565b83835b91509150613b66828b6001600160a01b03166370a082318a6040518263ffffffff1660e01b815260040180826001600160a01b03166001600160a01b0316815260200191505060206040518083038186803b15801561181e57600080fd5b9550613b73868383613210565b945050505050600080856001600160a01b0316886001600160a01b031614613b9d57826000613ba1565b6000835b91509150600060028c51038a10613bb8578a613bec565b613bec7f0000000000000000000000000000000000000000000000000000000000000000898e8d6002018151811061374757fe5b604080516000808252602082019283905263022c0d9f60e01b835260248201878152604483018790526001600160a01b038086166064850152608060848501908152845160a48601819052969750908c169563022c0d9f958a958a958a9591949193919260c486019290918190849084905b83811015613c76578181015183820152602001613c5e565b50505050905090810190601f168015613ca35780820380516001836020036101000a031916815260200191505b5095505050505050600060405180830381600087803b158015613cc557600080fd5b505af1158015613cd9573d6000803e3d6000fd5b50506001909b019a506139ea9950505050505050505050565b80820382811115611123576040805162461bcd60e51b815260206004820152601560248201527464732d6d6174682d7375622d756e646572666c6f7760581b604482015290519081900360640190fd5b6000808411613d825760405162461bcd60e51b815260040180806020018281038252602c8152602001806143aa602c913960400191505060405180910390fd5b600083118015613d925750600082115b613dcd5760405162461bcd60e51b81526004018080602001828103825260288152602001806144866028913960400191505060405180910390fd5b6000613df16103e8613de5868863ffffffff61423016565b9063ffffffff61423016565b90506000613e0b6103e5613de5868963ffffffff613cf216565b9050613e286001828481613e1b57fe5b049063ffffffff61429316565b9695505050505050565b6000808411613e725760405162461bcd60e51b81526004018080602001828103825260258152602001806144ae6025913960400191505060405180910390fd5b600083118015613e825750600082115b613ebd5760405162461bcd60e51b81526004018080602001828103825260288152602001806144866028913960400191505060405180910390fd5b82613ece858463ffffffff61423016565b81613ed557fe5b04949350505050565b600080826001600160a01b0316846001600160a01b03161415613f325760405162461bcd60e51b815260040180806020018281038252602581526020018061443b6025913960400191505060405180910390fd5b826001600160a01b0316846001600160a01b031610613f52578284613f55565b83835b90925090506001600160a01b038216613fb5576040805162461bcd60e51b815260206004820152601e60248201527f556e697377617056324c6962726172793a205a45524f5f414444524553530000604482015290519081900360640190fd5b9250929050565b6040805163e6a4390560e01b81526001600160a01b03888116600483015287811660248301529151600092839283927f00000000000000000000000000000000000000000000000000000000000000009092169163e6a4390591604480820192602092909190829003018186803b15801561403657600080fd5b505afa15801561404a573d6000803e3d6000fd5b505050506040513d602081101561406057600080fd5b50516001600160a01b0316141561411357604080516364e329cb60e11b81526001600160a01b038a81166004830152898116602483015291517f00000000000000000000000000000000000000000000000000000000000000009092169163c9c65396916044808201926020929091908290030181600087803b1580156140e657600080fd5b505af11580156140fa573d6000803e3d6000fd5b505050506040513d602081101561411057600080fd5b50505b6000806141417f00000000000000000000000000000000000000000000000000000000000000008b8b6142e2565b91509150816000148015614153575080155b1561416357879350869250614223565b6000614170898484613e32565b90508781116141c357858110156141b85760405162461bcd60e51b81526004018080602001828103825260268152602001806144606026913960400191505060405180910390fd5b889450925082614221565b60006141d0898486613e32565b9050898111156141dc57fe5b8781101561421b5760405162461bcd60e51b815260040180806020018281038252602681526020018061451a6026913960400191505060405180910390fd5b94508793505b505b5050965096945050505050565b600081158061424b5750508082028282828161424857fe5b04145b611123576040805162461bcd60e51b815260206004820152601460248201527364732d6d6174682d6d756c2d6f766572666c6f7760601b604482015290519081900360640190fd5b80820182811015611123576040805162461bcd60e51b815260206004820152601460248201527364732d6d6174682d6164642d6f766572666c6f7760601b604482015290519081900360640190fd5b60008060006142f18585613ede565b50905060008061430288888861344c565b6001600160a01b0316630902f1ac6040518163ffffffff1660e01b815260040160606040518083038186803b15801561433a57600080fd5b505afa15801561434e573d6000803e3d6000fd5b505050506040513d606081101561436457600080fd5b5080516020909101516001600160701b0391821693501690506001600160a01b038781169084161461439757808261439a565b81815b9099909850965050505050505056fe556e697377617056324c6962726172793a20494e53554646494349454e545f4f55545055545f414d4f554e545472616e7366657248656c7065723a3a7472616e7366657246726f6d3a207472616e7366657246726f6d206661696c65645472616e7366657248656c7065723a3a736166655472616e736665724554483a20455448207472616e73666572206661696c6564556e697377617056324c6962726172793a204944454e544943414c5f414444524553534553556e69737761705632526f757465723a20494e53554646494349454e545f425f414d4f554e54556e697377617056324c6962726172793a20494e53554646494349454e545f4c4951554944495459556e697377617056324c6962726172793a20494e53554646494349454e545f414d4f554e54556e69737761705632526f757465723a204558434553534956455f494e5055545f414d4f554e54556e69737761705632526f757465723a20494e56414c49445f50415448000000556e69737761705632526f757465723a20494e53554646494349454e545f415f414d4f554e54556e69737761705632526f757465723a20494e53554646494349454e545f4f55545055545f414d4f554e545472616e7366657248656c7065723a3a736166655472616e736665723a207472616e73666572206661696c6564556e697377617056324c6962726172793a20494e53554646494349454e545f494e5055545f414d4f554e54556e69737761705632526f757465723a20455850495245440000000000000000a264697066735822122047df80f1a7c10914f638b3ecbee2089fbb2c5a1561204f4fefca475be6a9b23964736f6c63430006060033";
    //     vector::append(&mut router_code, to_32bit(factory_addr));
    //     vector::append(&mut router_code, to_32bit(weth_addr));
    //     // debug::print(&router_code);
    //     let router_addr = execute(sender, ZERO_ADDR, 5, router_code, 0);
    //     debug::print(&router_addr);
    //
    //     debug::print(&utf8(b"mint usdc"));
    //     //40c10f19 + to address
    //     let mint_usdc_params = vector::empty<u8>();
    //     vector::append(&mut mint_usdc_params, x"40c10f19");
    //     vector::append(&mut mint_usdc_params, sender);
    //     // 200 * 1e18
    //     vector::append(&mut mint_usdc_params, u256_to_data(500000000000000000000));
    //     debug::print(&mint_usdc_params);
    //     execute(sender, usdc_addr, 6, mint_usdc_params, 0);
    //
    //     debug::print(&utf8(b"mint usdt"));
    //     //40c10f19 + to address
    //     let mint_usdt_params = vector::empty<u8>();
    //     vector::append(&mut mint_usdt_params, x"40c10f19");
    //     vector::append(&mut mint_usdt_params, sender);
    //     // 200 * 1e18
    //     vector::append(&mut mint_usdt_params, u256_to_data(500000000000000000000));
    //     debug::print(&mint_usdt_params);
    //     execute(sender, usdt_addr, 7, mint_usdt_params, 0);
    //
    //     debug::print(&utf8(b"approve usdc"));
    //     //095ea7b3 + router address
    //     let approve_usdc_params = vector::empty<u8>();
    //     vector::append(&mut approve_usdc_params, x"095ea7b3");
    //     vector::append(&mut approve_usdc_params, router_addr);
    //     // 1000000 * 1e18
    //     vector::append(&mut approve_usdc_params, u256_to_data(1000000000000000000000000));
    //     // debug::print(&approve_usdc_params);
    //     execute(sender, usdc_addr, 8, approve_usdc_params, 0);
    //
    //     debug::print(&utf8(b"approve usdt"));
    //     //095ea7b3 + router address
    //     let approve_usdt_params = vector::empty<u8>();
    //     vector::append(&mut approve_usdt_params, x"095ea7b3");
    //     // 1000000 * 1e18
    //     vector::append(&mut approve_usdt_params, router_addr);
    //     vector::append(&mut approve_usdt_params, u256_to_data(1000000000000000000000000));
    //     // debug::print(&approve_usdt_params);
    //     execute(sender, usdt_addr, 9, approve_usdt_params, 0);
    //
    //     let deadline = 1697746917;
    //     debug::print(&utf8(b"add liquidity"));
    //     //e8e33700 + tokenA + tokenB + amountADesired + amountBDesired + amountAMin + amountBMin + to + deadline
    //     let add_liquidity_params = vector::empty<u8>();
    //     vector::append(&mut add_liquidity_params, x"e8e33700");
    //     vector::append(&mut add_liquidity_params, to_32bit(usdc_addr));
    //     vector::append(&mut add_liquidity_params, to_32bit(usdt_addr));
    //     // 100 * 1e18
    //     vector::append(&mut add_liquidity_params, u256_to_data(100000000000000000000));
    //     vector::append(&mut add_liquidity_params, u256_to_data(100000000000000000000));
    //     //0
    //     vector::append(&mut add_liquidity_params, u256_to_data(0));
    //     vector::append(&mut add_liquidity_params, u256_to_data(0));
    //     vector::append(&mut add_liquidity_params, sender);
    //     vector::append(&mut add_liquidity_params, u256_to_data(deadline));
    //     // debug::print(&add_liquidity_params);
    //     execute(sender, router_addr, 10, add_liquidity_params, 0);
    //
    //     debug::print(&utf8(b"get balance of USDC"));
    //     let params = vector::empty<u8>();
    //     vector::append(&mut params, x"70a08231");
    //     vector::append(&mut params, sender);
    //     // debug::print(&params);
    //     debug::print(&query(x"", usdc_addr, params));
    //
    //     debug::print(&utf8(b"get balance of USDT"));
    //     let params = vector::empty<u8>();
    //     vector::append(&mut params, x"70a08231");
    //     vector::append(&mut params, sender);
    //     debug::print(&query(x"", usdt_addr, params));
    //
    //     debug::print(&utf8(b"swap usdc for usdt"));
    //     //38ed1739 + amountIn + amountOutMin + path + to + deadline
    //     let swap_params = vector::empty<u8>();
    //     vector::append(&mut swap_params, x"38ed1739");
    //     vector::append(&mut swap_params, u256_to_data(100000000000000000000));
    //     vector::append(&mut swap_params, u256_to_data(0));
    //     // array pointer
    //     vector::append(&mut swap_params, to_32bit(x"a0"));
    //     vector::append(&mut swap_params, to_32bit(sender));
    //     vector::append(&mut swap_params, u256_to_data(deadline));
    //     //address[] array
    //     vector::append(&mut swap_params, u256_to_data(2));// array size
    //     vector::append(&mut swap_params, to_32bit(usdt_addr));
    //     vector::append(&mut swap_params, to_32bit(usdc_addr));
    //     // debug::print(&swap_params);
    //     execute(sender, router_addr, 11, swap_params, 0);
    //
    //     debug::print(&utf8(b"approve pair"));
    //     //095ea7b3 + router address
    //     let approve_usdt_params = vector::empty<u8>();
    //     vector::append(&mut approve_usdt_params, x"095ea7b3");
    //     // 1000000 * 1e18
    //     vector::append(&mut approve_usdt_params, router_addr);
    //     vector::append(&mut approve_usdt_params, u256_to_data(10000000000000000000000));
    //     debug::print(&approve_usdt_params);
    //     execute(sender, pair_addr, 12, approve_usdt_params, 0);
    //
    //     debug::print(&utf8(b"remove liquidity"));
    //     //095ea7b3 + router address
    //     let remove_params = vector::empty<u8>();
    //     vector::append(&mut remove_params, x"baa2abde");
    //     // 1000000 * 1e18
    //     vector::append(&mut remove_params, usdc_addr);
    //     vector::append(&mut remove_params, usdt_addr);
    //     vector::append(&mut remove_params, u256_to_data(1000000000000000000));
    //     vector::append(&mut remove_params, u256_to_data(0));
    //     vector::append(&mut remove_params, u256_to_data(0));
    //     vector::append(&mut remove_params, to_32bit(sender));
    //     vector::append(&mut remove_params, u256_to_data(deadline));
    //     execute(sender, router_addr, 13, remove_params, 0);
    //
    //     debug::print(&utf8(b"get balance of USDC"));
    //     let params = vector::empty<u8>();
    //     vector::append(&mut params, x"70a08231");
    //     vector::append(&mut params, sender);
    //     // debug::print(&params);
    //     debug::print(&query(x"", usdc_addr, params));
    //
    //     debug::print(&utf8(b"get balance of USDT"));
    //     let params = vector::empty<u8>();
    //     vector::append(&mut params, x"70a08231");
    //     vector::append(&mut params, sender);
    //     debug::print(&query(x"", usdt_addr, params));
    //
    //     // let multicall_bytecode = x"608060405234801561001057600080fd5b5061066e806100206000396000f3fe608060405234801561001057600080fd5b50600436106100885760003560e01c806372425d9d1161005b57806372425d9d146100e757806386d516e8146100ef578063a8b0574e146100f7578063ee82ac5e1461010c57610088565b80630f28c97d1461008d578063252dba42146100ab57806327e86d6e146100cc5780634d2301cc146100d4575b600080fd5b61009561011f565b6040516100a2919061051e565b60405180910390f35b6100be6100b93660046103b6565b610123565b6040516100a292919061052c565b610095610231565b6100956100e2366004610390565b61023a565b610095610247565b61009561024b565b6100ff61024f565b6040516100a2919061050a565b61009561011a3660046103eb565b610253565b4290565b60006060439150825160405190808252806020026020018201604052801561015f57816020015b606081526020019060019003908161014a5790505b50905060005b835181101561022b576000606085838151811061017e57fe5b6020026020010151600001516001600160a01b031686848151811061019f57fe5b6020026020010151602001516040516101b891906104fe565b6000604051808303816000865af19150503d80600081146101f5576040519150601f19603f3d011682016040523d82523d6000602084013e6101fa565b606091505b50915091508161020957600080fd5b8084848151811061021657fe5b60209081029190910101525050600101610165565b50915091565b60001943014090565b6001600160a01b03163190565b4490565b4590565b4190565b4090565b600061026382356105d4565b9392505050565b600082601f83011261027b57600080fd5b813561028e61028982610573565b61054c565b81815260209384019390925082018360005b838110156102cc57813586016102b68882610325565b84525060209283019291909101906001016102a0565b5050505092915050565b600082601f8301126102e757600080fd5b81356102f561028982610594565b9150808252602083016020830185838301111561031157600080fd5b61031c8382846105ee565b50505092915050565b60006040828403121561033757600080fd5b610341604061054c565b9050600061034f8484610257565b825250602082013567ffffffffffffffff81111561036c57600080fd5b610378848285016102d6565b60208301525092915050565b600061026382356105df565b6000602082840312156103a257600080fd5b60006103ae8484610257565b949350505050565b6000602082840312156103c857600080fd5b813567ffffffffffffffff8111156103df57600080fd5b6103ae8482850161026a565b6000602082840312156103fd57600080fd5b60006103ae8484610384565b60006102638383610497565b61041e816105d4565b82525050565b600061042f826105c2565b61043981856105c6565b93508360208202850161044b856105bc565b60005b84811015610482578383038852610466838351610409565b9250610471826105bc565b60209890980197915060010161044e565b50909695505050505050565b61041e816105df565b60006104a2826105c2565b6104ac81856105c6565b93506104bc8185602086016105fa565b6104c58161062a565b9093019392505050565b60006104da826105c2565b6104e481856105cf565b93506104f48185602086016105fa565b9290920192915050565b600061026382846104cf565b602081016105188284610415565b92915050565b60208101610518828461048e565b6040810161053a828561048e565b81810360208301526103ae8184610424565b60405181810167ffffffffffffffff8111828210171561056b57600080fd5b604052919050565b600067ffffffffffffffff82111561058a57600080fd5b5060209081020190565b600067ffffffffffffffff8211156105ab57600080fd5b506020601f91909101601f19160190565b60200190565b5190565b90815260200190565b919050565b6000610518826105e2565b90565b6001600160a01b031690565b82818337506000910152565b60005b838110156106155781810151838201526020016105fd565b83811115610624576000848401525b50505050565b601f01601f19169056fea265627a7a72305820978cd44d5ce226bebdf172bdf24918753b9e111e3803cb6249d3ca2860b7a47f6c6578706572696d656e74616cf50037";
    //     // let multicall_addr = execute(sender, ZERO_ADDR, 14, multicall_bytecode, 0);
    //     // debug::print(&multicall_addr);
    //     // let mulicall_params = x"252dba420000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000200000000000000000000000009c4aae49118b26f5f4efa5865e6bfcc2cfd6a94b0000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002470a08231000000000000000000000000892a2b7cf919760e148a0d33c1eb0f44d3b383f800000000000000000000000000000000000000000000000000000000";
    //     // debug::print(&utf8(b"call multicall"));
    //     // debug::print(&query(x"", multicall_addr, mulicall_params));
    //
    //     // debug::print(&view(x"", multicall_addr, mulicall_params));
    //     // call(x"40c10f19000000000000000000000000892a2b7cf919760e148a0d33c1eb0f44d3b383f80000000000000000000000000000000000000000000000000000000000000064");
    //
    // }

    #[test]
    fun test_simple_deploy() acquires Account, ContractEvent {
        let sender = x"054ecb78d0276cf182514211d0c21fe46590b654";
        create_account_if_not_exist(create_resource_address(&@aptos_framework, sender));
        let weth_bytecode = x"60606040526040805190810160405280600d81526020017f57726170706564204574686572000000000000000000000000000000000000008152506000908051906020019061004f9291906100c8565b506040805190810160405280600481526020017f57455448000000000000000000000000000000000000000000000000000000008152506001908051906020019061009b9291906100c8565b506012600260006101000a81548160ff021916908360ff16021790555034156100c357600080fd5b61016d565b828054600181600116156101000203166002900490600052602060002090601f016020900481019282601f1061010957805160ff1916838001178555610137565b82800160010185558215610137579182015b8281111561013657825182559160200191906001019061011b565b5b5090506101449190610148565b5090565b61016a91905b8082111561016657600081600090555060010161014e565b5090565b90565b610c348061017c6000396000f3006060604052600436106100af576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff16806306fdde03146100b9578063095ea7b31461014757806318160ddd146101a157806323b872dd146101ca5780632e1a7d4d14610243578063313ce5671461026657806370a082311461029557806395d89b41146102e2578063a9059cbb14610370578063d0e30db0146103ca578063dd62ed3e146103d4575b6100b7610440565b005b34156100c457600080fd5b6100cc6104dd565b6040518080602001828103825283818151815260200191508051906020019080838360005b8381101561010c5780820151818401526020810190506100f1565b50505050905090810190601f1680156101395780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b341561015257600080fd5b610187600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061057b565b604051808215151515815260200191505060405180910390f35b34156101ac57600080fd5b6101b461066d565b6040518082815260200191505060405180910390f35b34156101d557600080fd5b610229600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061068c565b604051808215151515815260200191505060405180910390f35b341561024e57600080fd5b61026460048080359060200190919050506109d9565b005b341561027157600080fd5b610279610b05565b604051808260ff1660ff16815260200191505060405180910390f35b34156102a057600080fd5b6102cc600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610b18565b6040518082815260200191505060405180910390f35b34156102ed57600080fd5b6102f5610b30565b6040518080602001828103825283818151815260200191508051906020019080838360005b8381101561033557808201518184015260208101905061031a565b50505050905090810190601f1680156103625780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b341561037b57600080fd5b6103b0600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035906020019091905050610bce565b604051808215151515815260200191505060405180910390f35b6103d2610440565b005b34156103df57600080fd5b61042a600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610be3565b6040518082815260200191505060405180910390f35b34600360003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055503373ffffffffffffffffffffffffffffffffffffffff167fe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c346040518082815260200191505060405180910390a2565b60008054600181600116156101000203166002900480601f0160208091040260200160405190810160405280929190818152602001828054600181600116156101000203166002900480156105735780601f1061054857610100808354040283529160200191610573565b820191906000526020600020905b81548152906001019060200180831161055657829003601f168201915b505050505081565b600081600460003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925846040518082815260200191505060405180910390a36001905092915050565b60003073ffffffffffffffffffffffffffffffffffffffff1631905090565b600081600360008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054101515156106dc57600080fd5b3373ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff16141580156107b457507fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600460008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205414155b156108cf5781600460008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020541015151561084457600080fd5b81600460008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055505b81600360008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600360008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055508273ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a3600190509392505050565b80600360003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205410151515610a2757600080fd5b80600360003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055503373ffffffffffffffffffffffffffffffffffffffff166108fc829081150290604051600060405180830381858888f193505050501515610ab457600080fd5b3373ffffffffffffffffffffffffffffffffffffffff167f7fcf532c15f0a6db0bd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65826040518082815260200191505060405180910390a250565b600260009054906101000a900460ff1681565b60036020528060005260406000206000915090505481565b60018054600181600116156101000203166002900480601f016020809104026020016040519081016040528092919081815260200182805460018160011615610100020316600290048015610bc65780601f10610b9b57610100808354040283529160200191610bc6565b820191906000526020600020905b815481529060010190602001808311610ba957829003601f168201915b505050505081565b6000610bdb33848461068c565b905092915050565b60046020528160005260406000206020528060005260406000206000915091505054815600a165627a7a72305820deb4c2ccab3c2fdca32ab3f46728389c2fe2c165d5fafa07661e4e004f6c344a0029";
        let weth_addr = execute(sender, x"", 0, weth_bytecode, 0);
        debug::print(&weth_addr);

        let grid_byte_code = x"60c06040523480156200001157600080fd5b50604051620031dd380380620031dd833981016040819052620000349162000331565b6200003f33620000ea565b62000055826200013c60201b620009381760201c565b6200008e5760405162461bcd60e51b815260206004820152600560248201526447465f4e4360d81b604482015260640160405180910390fd5b6040516200009c9062000267565b604051809103906000f080158015620000b9573d6000803e3d6000fd5b506001600160a01b03908116608052821660a052620000d76200014b565b620000e2816200024e565b50506200046e565b600580546001600160a01b038381166001600160a01b0319831681179093556040519116919082907f8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e090600090a35050565b6001600160a01b03163b151590565b6001600081815260066020527f3e5fec24aa4dc4e5aee2e025e51e1392c72a2500577559fae9665c6d52bd6a31805462ffffff19166064908117909155604051909291600080516020620031bd83398151915291a36005600081815260066020527fbfd358e93f18da3ed276c3afdbdba00b8f0b6008a03476a6a86bd6320ee6938b805462ffffff19166101f4908117909155604051909291600080516020620031bd83398151915291a3601e600081815260066020527fb6ba906ff52451a7a924e2eaeb8aea3ebee7350a8703e5e417edb25358c7dcc1805462ffffff1916610bb8908117909155604051909291600080516020620031bd83398151915291a3565b80516200026390600090602084019062000275565b5050565b611a4c806200177183390190565b828054620002839062000431565b90600052602060002090601f016020900481019282620002a75760008555620002f2565b82601f10620002c257805160ff1916838001178555620002f2565b82800160010185558215620002f2579182015b82811115620002f2578251825591602001919060010190620002d5565b506200030092915062000304565b5090565b5b8082111562000300576000815560010162000305565b634e487b7160e01b600052604160045260246000fd5b600080604083850312156200034557600080fd5b82516001600160a01b03811681146200035d57600080fd5b602084810151919350906001600160401b03808211156200037d57600080fd5b818601915086601f8301126200039257600080fd5b815181811115620003a757620003a76200031b565b604051601f8201601f19908116603f01168101908382118183101715620003d257620003d26200031b565b816040528281528986848701011115620003eb57600080fd5b600093505b828410156200040f5784840186015181850187015292850192620003f0565b82841115620004215760008684830101525b8096505050505050509250929050565b600181811c908216806200044657607f821691505b602082108114156200046857634e487b7160e01b600052602260045260246000fd5b50919050565b60805160a0516112d0620004a16000396000818161018201526106c601526000818160d301526106a501526112d06000f3fe608060405234801561001057600080fd5b50600436106100c95760003560e01c8063715018a611610081578063c841d7061161005b578063c841d7061461028d578063f2fde38b146102a0578063fd001ef0146102b357600080fd5b8063715018a6146101a457806389035730146101ae5780638da5cb5b1461026f57600080fd5b8063345d5db8116100b2578063345d5db81461013257806347af52211461014757806350879c1c1461017d57600080fd5b80632630c12f146100ce5780632ca275c01461011f575b600080fd5b6100f57f000000000000000000000000000000000000000000000000000000000000000081565b60405173ffffffffffffffffffffffffffffffffffffffff90911681526020015b60405180910390f35b6100f561012d366004610f4d565b6102fa565b61013a6107c6565b6040516101169190610fc0565b61016a610155366004611011565b60066020526000908152604090205460020b81565b60405160029190910b8152602001610116565b6100f57f000000000000000000000000000000000000000000000000000000000000000081565b6101ac610854565b005b6001546002805460035460045461021f9473ffffffffffffffffffffffffffffffffffffffff9081169484821694740100000000000000000000000000000000000000008104820b947701000000000000000000000000000000000000000000000090910490910b92908216911686565b6040805173ffffffffffffffffffffffffffffffffffffffff97881681529587166020870152600294850b908601529190920b6060840152908316608083015290911660a082015260c001610116565b60055473ffffffffffffffffffffffffffffffffffffffff166100f5565b6101ac61029b366004611062565b610868565b6101ac6102ae366004611131565b610884565b6100f56102c1366004610f4d565b600760209081526000938452604080852082529284528284209052825290205473ffffffffffffffffffffffffffffffffffffffff1681565b60008061031c60055473ffffffffffffffffffffffffffffffffffffffff1690565b73ffffffffffffffffffffffffffffffffffffffff161461039e576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600560248201527f47465f4e4900000000000000000000000000000000000000000000000000000060448201526064015b60405180910390fd5b73ffffffffffffffffffffffffffffffffffffffff84163b61041c576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600560248201527f47465f4e430000000000000000000000000000000000000000000000000000006044820152606401610395565b73ffffffffffffffffffffffffffffffffffffffff83163b61049a576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600560248201527f47465f4e430000000000000000000000000000000000000000000000000000006044820152606401610395565b8273ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff161415610530576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600660248201527f47465f54414400000000000000000000000000000000000000000000000000006044820152606401610395565b73ffffffffffffffffffffffffffffffffffffffff848116600090815260076020908152604080832087851684528252808320600287900b845290915290205416156105d8576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600660248201527f47465f50414500000000000000000000000000000000000000000000000000006044820152606401610395565b600282810b60009081526006602052604081205490910b908113610658576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600660248201527f47465f524e4500000000000000000000000000000000000000000000000000006044820152606401610395565b6000808573ffffffffffffffffffffffffffffffffffffffff168773ffffffffffffffffffffffffffffffffffffffff1610610695578587610698565b86865b915091506106ea828287867f00000000000000000000000000000000000000000000000000000000000000007f0000000000000000000000000000000000000000000000000000000000000000610954565b73ffffffffffffffffffffffffffffffffffffffff88811660008181526007602081815260408084208d871680865290835281852060028e900b80875290845282862080548a8a167fffffffffffffffffffffffff000000000000000000000000000000000000000091821681179092559287529484528286209686529583528185208686528352938190208054909416831790935591519081529397509092848316928616917ffe23981920c53fdfe858f29ee2c426fb8bf164162938c157cdf27bac46fccab7910160405180910390a45050509392505050565b600080546107d39061114c565b80601f01602080910402602001604051908101604052809291908181526020018280546107ff9061114c565b801561084c5780601f106108215761010080835404028352916020019161084c565b820191906000526020600020905b81548152906001019060200180831161082f57829003601f168201915b505050505081565b61085c610be0565b6108666000610c61565b565b610870610be0565b61087981610cd8565b610881610854565b50565b61088c610be0565b73ffffffffffffffffffffffffffffffffffffffff811661092f576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152602660248201527f4f776e61626c653a206e6577206f776e657220697320746865207a65726f206160448201527f64647265737300000000000000000000000000000000000000000000000000006064820152608401610395565b61088181610c61565b73ffffffffffffffffffffffffffffffffffffffff163b151590565b6040805160c08101825273ffffffffffffffffffffffffffffffffffffffff808916808352888216602080850182905260028a810b8688015289810b60608701528885166080870181905294881660a0909601869052600180547fffffffffffffffffffffffff00000000000000000000000000000000000000009081169095179055805462ffffff808c1677010000000000000000000000000000000000000000000000027fffffffffffff000000ffffffffffffffffffffffffffffffffffffffffffffff918e1674010000000000000000000000000000000000000000027fffffffffffffffffff0000000000000000000000000000000000000000000000909316909517919091171692909217909155600380548316909317909255600480549091169092179091559051600091610b71918391610acb918b918b918b910173ffffffffffffffffffffffffffffffffffffffff938416815291909216602082015260029190910b604082015260600190565b6040516020818303038152906040528051906020012060008054610aee9061114c565b80601f0160208091040260200160405190810160405280929190818152602001828054610b1a9061114c565b8015610b675780601f10610b3c57610100808354040283529160200191610b67565b820191906000526020600020905b815481529060010190602001808311610b4a57829003601f168201915b5050505050610d14565b600180547fffffffffffffffffffffffff0000000000000000000000000000000000000000908116909155600280547fffffffffffff00000000000000000000000000000000000000000000000000001690556003805482169055600480549091169055979650505050505050565b60055473ffffffffffffffffffffffffffffffffffffffff163314610866576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820181905260248201527f4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e65726044820152606401610395565b6005805473ffffffffffffffffffffffffffffffffffffffff8381167fffffffffffffffffffffffff0000000000000000000000000000000000000000831681179093556040519116919082907f8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e090600090a35050565b600081604051602001610cec9291906111bc565b60405160208183030381529060405260009080519060200190610d10929190610e79565b5050565b60008084471015610d81576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601d60248201527f437265617465323a20696e73756666696369656e742062616c616e63650000006044820152606401610395565b8251610de9576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820181905260248201527f437265617465323a2062797465636f6465206c656e677468206973207a65726f6044820152606401610395565b8383516020850187f5905073ffffffffffffffffffffffffffffffffffffffff8116610e71576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601960248201527f437265617465323a204661696c6564206f6e206465706c6f79000000000000006044820152606401610395565b949350505050565b828054610e859061114c565b90600052602060002090601f016020900481019282610ea75760008555610eed565b82601f10610ec057805160ff1916838001178555610eed565b82800160010185558215610eed579182015b82811115610eed578251825591602001919060010190610ed2565b50610ef9929150610efd565b5090565b5b80821115610ef95760008155600101610efe565b803573ffffffffffffffffffffffffffffffffffffffff81168114610f3657600080fd5b919050565b8035600281900b8114610f3657600080fd5b600080600060608486031215610f6257600080fd5b610f6b84610f12565b9250610f7960208501610f12565b9150610f8760408501610f3b565b90509250925092565b60005b83811015610fab578181015183820152602001610f93565b83811115610fba576000848401525b50505050565b6020815260008251806020840152610fdf816040850160208701610f90565b601f017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0169190910160400192915050565b60006020828403121561102357600080fd5b61102c82610f3b565b9392505050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052604160045260246000fd5b60006020828403121561107457600080fd5b813567ffffffffffffffff8082111561108c57600080fd5b818401915084601f8301126110a057600080fd5b8135818111156110b2576110b2611033565b604051601f82017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0908116603f011681019083821181831017156110f8576110f8611033565b8160405282815287602084870101111561111157600080fd5b826020860160208301376000928101602001929092525095945050505050565b60006020828403121561114357600080fd5b61102c82610f12565b600181811c9082168061116057607f821691505b6020821081141561119a577f4e487b7100000000000000000000000000000000000000000000000000000000600052602260045260246000fd5b50919050565b600081516111b2818560208601610f90565b9290920192915050565b600080845481600182811c9150808316806111d857607f831692505b6020808410821415611211577f4e487b710000000000000000000000000000000000000000000000000000000086526022600452602486fd5b818015611225576001811461125457611281565b7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00861689528489019650611281565b60008b81526020902060005b868110156112795781548b820152908501908301611260565b505084890196505b50505050505061129181856111a0565b9594505050505056fea2646970667358221220b1e2306a77cee151ba8f5cd58b467390ab5fd5aee6c0bcb48f1bfdd37da0c5e564736f6c6343000809003360a060405234801561001057600080fd5b5033608052608051611a166100366000396000818160d001526102480152611a166000f3fe608060405234801561001057600080fd5b50600436106100875760003560e01c8063a2d263f01161005b578063a2d263f014610152578063a7db66b014610172578063cc2ef58c146101d1578063ce5659ea146101e457600080fd5b8062b20ce41461008c57806303a7dcdc146100cb5780639dce6651146101175780639fb482b31461012c575b600080fd5b61009f61009a36600461159a565b6101f7565b6040805163ffffffff909416845260069290920b60208401521515908201526060015b60405180910390f35b6100f27f000000000000000000000000000000000000000000000000000000000000000081565b60405173ffffffffffffffffffffffffffffffffffffffff90911681526020016100c2565b61012a6101253660046115d5565b610241565b005b61013f61013a366004611632565b61030c565b60405160069190910b81526020016100c2565b61016561016036600461166b565b610490565b6040516100c291906116f3565b6101ac61018036600461173a565b60006020819052908152604090205461ffff808216916201000081048216916401000000009091041683565b6040805161ffff948516815292841660208401529216918101919091526060016100c2565b61012a6101df366004611757565b6106c8565b61012a6101f2366004611775565b6106d7565b60016020528160005260406000208161ffff811061021457600080fd5b015463ffffffff81169250640100000000810460060b91506b010000000000000000000000900460ff1683565b60006102777f00000000000000000000000000000000000000000000000000000000000000006102728686866108bb565b610964565b905073ffffffffffffffffffffffffffffffffffffffff811633146102fd576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600560248201527f504f5f494300000000000000000000000000000000000000000000000000000060448201526064015b60405180910390fd5b61030681610a99565b50505050565b73ffffffffffffffffffffffffffffffffffffffff82166000908152602081815260408083208151606081018352905461ffff80821683526201000082048116948301859052640100000000909104169181019190915290600111156103ce576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600560248201527f504f5f555200000000000000000000000000000000000000000000000000000060448201526064016102f4565b60008473ffffffffffffffffffffffffffffffffffffffff16633850c7bd6040518163ffffffff1660e01b815260040160806040518083038186803b15801561041657600080fd5b505afa15801561042a573d6000803e3d6000fd5b505050506040513d601f19601f8201168201806040525081019061044e91906117aa565b505073ffffffffffffffffffffffffffffffffffffffff8716600090815260016020526040902090925061048791508390834288610c3b565b95945050505050565b73ffffffffffffffffffffffffffffffffffffffff831660009081526020818152604091829020825160608181018552915461ffff808216835262010000820481169483018590526401000000009091041693810193909352919060011115610555576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600560248201527f504f5f555200000000000000000000000000000000000000000000000000000060448201526064016102f4565b8267ffffffffffffffff81111561056e5761056e61180e565b604051908082528060200260200182016040528015610597578160200160208202803683370190505b50915060008573ffffffffffffffffffffffffffffffffffffffff16633850c7bd6040518163ffffffff1660e01b815260040160806040518083038186803b1580156105e257600080fd5b505afa1580156105f6573d6000803e3d6000fd5b505050506040513d601f19601f8201168201806040525081019061061a91906117aa565b505073ffffffffffffffffffffffffffffffffffffffff881660009081526001602052604081209193504292505b868110156106bc57610683858386868c8c878181106106695761066961183d565b905060200201602081019061067e919061186c565b610c3b565b8682815181106106955761069561183d565b602002602001019060060b908160060b8152505080806106b4906118b8565b915050610648565b50505050509392505050565b6106d3338383610d90565b5050565b73ffffffffffffffffffffffffffffffffffffffff82166000908152602081905260409020805460016201000090910461ffff161015610773576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600560248201527f504f5f555200000000000000000000000000000000000000000000000000000060448201526064016102f4565b805461ffff640100000000909104811690831681106107925750505050565b805b8361ffff168161ffff1610156108275773ffffffffffffffffffffffffffffffffffffffff8516600090815260016020819052604090912061ffff8084169081106107e1576107e161183d565b0180547fffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000001663ffffffff929092169190911790558061081f816118f1565b915050610794565b5081547fffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffffffff1664010000000061ffff858116918202929092178455604080519284168352602083019190915273ffffffffffffffffffffffffffffffffffffffff8616917fd5af696270ef03e041598b42b536784a4886e5ca0f99c1e903fb57b193d40780910160405180910390a250505050565b60408051606081018252600080825260208201819052918101919091528273ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff161115610910579192915b60405180606001604052808573ffffffffffffffffffffffffffffffffffffffff1681526020018473ffffffffffffffffffffffffffffffffffffffff1681526020018360020b81525090505b9392505050565b6000816020015173ffffffffffffffffffffffffffffffffffffffff16826000015173ffffffffffffffffffffffffffffffffffffffff16106109a657600080fd5b8151602080840151604080860151815173ffffffffffffffffffffffffffffffffffffffff95861681860152949092168482015260029190910b6060808501919091528151808503820181526080850183528051908401207fff0000000000000000000000000000000000000000000000000000000000000060a08601529087901b7fffffffffffffffffffffffffffffffffffffffff0000000000000000000000001660a185015260b58401527f884a6891a166f885bf6f0a3b330a25e41d1761a5aa091110a229d9a0e34b2c3660d5808501919091528151808503909101815260f59093019052815191012061095d565b73ffffffffffffffffffffffffffffffffffffffff811660009081526020819052604090205462010000900461ffff1615610b30576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600560248201527f504f5f415200000000000000000000000000000000000000000000000000000060448201526064016102f4565b73ffffffffffffffffffffffffffffffffffffffff811660008181526020818152604080832080547fffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffff1664010001000017905580516060810182524263ffffffff168152808301849052600181830181905294845293909152812090825191018054602084015160409094015115156b010000000000000000000000027fffffffffffffffffffffffffffffffffffffffff00ffffffffffffffffffffff66ffffffffffffff909516640100000000027fffffffffffffffffffffffffffffffffffffffffff000000000000000000000090921663ffffffff90941693909317179290921617905550565b600063ffffffff8216610ce257600085876000015161ffff1661ffff8110610c6557610c6561183d565b60408051606081018252919092015463ffffffff808216808452640100000000830460060b60208501526b01000000000000000000000090920460ff161515938301939093529092509085161415610cc257602001519050610487565b8060000151840363ffffffff168560020b02816020015101915050610487565b818303600080610cf589898989876110c4565b91509150816000015163ffffffff168363ffffffff161415610d1f57506020015191506104879050565b805163ffffffff84811691161415610d3f57602001519250610487915050565b8151815160208085015190840151838703936000930360030b9163ffffffff8516910360060b02600a0b81610d7657610d76611913565b059050808460200151019550505050505095945050505050565b73ffffffffffffffffffffffffffffffffffffffff8316600090815260208181526040918290208251606081018452905461ffff80821683526201000082048116938301849052640100000000909104169281019290925260011115610e52576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600560248201527f504f5f555200000000000000000000000000000000000000000000000000000060448201526064016102f4565b73ffffffffffffffffffffffffffffffffffffffff84166000908152600160205260408120825161ffff908116908110610e8e57610e8e61183d565b0180546040840151845192935063ffffffff90911685039160009161ffff908116916001011681610ec157610ec1611913565b06905060405180606001604052808663ffffffff1681526020018363ffffffff168860020b028560000160049054906101000a900460060b0160060b815260200160011515815250600160008973ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000208261ffff1661ffff8110610f5e57610f5e61183d565b82519101805460208085015160409095015115156b010000000000000000000000027fffffffffffffffffffffffffffffffffffffffff00ffffffffffffffffffffff66ffffffffffffff909616640100000000027fffffffffffffffffffffffffffffffffffffffffff000000000000000000000090931663ffffffff90951694909417919091179390931691909117905584015161ffff828116911614156110655760408085015173ffffffffffffffffffffffffffffffffffffffff89166000908152602081905291909120805461ffff90921662010000027fffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff9092169190911790555b73ffffffffffffffffffffffffffffffffffffffff96909616600090815260208190526040902080547fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00001661ffff909716969096179095555050505050565b6040805160608101825260008082526020820181905291810191909152604080516060810182526000808252602082018190529181019190915285876000015161ffff1661ffff81106111195761111961183d565b60408051606081018252919092015463ffffffff8116808352640100000000820460060b60208401526b01000000000000000000000090910460ff16151592820192909252925061116c908590856112b9565b156111ce578263ffffffff16826000015163ffffffff16146111c95760405180606001604052808463ffffffff1681526020018360000151850363ffffffff168760020b0284602001510160060b81526020016000151581525091505b6112af565b6020870151875160009188916111e5906001611942565b6111ef9190611968565b61ffff1661ffff81106112045761120461183d565b0180549091506b010000000000000000000000900460ff166112235750855b805461123790869063ffffffff16866112b9565b61129d576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600660248201527f504f5f53544c000000000000000000000000000000000000000000000000000060448201526064016102f4565b6112a98888878761137c565b92509250505b9550959350505050565b60008363ffffffff168363ffffffff16111580156112e357508363ffffffff168263ffffffff1611155b156112ff578163ffffffff168363ffffffff161115905061095d565b60008463ffffffff168463ffffffff1611611327578363ffffffff166401000000000161132f565b8363ffffffff165b64ffffffffff16905060008563ffffffff168463ffffffff1611611360578363ffffffff1664010000000001611368565b8363ffffffff165b64ffffffffff169091111595945050505050565b60408051606080820183526000808352602080840182905283850182905284519283018552818352828101829052938201819052928701518751929391926113c5906001611942565b6113cf9190611968565b61ffff16905060006001886020015161ffff16836113ed9190611989565b6113f791906119a1565b905060005b60026114088385611989565b61141291906119b8565b905087896020015161ffff168261142991906119cc565b61ffff811061143a5761143a61183d565b60408051606081018252919092015463ffffffff81168252640100000000810460060b60208301526b010000000000000000000000900460ff16151591810182905295506114945761148d816001611989565b92506113fc565b6020890151889061ffff166114aa836001611989565b6114b491906119cc565b61ffff81106114c5576114c561183d565b60408051606081018252929091015463ffffffff81168352640100000000810460060b602084015260ff6b01000000000000000000000090910416151590820152855190945060009061151a908990896112b9565b90508080156115335750611533888887600001516112b9565b15611541575050505061156c565b80611558576115516001836119a1565b9250611566565b611563826001611989565b93505b506113fc565b94509492505050565b73ffffffffffffffffffffffffffffffffffffffff8116811461159757600080fd5b50565b600080604083850312156115ad57600080fd5b82356115b881611575565b946020939093013593505050565b8060020b811461159757600080fd5b6000806000606084860312156115ea57600080fd5b83356115f581611575565b9250602084013561160581611575565b91506040840135611615816115c6565b809150509250925092565b63ffffffff8116811461159757600080fd5b6000806040838503121561164557600080fd5b823561165081611575565b9150602083013561166081611620565b809150509250929050565b60008060006040848603121561168057600080fd5b833561168b81611575565b9250602084013567ffffffffffffffff808211156116a857600080fd5b818601915086601f8301126116bc57600080fd5b8135818111156116cb57600080fd5b8760208260051b85010111156116e057600080fd5b6020830194508093505050509250925092565b6020808252825182820181905260009190848201906040850190845b8181101561172e57835160060b8352928401929184019160010161170f565b50909695505050505050565b60006020828403121561174c57600080fd5b813561095d81611575565b6000806040838503121561176a57600080fd5b8235611650816115c6565b6000806040838503121561178857600080fd5b823561179381611575565b9150602083013561ffff8116811461166057600080fd5b600080600080608085870312156117c057600080fd5b84516117cb81611575565b60208601519094506117dc816115c6565b60408601519093506117ed81611620565b6060860151909250801515811461180357600080fd5b939692955090935050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052604160045260246000fd5b7f4e487b7100000000000000000000000000000000000000000000000000000000600052603260045260246000fd5b60006020828403121561187e57600080fd5b813561095d81611620565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052601160045260246000fd5b60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8214156118ea576118ea611889565b5060010190565b600061ffff8083168181141561190957611909611889565b6001019392505050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052601260045260246000fd5b600061ffff80831681851680830382111561195f5761195f611889565b01949350505050565b600061ffff8084168061197d5761197d611913565b92169190910692915050565b6000821982111561199c5761199c611889565b500190565b6000828210156119b3576119b3611889565b500390565b6000826119c7576119c7611913565b500490565b6000826119db576119db611913565b50069056fea2646970667358221220498a2ec8acb58747080078f85b7907ecf4aaeb037329da5511627d5101ff9a1364736f6c6343000809003394bd7616b3e0872dc5005ad73564bfaeec12f1932d85d8e471689e86f79c46590000000000000000000000006fd918a961f940d7a497664689cf592adb84c539000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000061aa6101406040523480156200001257600080fd5b50336001600160a01b031663890357306040518163ffffffff1660e01b815260040160c06040518083038186803b1580156200004d57600080fd5b505afa15801562000062573d6000803e3d6000fd5b505050506040513d601f19601f82011682018060405250810190620000889190620000ec565b6001600160a01b0390811660e05290811661010052600291820b6101205291900b60c05290811660a052166080526200016d565b80516001600160a01b0381168114620000d457600080fd5b919050565b8051600281900b8114620000d457600080fd5b60008060008060008060c087890312156200010657600080fd5b6200011187620000bc565b95506200012160208801620000bc565b94506200013160408801620000d9565b93506200014160608801620000d9565b92506200015160808801620000bc565b91506200016160a08801620000bc565b90509295509295509295565b60805160a05160c05160e0516101005161012051615f3e6200026c600039600081816103400152611bb2015260008181610b4c015261160f01526000613f410152600081816104da0152818161097001528181610a35015281816115e601528181611eee01528181612e2601528181612e5e01526141ec0152600081816106d301528181610ded015281816115be0152818161227b015281816122bc015281816126a201528181612837015281816129010152612b2301526000818161018c01528181610db2015281816115960152818161225a015281816122dd01528181612564015281816127b6015281816128c60152612b4c0152615f3e6000f3fe60806040526004361061016e5760003560e01c80637e071773116100cb578063b703179d1161007f578063dd5f8a7b11610059578063dd5f8a7b146106f5578063f12e768c14610715578063f8421a311461073557600080fd5b8063b703179d1461063a578063d18b83d114610667578063d21220a7146106c157600080fd5b80638455c01d116100b05780638455c01d14610564578063a54cfb2314610584578063a85c38ef146105a457600080fd5b80637e071773146104fc57806380281adb1461053757600080fd5b8063490e6cbc1161012257806360d49d531161010757806360d49d53146103f8578063624ac9a71461041857806371e21495146104c857600080fd5b8063490e6cbc1461037557806356ebe63c1461039757600080fd5b8063285d937911610153578063285d9379146102005780633850c7bd1461028a57806343f0179b1461032e57600080fd5b80630dfe16811461017a578063128acb08146101cb57600080fd5b3661017557005b600080fd5b34801561018657600080fd5b506101ae7f000000000000000000000000000000000000000000000000000000000000000081565b6040516001600160a01b0390911681526020015b60405180910390f35b3480156101d757600080fd5b506101eb6101e63660046151e6565b610763565b604080519283526020830191909152016101c2565b34801561020c57600080fd5b5061025a61021b36600461527d565b60026020526000908152604090205467ffffffffffffffff8082169168010000000000000000810490911690600160801b90046001600160801b031683565b6040805167ffffffffffffffff94851681529390921660208401526001600160801b0316908201526060016101c2565b34801561029657600080fd5b506000546102f4906001600160a01b0381169074010000000000000000000000000000000000000000810460020b9077010000000000000000000000000000000000000000000000810463ffffffff1690600160d81b900460ff1684565b604080516001600160a01b03909516855260029390930b602085015263ffffffff90911691830191909152151560608201526080016101c2565b34801561033a57600080fd5b506103627f000000000000000000000000000000000000000000000000000000000000000081565b60405160029190910b81526020016101c2565b34801561038157600080fd5b50610395610390366004615298565b610d34565b005b3480156103a357600080fd5b506103d86103b2366004615302565b6009602052600090815260409020546001600160801b0380821691600160801b90041682565b604080516001600160801b039384168152929091166020830152016101c2565b34801561040457600080fd5b506103d8610413366004615336565b610f4f565b34801561042457600080fd5b5061048561043336600461537b565b6008602052600090815260409020805460018201546002928301549282900b9260ff6301000000840416926001600160801b0364010000000090910481169280821692600160801b9091048216911686565b6040805160029790970b875294151560208701526001600160801b03938416948601949094529082166060850152811660808401521660a082015260c0016101c2565b3480156104d457600080fd5b506103627f000000000000000000000000000000000000000000000000000000000000000081565b34801561050857600080fd5b506105296105173660046153a5565b60036020526000908152604090205481565b6040519081526020016101c2565b34801561054357600080fd5b506105296105523660046153a5565b60046020526000908152604090205481565b34801561057057600080fd5b506103d861057f3660046153c8565b611045565b34801561059057600080fd5b506103d861059f36600461551b565b6110e7565b3480156105b057600080fd5b506106036105bf3660046155cd565b6006602052600090815260409020805460019091015467ffffffffffffffff8216916801000000000000000090046001600160a01b0316906001600160801b031683565b6040805167ffffffffffffffff90941684526001600160a01b0390921660208401526001600160801b0316908201526060016101c2565b34801561064657600080fd5b5061065a61065536600461567e565b61115b565b6040516101c29190615776565b34801561067357600080fd5b5061025a61068236600461527d565b60016020526000908152604090205467ffffffffffffffff8082169168010000000000000000810490911690600160801b90046001600160801b031683565b3480156106cd57600080fd5b506101ae7f000000000000000000000000000000000000000000000000000000000000000081565b34801561070157600080fd5b50610529610710366004615789565b61120e565b34801561072157600080fd5b506103d86107303660046155cd565b6112d5565b34801561074157600080fd5b50610755610750366004615820565b611407565b6040516101c29291906158e7565b600080856107b85760405162461bcd60e51b815260206004820152600560248201527f475f41535a00000000000000000000000000000000000000000000000000000060448201526064015b60405180910390fd5b604080516080810182526000546001600160a01b038116825274010000000000000000000000000000000000000000810460020b602083015277010000000000000000000000000000000000000000000000810463ffffffff1692820192909252600160d81b90910460ff1615156060820181905261087b5760405162461bcd60e51b81526004016107af9060208082526004908201527f475f474c00000000000000000000000000000000000000000000000000000000604082015260600190565b8761089e5780600001516001600160a01b0316866001600160a01b0316116108b8565b80600001516001600160a01b0316866001600160a01b0316105b6109045760405162461bcd60e51b815260206004820152600560248201527f475f504c4f00000000000000000000000000000000000000000000000000000060448201526064016107af565b6000805460ff60d81b1916815560408051610180810182528a1515815260208082018b9052918101839052606081018390526080810183905283516001600160a01b0390811660a0830152891660c0820152908301805160020b60e083015251610100820190610994907f00000000000000000000000000000000000000000000000000000000000000006118ea565b60020b81526000602082018190526040820181905260609091018190529091506109be8a15611924565b905060006109cc8b1561193a565b90505b6020830151158015906109e55750826101600151155b15610a9f5760e083015160a08401516101008501805160020b6000908152602085905260408120549151875191948594610a5a94899492939192600160801b9091046001600160801b03161515917f000000000000000000000000000000000000000000000000000000000000000091611950565b6001600160a01b039081166101408a015216610120880152909250905080610a83575050610a9f565b610a8f84848488611a80565b1515610160860152506109cf9050565b83600001516001600160a01b03168360a001516001600160a01b031614610c8457610acd8360a00151611f42565b600290810b60e0850181905260208601516000920b14801590610b0357504290508063ffffffff16856040015163ffffffff1614155b15610bfb5760208501516040517fcc2ef58c00000000000000000000000000000000000000000000000000000000815260029190910b600482015263ffffffff821660248201527f00000000000000000000000000000000000000000000000000000000000000006001600160a01b03169063cc2ef58c90604401600060405180830381600087803b158015610b9857600080fd5b505af1158015610bac573d6000803e3d6000fd5b5050600080547fffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffff167701000000000000000000000000000000000000000000000063ffffffff86160217905550505b5060a083015160e0840151600080546001600160a01b039093167fffffffffffffffffffffffff000000000000000000000000000000000000000062ffffff9093167401000000000000000000000000000000000000000002929092167fffffffffffffffffff0000000000000000000000000000000000000000000000909316929092171790555b610c90838d8a8a61222b565b90965094506001600160a01b038c16336001600160a01b03167f41e82c9c8c68651be91e14fa6bb6d577822b5f6b66fda7d7f365faed56e2855e88888760a001518860e00151604051610d08949392919093845260208401929092526001600160a01b0316604083015260020b606082015260800190565b60405180910390a350506000805460ff60d81b1916600160d81b17905550919890975095505050505050565b600054600160d81b900460ff16610d8f5760405162461bcd60e51b81526004016107af9060208082526004908201527f475f474c00000000000000000000000000000000000000000000000000000000604082015260600190565b6000805460ff60d81b19168155808515610dd857610dab612533565b9150610dd87f000000000000000000000000000000000000000000000000000000000000000088886125ec565b8415610e1357610de6612671565b9050610e137f000000000000000000000000000000000000000000000000000000000000000088876125ec565b6040517f7b17fb300000000000000000000000000000000000000000000000000000000081523390637b17fb3090610e519087908790600401615955565b600060405180830381600087803b158015610e6b57600080fd5b505af1158015610e7f573d6000803e3d6000fd5b505050506000806000881115610eb1576000610e99612533565b9050610ead610ea88683615998565b6126d9565b9250505b8615610ed4576000610ec1612671565b9050610ed0610ea88583615998565b9150505b60408051898152602081018990526001600160801b03848116828401528316606082015290516001600160a01b038b169133917fab4f19a9f2e46fd590cecef736d778467430de8fd1f41cd7a7e3d23df9a86f4c9181900360800190a350506000805460ff60d81b1916600160d81b17905550505050505050565b600080548190600160d81b900460ff16610fad5760405162461bcd60e51b81526004016107af9060208082526004908201527f475f474c00000000000000000000000000000000000000000000000000000000604082015260600190565b6000805460ff60d81b19168155338152600960205260409020610fd29086868661275c565b604080516001600160801b0380851682528316602082015281519395509193506001600160a01b0388169233927f38c069c2e9bc192f8cf4f1b85be791ccc0d04bb12c4ca71a3fbfe96ea0932dd592908290030190a36000805460ff60d81b1916600160d81b1790559094909350915050565b600080548190600160d81b900460ff166110a35760405162461bcd60e51b81526004016107af9060208082526004908201527f475f474c00000000000000000000000000000000000000000000000000000000604082015260600190565b6000805460ff60d81b191690556110b984612869565b90925090506110ca858383866128b1565b6000805460ff60d81b1916600160d81b1790559094909350915050565b600080548190600160d81b900460ff166111455760405162461bcd60e51b81526004016107af9060208082526004908201527f475f474c00000000000000000000000000000000000000000000000000000000604082015260600190565b6000805460ff60d81b191690556110b98461297f565b600054606090600160d81b900460ff166111b95760405162461bcd60e51b81526004016107af9060208082526004908201527f475f474c00000000000000000000000000000000000000000000000000000000604082015260600190565b6000805460ff60d81b191681558451602086015160408701516111dd929190612a2b565b602087015191935091506111f390828686612b17565b506000805460ff60d81b1916600160d81b1790559392505050565b60008054600160d81b900460ff1661126a5760405162461bcd60e51b81526004016107af9060208082526004908201527f475f474c00000000000000000000000000000000000000000000000000000000604082015260600190565b6000805460ff60d81b1916905561127f612d7a565b905061129e818560000151866020015187604001518860600151612d95565b6112bb846020015185606001516001600160801b03168585612b17565b6000805460ff60d81b1916600160d81b1790559392505050565b600080548190600160d81b900460ff166113335760405162461bcd60e51b81526004016107af9060208082526004908201527f475f474c00000000000000000000000000000000000000000000000000000000604082015260600190565b6000805460ff60d81b1916905561134983612869565b33600090815260096020526040902091935091506001600160801b038316156113a75780546113829084906001600160801b03166159af565b81546fffffffffffffffffffffffffffffffff19166001600160801b03919091161781555b6001600160801b038216156113ec5780546113d3908390600160801b90046001600160801b03166159af565b81546001600160801b03918216600160801b0291161781555b506000805460ff60d81b1916600160d81b1790559092909150565b60005460609081906001600160a01b0316156114655760405162461bcd60e51b815260206004820152600560248201527f475f47414900000000000000000000000000000000000000000000000000000060448201526064016107af565b84516114709061326e565b6114bc5760405162461bcd60e51b815260206004820152600560248201527f475f504f5200000000000000000000000000000000000000000000000000000060448201526064016107af565b6000856040015151116115115760405162461bcd60e51b815260206004820152600560248201527f475f4f4e4500000000000000000000000000000000000000000000000000000060448201526064016107af565b6000856060015151116115665760405162461bcd60e51b815260206004820152600560248201527f475f4f4e4500000000000000000000000000000000000000000000000000000060448201526064016107af565b6040517f9dce66510000000000000000000000000000000000000000000000000000000081526001600160a01b037f0000000000000000000000000000000000000000000000000000000000000000811660048301527f0000000000000000000000000000000000000000000000000000000000000000811660248301527f000000000000000000000000000000000000000000000000000000000000000060020b60448301527f00000000000000000000000000000000000000000000000000000000000000001690639dce665190606401600060405180830381600087803b15801561165357600080fd5b505af1158015611667573d6000803e3d6000fd5b50505050600061167a8660000151611f42565b6040805160808101825288516001600160a01b03908116808352600285900b60208085018290524263ffffffff168587018190526000606090960186905285547fffffffffffffffffff0000000000000000000000000000000000000000000000169093177401000000000000000000000000000000000000000062ffffff891602177fffffffff0000000000ffffffffffffffffffffffffffffffffffffffffffffff167701000000000000000000000000000000000000000000000090930260ff60d81b1916929092179093558a518451921682528101919091529192507f98636036cb66a9c19a37435efc1e90142190214e8abeb821bdba3f2990dd4c95910160405180910390a1600061179b876020015160018960400151612a2b565b809250819550505060006117b9886020015160008a60600151612a2b565b90945090506000806117c9612533565b6117d1612671565b915091506117dc3390565b6001600160a01b0316638f61c9f785858c8c6040518563ffffffff1660e01b815260040161180d94939291906159da565b600060405180830381600087803b15801561182757600080fd5b505af115801561183b573d6000803e3d6000fd5b5050505060008061184a612533565b611852612671565b9092509050856118628584615998565b101580156118795750846118768483615998565b10155b6118c55760405162461bcd60e51b815260206004820152600560248201527f475f54504600000000000000000000000000000000000000000000000000000060448201526064016107af565b50506000805460ff60d81b1916600160d81b1790555094989397509295505050505050565b60008160020b828360020b8560020b81611906576119066159fa565b070160020b81611918576119186159fa565b07830390505b92915050565b60008161193257600461191e565b600392915050565b60008161194857600261191e565b600192915050565b6000808080806119608888615a29565b905088156119fc5785156119b7576000611979886132ae565b90508a6001600160a01b0316816001600160a01b031610156119b157876001826119a2856132ae565b95509550955095505050611a72565b506119fc565b60006119c2826132ae565b90508a6001600160a01b0316816001600160a01b031611156119fa578760016119ea8a6132ae565b8395509550955095505050611a72565b505b85158015611a0f57508a60020b8160020b145b611a19578a611a1b565b865b9a505b611a278b61358a565b15611a7057611a388c8c8a896135cb565b90955093508315611a6857846001611a4f876132ae565b611a5a8b89016132ae565b945094509450945050611a72565b849a50611a1e565b505b975097509750979350505050565b604080516080810182526101208301516001600160a01b0390811682526101408401511660208201526000918101829052606081018290528251611ada578060200151611ad582600001518560a00151613795565b611af1565b8060000151611af182602001518560a001516137bf565b6001600160a01b03908116606084015216604082015282518015611b2f57508260c001516001600160a01b031681606001516001600160a01b031611155b80611b5e57508251158015611b5e57508260c001516001600160a01b031681606001516001600160a01b031610155b15611b6d576001915050611f3a565b600284900b60009081526020868152604080832060608501519185015160c0880151938801518254929594611bd69493909190600160801b90046001600160801b03167f00000000000000000000000000000000000000000000000000000000000000006137e0565b905080604001516001600160801b031660001415611bfa5760019350505050611f3a565b80602001518560400151611c0e9190615a70565b604086015260608082015190860151611c30916001600160801b031690615a70565b606086015260408101516080860151611c52916001600160801b031690615a70565b60808601526020850151600013611c9c5780606001516001600160801b0316611c7e8260200151613858565b8660200151611c8d9190615a88565b611c979190615a88565b611cb9565b80604001516001600160801b03168560200151611cb99190615afc565b602080870191909152825467ffffffffffffffff16600090815260088252604080822092840151908401516060850151611cf692859290916138f0565b8454604082015191925067ffffffffffffffff16907f700dec44bb198379f48560c2e4ea3ce1a6485d0beaf623dbcead52c7850ff3df90611d3f906001600160801b0316615b70565b835160808501516040805193845260208401929092526001600160801b03169082015260600160405180910390a260018201546001600160801b0316611eb657835468010000000000000000810467ffffffffffffffff166fffffffffffffffffffffffffffffffff1990911617845560608101516001600160801b031615611eb657835467ffffffffffffffff16600090815260086020908152604090912090820151606083015160a0840151611dfa92849290916138f0565b8554604082015191935067ffffffffffffffff16907f700dec44bb198379f48560c2e4ea3ce1a6485d0beaf623dbcead52c7850ff3df90611e43906001600160801b0316615b70565b845160808601516040805193845260208401929092526001600160801b03169082015260600160405180910390a260018101546001600160801b0316611eb457845468010000000000000000810467ffffffffffffffff166fffffffffffffffffffffffffffffffff199091161785555b505b5050604081015182546001600160801b03600160801b8083048216939093038082169384029190921617845590611f1257611f1289887f0000000000000000000000000000000000000000000000000000000000000000613ab7565b50516001600160a01b031660a0850152505050600282900b60e0820181905261010082015260005b949350505050565b600077ffffffffffffffffffffffffffffffffffffffff00000000602083901b166001600160801b03811160071b81811c67ffffffffffffffff811160061b90811c63ffffffff811160051b90811c61ffff811160041b90811c60ff8111600390811b91821c600f811160021b90811c918211600190811b92831c97908811961790941790921717909117171760808110611fe557607f810383901c9150611fef565b80607f0383901b91505b908002607f81811c60ff83811c9190911c800280831c81831c1c800280841c81841c1c800280851c81851c1c800280861c81861c1c800280871c81871c1c800280881c81881c1c800280891c81891c1c8002808a1c818a1c1c8002808b1c818b1c1c8002808c1c818c1c1c8002808d1c818d1c1c8002808e1c9c81901c9c909c1c80029c8d901c9e9d7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff808f0160401b60c09190911c678000000000000000161760c19b909b1c674000000000000000169a909a1760c29990991c672000000000000000169890981760c39790971c671000000000000000169690961760c49590951c670800000000000000169490941760c59390931c670400000000000000169290921760c69190911c670200000000000000161760c79190911c670100000000000000161760c89190911c6680000000000000161760c99190911c6640000000000000161760ca9190911c6620000000000000161760cb9190911c6610000000000000161760cc9190911c6608000000000000161760cd9190911c66040000000000001617691b13d180eb882abba64281027ffffffffffffffffffffffffffffffffffeb84dbf2a407dd93f221832f996e78b8101608090811d906fd9e63e52eeeb7828cf1af18004b842588301901d600281810b9083900b1461221c57886001600160a01b0316612201826132ae565b6001600160a01b03161115612216578161221e565b8061221e565b815b9998505050505050505050565b6000806000866060015187604001516122449190615a70565b608088015188519192509060009081906122ba577f00000000000000000000000000000000000000000000000000000000000000007f00000000000000000000000000000000000000000000000000000000000000006122a385613858565b6122ac90615b70565b6122b587613858565b612317565b7f00000000000000000000000000000000000000000000000000000000000000007f000000000000000000000000000000000000000000000000000000000000000061230586613858565b61230e86613858565b61231790615b70565b9098509650909250905061232c828a856125ec565b6040517f70a082310000000000000000000000000000000000000000000000000000000081523060048201526000906001600160a01b038316906370a082319060240160206040518083038186803b15801561238757600080fd5b505afa15801561239b573d6000803e3d6000fd5b505050506040513d601f19601f820116820180604052508101906123bf9190615ba9565b6040517f8870c4f80000000000000000000000000000000000000000000000000000000081529091503390638870c4f890612404908a908a908e908e906004016159da565b600060405180830381600087803b15801561241e57600080fd5b505af1158015612432573d6000803e3d6000fd5b50506040517f70a08231000000000000000000000000000000000000000000000000000000008152306004820152600092506001600160a01b03851691506370a082319060240160206040518083038186803b15801561249157600080fd5b505afa1580156124a5573d6000803e3d6000fd5b505050506040513d601f19601f820116820180604052508101906124c99190615ba9565b9050856124d68383615998565b10156125245760405162461bcd60e51b815260206004820152600560248201527f475f54524600000000000000000000000000000000000000000000000000000060448201526064016107af565b50505050505094509492505050565b6040517f70a082310000000000000000000000000000000000000000000000000000000081523060048201526000907f00000000000000000000000000000000000000000000000000000000000000006001600160a01b0316906370a08231906024015b60206040518083038186803b1580156125af57600080fd5b505afa1580156125c3573d6000803e3d6000fd5b505050506040513d601f19601f820116820180604052508101906125e79190615ba9565b905090565b604080516001600160a01b038416602482015260448082018490528251808303909101815260649091019091526020810180517bffffffffffffffffffffffffffffffffffffffffffffffffffffffff167fa9059cbb0000000000000000000000000000000000000000000000000000000017905261266c908490613b0a565b505050565b6040517f70a082310000000000000000000000000000000000000000000000000000000081523060048201526000907f00000000000000000000000000000000000000000000000000000000000000006001600160a01b0316906370a0823190602401612597565b60006001600160801b038211156127585760405162461bcd60e51b815260206004820152602760248201527f53616665436173743a2076616c756520646f65736e27742066697420696e203160448201527f323820626974730000000000000000000000000000000000000000000000000060648201526084016107af565b5090565b6000806001600160801b038416156127df5785546127849085906001600160801b0316613bef565b86546fffffffffffffffffffffffffffffffff1981166001600160801b0391821683900382161788559092506127df907f000000000000000000000000000000000000000000000000000000000000000090879085166125ec565b6001600160801b0383161561286057855461280b908490600160801b90046001600160801b0316613bef565b86546001600160801b03600160801b8083048216849003821602918116919091178855909150612860907f000000000000000000000000000000000000000000000000000000000000000090879084166125ec565b94509492505050565b60008060008060008061287b87613c10565b9350935093509350836128985761289281836159af565b836128a3565b826128a382846159af565b909890975095505050505050565b6001600160801b038316156128ec576128ec847f00000000000000000000000000000000000000000000000000000000000000008584613f37565b6001600160801b0382161561292757612927847f00000000000000000000000000000000000000000000000000000000000000008484613f37565b604080516001600160801b0385811682528416602082015281516001600160a01b0387169233927f38c069c2e9bc192f8cf4f1b85be791ccc0d04bb12c4ca71a3fbfe96ea0932dd5929081900390910190a350505050565b60008060005b8351811015612a25576000806000806129b68886815181106129a9576129a9615bc2565b6020026020010151613c10565b9350935093509350836129e757806129ce83896159af565b6129d891906159af565b6129e284886159af565b612a06565b6129f183886159af565b816129fc84896159af565b612a0691906159af565b8097508198505050505050508080612a1d90615bf1565b915050612985565b50915091565b60606000825167ffffffffffffffff811115612a4957612a4961540a565b604051908082528060200260200182016040528015612a72578160200160208202803683370190505b5091506000612a818451614027565b905060005b8451811015612b0d576000858281518110612aa357612aa3615bc2565b60200260200101519050612ac283898984600001518560200151612d95565b82858381518110612ad557612ad5615bc2565b6020908102919091018101919091528101516001938401939290920191612b05906001600160801b031685615a70565b935050612a86565b5050935093915050565b600080600086612b4a577f0000000000000000000000000000000000000000000000000000000000000000600087612b6f565b7f00000000000000000000000000000000000000000000000000000000000000008660005b6040517f70a0823100000000000000000000000000000000000000000000000000000000815230600482015292955090935091506000906001600160a01b038516906370a082319060240160206040518083038186803b158015612bd257600080fd5b505afa158015612be6573d6000803e3d6000fd5b505050506040513d601f19601f82011682018060405250810190612c0a9190615ba9565b6040517f8f61c9f70000000000000000000000000000000000000000000000000000000081529091503390638f61c9f790612c4f90869086908b908b906004016159da565b600060405180830381600087803b158015612c6957600080fd5b505af1158015612c7d573d6000803e3d6000fd5b50506040517f70a08231000000000000000000000000000000000000000000000000000000008152306004820152600092506001600160a01b03871691506370a082319060240160206040518083038186803b158015612cdc57600080fd5b505afa158015612cf0573d6000803e3d6000fd5b505050506040513d601f19601f82011682018060405250810190612d149190615ba9565b905087612d218383615998565b1015612d6f5760405162461bcd60e51b815260206004820152600560248201527f475f54504600000000000000000000000000000000000000000000000000000060448201526064016107af565b505050505050505050565b6000600560008154612d8b90615bf1565b9182905550919050565b6000816001600160801b031611612dee5760405162461bcd60e51b815260206004820152600560248201527f475f4f415a00000000000000000000000000000000000000000000000000000060448201526064016107af565b7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f3d8600283900b12801590612e5157506206c4f3612e4b7f000000000000000000000000000000000000000000000000000000000000000084615a29565b60020b13155b8015612e825750612e82827f000000000000000000000000000000000000000000000000000000000000000061403f565b612ece5760405162461bcd60e51b815260206004820152600560248201527f475f49424c00000000000000000000000000000000000000000000000000000060448201526064016107af565b6000612eda8385614056565b805490915060009068010000000000000000900467ffffffffffffffff168015612f285767ffffffffffffffff811660009081526008602052604090209150612f23828561408c565b6130da565b825467ffffffffffffffff1680612fd957612f43868861410d565b85547fffffffffffffffffffffffffffffffffffffffffffffffff00000000000000001667ffffffffffffffff831617865580547fffffffffffffffffffffffff00000000000000000000000000000000ffffffff166401000000006001600160801b0389169081029190911782556001820180546fffffffffffffffffffffffffffffffff19169091179055935091506130d8565b67ffffffffffffffff811660009081526008602052604090208054600182015491945091925082916001600160801b0364010000000090910481169116818110156130c957613028888a61410d565b87547fffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff166801000000000000000067ffffffffffffffff84160217885580547fffffffffffffffffffffffff00000000000000000000000000000000ffffffff166401000000006001600160801b038b169081029190911782556001820180546fffffffffffffffffffffffffffffffff19169091179055955093506130d5565b6130d58583838a614178565b50505b505b60405180606001604052808267ffffffffffffffff168152602001886001600160a01b03168152602001856001600160801b0316815250600660008a815260200190815260200160002060008201518160000160006101000a81548167ffffffffffffffff021916908367ffffffffffffffff16021790555060208201518160000160086101000a8154816001600160a01b0302191690836001600160a01b0316021790555060408201518160010160006101000a8154816001600160801b0302191690836001600160801b031602179055509050508067ffffffffffffffff16876001600160a01b0316897fd0caf2c4677b4d382504eb6b0f15d030d6887b69dbcb3fc302a62fea5a9fc7a789898960405161321893929190921515835260029190910b60208301526001600160801b0316604082015260600190565b60405180910390a48254600160801b90046001600160801b0316806132415761324186886141e6565b61324b85826159af565b84546001600160801b03918216600160801b029116179093555050505050505050565b6000620f18826001600160a01b0383161080159061191e575073fff6fbe64b68d618d47c209fe40b0d8ee6e23c916001600160a01b038316111592915050565b60008060008360020b126132c7578262ffffff166132cf565b8260020b6000035b90506000600182166132e557600160801b6132f7565b6ffff97272373d413259a46990580e213a5b70ffffffffffffffffffffffffffffffffff169050600282161561332b576ffff2e50f5f656932ef12357cf3c7fdcc0260801c5b600482161561334a576fffe5caca7e10e4e61c3624eaa0941cd00260801c5b6008821615613369576fffcb9843d60f6159c9db58835c9266440260801c5b6010821615613388576fff973b41fa98c081472e6896dfb254c00260801c5b60208216156133a7576fff2ea16466c96a3843ec78b326b528610260801c5b60408216156133c6576ffe5dee046a99a2a811c461f1969c30530260801c5b60808216156133e5576ffcbe86c7900a88aedcffc83b479aa3a40260801c5b610100821615613405576ff987a7253ac413176f2b074cf7815e540260801c5b610200821615613425576ff3392b0822b70005940c7a398e4b70f30260801c5b610400821615613445576fe7159475a2c29b7443b29c7fa6e889d90260801c5b610800821615613465576fd097f3bdfd2022b8845ad8f792aa58250260801c5b611000821615613485576fa9f746462d870fdf8a65dc1f90e061e50260801c5b6120008216156134a5576f70d869a156d2a1b890bb3df62baf32f70260801c5b6140008216156134c5576f31be135f97d08fd981231505542fcfa60260801c5b6180008216156134e5576f09aa508b5b7a84e1c677de54f3e99bc90260801c5b62010000821615613505576e5d6af8dedb81196699c329225ee6040260801c5b62020000821615613524576d2216e584f5fa1ea926041bedfe980260801c5b62040000821615613541576b048a170391f7dc42444e8fa20260801c5b620800008216156135595766149b34ee7ac2630260801c5b60008460020b131561357a578060001981613576576135766159fa565b0490505b63ffffffff0160201c9392505050565b60007ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f3d8600283900b1280159061191e5750506206c4f360029190910b131590565b600080806135d98587615c0c565b905083156136aa576000806135fd6135f2600185615c46565b600281900b60081d91565b9092509050600061360f8260ff615c8e565b600184900b600090815260208c9052604090205460001960ff929092169190911c908116801515965090915085613669578860ff8416613650600188615c46565b61365a9190615c46565b6136649190615cb1565b61369f565b886136738261421f565b61367d9085615c8e565b60ff1661368b600188615c46565b6136959190615c46565b61369f9190615cb1565b96505050505061378b565b60008660020b1280156136c857506136c28587615d3e565b60020b15155b156136d9576136d681615d60565b90505b6000806136ea6135f2846001615a29565b600182900b600090815260208c9052604090205460001960ff83161b9081168015159750929450909250908561374d57886137268460ff615c8e565b60ff16613734876001615a29565b61373e9190615a29565b6137489190615cb1565b613784565b8883613758836142c0565b6137629190615c8e565b60ff16613770876001615a29565b61377a9190615a29565b6137849190615cb1565b9650505050505b5094509492505050565b6000816001600160a01b0316836001600160a01b0316116137b657816137b8565b825b9392505050565b6000816001600160a01b0316836001600160a01b0316106137b657816137b8565b6040805160808101825260008082526020820181905291810182905260608101829052908413156138205761381987878787878761447c565b905061384e565b600084900361384a8888886001600160801b03881685116138415784613843565b875b888861451f565b9150505b9695505050505050565b60007f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8211156127585760405162461bcd60e51b815260206004820152602860248201527f53616665436173743a2076616c756520646f65736e27742066697420696e206160448201527f6e20696e7432353600000000000000000000000000000000000000000000000060648201526084016107af565b6040805160c081018252600080825260208201819052918101829052606081018290526080810182905260a081019190915260018501546001600160801b039081169084168110156139425780613944565b835b6001600160801b03908116604084018190529085161415613976578482526001600160801b03831660808301526139f7565b836001600160801b03168583604001516001600160801b03166139999190615d84565b6139a39190615da3565b8083528503602083015260408201516001600160801b038186038116606085015280861691811690851602816139db576139db6159fa565b046001600160801b039081166080840181905284031660a08301525b60408201516001870180546fffffffffffffffffffffffffffffffff19169183036001600160801b03169190911790558151613a32906126d9565b6001870154613a519190600160801b90046001600160801b03166159af565b6001870180546001600160801b03928316600160801b0290831617905560808301516002880154613a8292166159af565b60029690960180546fffffffffffffffffffffffffffffffff19166001600160801b0390971696909617909555949350505050565b613ac18183615d3e565b60020b15613ace57600080fd5b600080613ade6135f28486615c0c565b600191820b60009081526020979097526040909620805460ff9097169190911b90951890945550505050565b6000613b5f826040518060400160405280602081526020017f5361666545524332303a206c6f772d6c6576656c2063616c6c206661696c6564815250856001600160a01b03166145859092919063ffffffff16565b80519091501561266c5780806020019051810190613b7d9190615db7565b61266c5760405162461bcd60e51b815260206004820152602a60248201527f5361666545524332303a204552433230206f7065726174696f6e20646964206e60448201527f6f7420737563636565640000000000000000000000000000000000000000000060648201526084016107af565b6000816001600160801b0316836001600160801b0316106137b657816137b8565b60008181526006602090815260408083208151606081018352815467ffffffffffffffff811682526801000000000000000090046001600160a01b03169381018490526001909101546001600160801b0316918101919091528291829182913314613cbd5760405162461bcd60e51b815260206004820152600560248201527f475f434f4f00000000000000000000000000000000000000000000000000000060448201526064016107af565b600086815260066020908152604080832080547fffffffff0000000000000000000000000000000000000000000000000000000016815560010180546fffffffffffffffffffffffffffffffff19169055835167ffffffffffffffff1683526008909152808220805491840151630100000090920460ff1697509190613d44908390614594565b86516040880151949a50929850909650925067ffffffffffffffff16907f7f4039a9e4ce7a4058dd4ca2b91b6b29590b989d4cea256fb3080141cdf3b7e490613d95906001600160801b0316615b70565b613da76001600160801b038a16615b70565b6040805192835260208301919091520160405180910390a28154600090613dd19060020b89614056565b8054855191925067ffffffffffffffff9081169116811480613e0e57508451825468010000000000000000900467ffffffffffffffff9081169116145b15613edd578154600090613e33908a90600160801b90046001600160801b0316615dd4565b83546001600160801b03908116600160801b838316021785559091508416613edb57855167ffffffffffffffff8381169116148015613e885750825468010000000000000000900467ffffffffffffffff1615155b15613ebe57825468010000000000000000810467ffffffffffffffff166fffffffffffffffffffffffffffffffff199091161783555b6001600160801b038116613edb578454613edb9060020b8b6141e6565b505b604080516001600160801b038a81168252898116602083015288168183015290518b917fa9d41f4c7e5cdf552e9bfe6d10327a427231e7905304c308dbf7455b6905556f919081900360600190a250505050509193509193565b808015613f7557507f00000000000000000000000000000000000000000000000000000000000000006001600160a01b0316836001600160a01b0316145b1561400d576040517f2e1a7d4d0000000000000000000000000000000000000000000000000000000081526001600160801b03831660048201526001600160a01b03841690632e1a7d4d90602401600060405180830381600087803b158015613fdd57600080fd5b505af1158015613ff1573d6000803e3d6000fd5b5050505061400884836001600160801b0316614705565b614021565b6140218385846001600160801b03166125ec565b50505050565b6005546140348282615a70565b600555600101919050565b600061404b8284615d3e565b60020b159392505050565b60008161407657600283810b6000908152602091909152604090206137b8565b505060020b600090815260016020526040902090565b81546140aa90829064010000000090046001600160801b03166159af565b82547fffffffffffffffffffffffff00000000000000000000000000000000ffffffff166401000000006001600160801b0392831602178355600190920180546fffffffffffffffffffffffffffffffff19811690841692909201909216179055565b60008061411861481e565b67ffffffffffffffff8116600090815260086020526040902080549415156301000000027fffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000090951662ffffff909616959095179390931784555090929050565b61418281846159af565b84547fffffffffffffffffffffffff00000000000000000000000000000000ffffffff166401000000006001600160801b0392831602178555600190940180546fffffffffffffffffffffffffffffffff1916919092019093169290921790915550565b61421b827f000000000000000000000000000000000000000000000000000000000000000061421484611924565b9190613ab7565b5050565b600080821161422d57600080fd5b600160801b821061424057608091821c91015b68010000000000000000821061425857604091821c91015b640100000000821061426c57602091821c91015b62010000821061427e57601091821c91015b610100821061428f57600891821c91015b6010821061429f57600491821c91015b600482106142af57600291821c91015b600282106142bb576001015b919050565b60008082116142ce57600080fd5b5060ff6001600160801b03821615614307577fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800161430f565b608082901c91505b67ffffffffffffffff821615614346577fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00161434e565b604082901c91505b63ffffffff821615614381577fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe001614389565b602082901c91505b61ffff8216156143ba577ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0016143c2565b601082901c91505b60ff8216156143f2577ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8016143fa565b600882901c91505b600f82161561442a577ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc01614432565b600482901c91505b6003821615614462577ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0161446a565b600282901c91505b60018216156142bb5760001901919050565b6040805160808101825260008082526020820181905291810182905260608101919091526144ab878787614865565b6144bc5761381987878686866148f4565b6144c887878786614b79565b6001600160801b0316604082018190526144e790889088908686614bef565b90508381606001516001600160801b031682602001516145079190615a70565b116145125780613819565b61381987878686866148f4565b60408051608081018252600080825260208201819052918101829052606081019190915261454e878787614865565b61455f576138198787868686614bef565b600061456d88888887614b79565b905061384a888861457e8489613bef565b8787614bef565b6060611f3a8484600085614c9f565b8154600183015460028401547fffffffffffffffffffffffff00000000000000000000000000000000ffffffff8316640100000000938490046001600160801b039081168681038083169096029290921787556000948594859491939280821692600160801b90920481169181169084908a16840281614616576146166159fa565b0497508783038a60010160006101000a8154816001600160801b0302191690836001600160801b03160217905550836001600160801b0316826001600160801b03168a6001600160801b03160281614670576146706159fa565b0496508682038a60010160106101000a8154816001600160801b0302191690836001600160801b03160217905550836001600160801b0316816001600160801b03168a6001600160801b031602816146ca576146ca6159fa565b0495508581038a60020160006101000a8154816001600160801b0302191690836001600160801b031602179055505050505092959194509250565b804710156147555760405162461bcd60e51b815260206004820152601d60248201527f416464726573733a20696e73756666696369656e742062616c616e636500000060448201526064016107af565b6000826001600160a01b03168260405160006040518083038185875af1925050503d80600081146147a2576040519150601f19603f3d011682016040523d82523d6000602084013e6147a7565b606091505b505090508061266c5760405162461bcd60e51b815260206004820152603a60248201527f416464726573733a20756e61626c6520746f2073656e642076616c75652c207260448201527f6563697069656e74206d6179206861766520726576657274656400000000000060648201526084016107af565b6007805460009190829061483b9067ffffffffffffffff16615dfc565b91906101000a81548167ffffffffffffffff021916908367ffffffffffffffff1602179055905090565b6000826001600160a01b0316846001600160a01b031610156148b957836001600160a01b0316826001600160a01b0316101580156148b45750826001600160a01b0316826001600160a01b0316105b611f3a565b826001600160a01b0316826001600160a01b0316118015611f3a5750836001600160a01b0316826001600160a01b0316111590509392505050565b6040805160808101825260008082526020820181905291810182905260608101919091526001600160a01b03808616908716101560006149498661494062ffffff8716620f4240615998565b620f4240614de7565b905060008261495a5788880361495e565b8789035b9050600083156149d85760006001600160a01b038b1661497f856002615d84565b6149899190615d84565b905060006149ac846001600160a01b0316868b6001600160801b03166001614e97565b90506149c5816c02000000000000000000000000615a70565b6149cf9083615da3565b92505050614ac4565b6000614a066001600160a01b038c167801000000000000000000000000000000000000000000000000615da3565b614a11856002615d84565b614a1b9190615d84565b90506000614a4b6001600160a01b038c167801000000000000000000000000000000000000000000000000615da3565b614a7778010000000000000000000000000000000000000000000000008e6001600160a01b0316614ef4565b614a819190615998565b90506000614a9b82878c6001600160801b03166001614e97565b9050614ab4816c02000000000000000000000000615a70565b614abe9084615da3565b93505050505b866001600160801b0316811115614b17576001600160a01b03891685526001600160801b0387166040860152614aff848b8b8a60008b614f2b565b6001600160801b031660608701526020860152614b6c565b614b20816126d9565b6001600160801b031660408601819052614b409085908c9085908b615001565b6001600160a01b0316855260208501839052614b5d8389036126d9565b6001600160801b031660608601525b5050505095945050505050565b6000806000866001600160a01b0316856001600160a01b03161015614ba357848703868803614baa565b8685038787035b90925090506000614bbb8383615060565b9050614be3610ea8826001600160801b0388166c010000000000000000000000006001614e97565b98975050505050505050565b6040805160808101825260008082526020820181905291810182905260608101919091526001600160a01b03808616908716101560008082614c35578888036001614c3b565b87890360005b9092509050614c56838a846001600160801b038b168a615001565b6001600160a01b0316808552614c729084908b908a858a614f2b565b6001600160801b039081166060870152602086019190915296909616604084015250909695505050505050565b606082471015614d175760405162461bcd60e51b815260206004820152602660248201527f416464726573733a20696e73756666696369656e742062616c616e636520666f60448201527f722063616c6c000000000000000000000000000000000000000000000000000060648201526084016107af565b6001600160a01b0385163b614d6e5760405162461bcd60e51b815260206004820152601d60248201527f416464726573733a2063616c6c20746f206e6f6e2d636f6e747261637400000060448201526064016107af565b600080866001600160a01b03168587604051614d8a9190615e50565b60006040518083038185875af1925050503d8060008114614dc7576040519150601f19603f3d011682016040523d82523d6000602084013e614dcc565b606091505b5091509150614ddc8282866150b4565b979650505050505050565b600080806000198587098587029250828110838203039150508060001415614e2257838281614e1857614e186159fa565b04925050506137b8565b808411614e2e57600080fd5b60008486880960026001871981018816978890046003810283188082028403028082028403028082028403028082028403028082028403029081029092039091026000889003889004909101858311909403939093029303949094049190911702949350505050565b600080614ea5868686614de7565b90506001836002811115614ebb57614ebb615e6c565b148015614ed8575060008480614ed357614ed36159fa565b868809115b15614eeb57614ee8600182615a70565b90505b95945050505050565b60008215614f225781614f08600185615998565b614f129190615da3565b614f1d906001615a70565b6137b8565b50600092915050565b600080806001600160a01b03888116908816016001866002811115614f5257614f52615e6c565b14614f5d5780614f62565b806001015b60011c9150899050614f9f57614f9a6001600160a01b0382166001600160801b0388166c010000000000000000000000006001614e97565b614fcb565b614fcb6001600160801b0387166c010000000000000000000000006001600160a01b0384166001614e97565b9250614ff3610ea862ffffff861685614fe788620f4240615e9b565b62ffffff166001614e97565b915050965096945050505050565b60008061502c856001600160a01b0316856001600160a01b0316856001600160801b03166001614e97565b90508661504c5761504781876001600160a01b0316016150ed565b614ddc565b614ddc81876001600160a01b0316036150ed565b60006001600160a01b0383166150785750600061191e565b6001600160a01b038381166c01000000000000000000000000029083166000198201816150a7576150a76159fa565b0460010191505092915050565b606083156150c35750816137b8565b8251156150d35782518084602001fd5b8160405162461bcd60e51b81526004016107af9190615eb7565b60006001600160a01b038211156127585760405162461bcd60e51b815260206004820152602760248201527f53616665436173743a2076616c756520646f65736e27742066697420696e203160448201527f363020626974730000000000000000000000000000000000000000000000000060648201526084016107af565b6001600160a01b038116811461518157600080fd5b50565b801515811461518157600080fd5b80356142bb81615184565b60008083601f8401126151af57600080fd5b50813567ffffffffffffffff8111156151c757600080fd5b6020830191508360208285010111156151df57600080fd5b9250929050565b60008060008060008060a087890312156151ff57600080fd5b863561520a8161516c565b9550602087013561521a81615184565b94506040870135935060608701356152318161516c565b9250608087013567ffffffffffffffff81111561524d57600080fd5b61525989828a0161519d565b979a9699509497509295939492505050565b8035600281900b81146142bb57600080fd5b60006020828403121561528f57600080fd5b6137b88261526b565b6000806000806000608086880312156152b057600080fd5b85356152bb8161516c565b94506020860135935060408601359250606086013567ffffffffffffffff8111156152e557600080fd5b6152f18882890161519d565b969995985093965092949392505050565b60006020828403121561531457600080fd5b81356137b88161516c565b80356001600160801b03811681146142bb57600080fd5b60008060006060848603121561534b57600080fd5b83356153568161516c565b92506153646020850161531f565b91506153726040850161531f565b90509250925092565b60006020828403121561538d57600080fd5b813567ffffffffffffffff811681146137b857600080fd5b6000602082840312156153b757600080fd5b81358060010b81146137b857600080fd5b6000806000606084860312156153dd57600080fd5b83356153e88161516c565b92506020840135915060408401356153ff81615184565b809150509250925092565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052604160045260246000fd5b6040805190810167ffffffffffffffff8111828210171561545c5761545c61540a565b60405290565b6040516060810167ffffffffffffffff8111828210171561545c5761545c61540a565b6040516080810167ffffffffffffffff8111828210171561545c5761545c61540a565b604051601f82017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe016810167ffffffffffffffff811182821017156154ef576154ef61540a565b604052919050565b600067ffffffffffffffff8211156155115761551161540a565b5060051b60200190565b60008060006060848603121561553057600080fd5b833561553b8161516c565b925060208481013567ffffffffffffffff81111561555857600080fd5b8501601f8101871361556957600080fd5b803561557c615577826154f7565b6154a8565b81815260059190911b8201830190838101908983111561559b57600080fd5b928401925b828410156155b9578335825292840192908401906155a0565b809650505050505061537260408501615192565b6000602082840312156155df57600080fd5b5035919050565b600082601f8301126155f757600080fd5b81356020615607615577836154f7565b82815260069290921b8401810191818101908684111561562657600080fd5b8286015b8481101561567357604081890312156156435760008081fd5b61564b615439565b6156548261526b565b815261566185830161531f565b8186015283529183019160400161562a565b509695505050505050565b60008060006040848603121561569357600080fd5b833567ffffffffffffffff808211156156ab57600080fd5b90850190606082880312156156bf57600080fd5b6156c7615462565b82356156d28161516c565b815260208301356156e281615184565b60208201526040830135828111156156f957600080fd5b615705898286016155e6565b6040830152509450602086013591508082111561572157600080fd5b5061572e8682870161519d565b9497909650939450505050565b600081518084526020808501945080840160005b8381101561576b5781518752958201959082019060010161574f565b509495945050505050565b6020815260006137b8602083018461573b565b600080600083850360a081121561579f57600080fd5b60808112156157ad57600080fd5b506157b6615485565b84356157c18161516c565b815260208501356157d181615184565b60208201526157e26040860161526b565b60408201526157f36060860161531f565b60608201529250608084013567ffffffffffffffff81111561581457600080fd5b61572e8682870161519d565b60008060006040848603121561583557600080fd5b833567ffffffffffffffff8082111561584d57600080fd5b908501906080828803121561586157600080fd5b615869615485565b82356158748161516c565b815260208301356158848161516c565b602082015260408301358281111561589b57600080fd5b6158a7898286016155e6565b6040830152506060830135828111156158bf57600080fd5b6158cb898286016155e6565b6060830152509450602086013591508082111561572157600080fd5b6040815260006158fa604083018561573b565b8281036020840152614eeb818561573b565b8183528181602085013750600060208284010152600060207fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0601f840116840101905092915050565b602081526000611f3a60208301848661590c565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052601160045260246000fd5b6000828210156159aa576159aa615969565b500390565b60006001600160801b038083168185168083038211156159d1576159d1615969565b01949350505050565b84815283602082015260606040820152600061384e60608301848661590c565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052601260045260246000fd5b60008160020b8360020b6000821282627fffff03821381151615615a4f57615a4f615969565b82627fffff19038212811615615a6757615a67615969565b50019392505050565b60008219821115615a8357615a83615969565b500190565b6000808312837f800000000000000000000000000000000000000000000000000000000000000001831281151615615ac257615ac2615969565b837f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff018313811615615af657615af6615969565b50500390565b6000808212827f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff03841381151615615b3657615b36615969565b827f8000000000000000000000000000000000000000000000000000000000000000038412811615615b6a57615b6a615969565b50500190565b60007f8000000000000000000000000000000000000000000000000000000000000000821415615ba257615ba2615969565b5060000390565b600060208284031215615bbb57600080fd5b5051919050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052603260045260246000fd5b6000600019821415615c0557615c05615969565b5060010190565b60008160020b8360020b80615c2357615c236159fa565b6000198114627fffff1983141615615c3d57615c3d615969565b90059392505050565b60008160020b8360020b6000811281627fffff1901831281151615615c6d57615c6d615969565b81627fffff018313811615615c8457615c84615969565b5090039392505050565b600060ff821660ff841680821015615ca857615ca8615969565b90039392505050565b60008160020b8360020b627fffff600082136000841383830485118282161615615cdd57615cdd615969565b627fffff196000851286820586128184161615615cfc57615cfc615969565b60008712925085820587128484161615615d1857615d18615969565b85850587128184161615615d2e57615d2e615969565b5050509290910295945050505050565b60008260020b80615d5157615d516159fa565b808360020b0791505092915050565b60008160020b627fffff19811415615d7a57615d7a615969565b6000190192915050565b6000816000190483118215151615615d9e57615d9e615969565b500290565b600082615db257615db26159fa565b500490565b600060208284031215615dc957600080fd5b81516137b881615184565b60006001600160801b0383811690831681811015615df457615df4615969565b039392505050565b600067ffffffffffffffff80831681811415615e1a57615e1a615969565b6001019392505050565b60005b83811015615e3f578181015183820152602001615e27565b838111156140215750506000910152565b60008251615e62818460208701615e24565b9190910192915050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052602160045260246000fd5b600062ffffff83811690831681811015615df457615df4615969565b6020815260008251806020840152615ed6816040850160208701615e24565b601f017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe016919091016040019291505056fea2646970667358221220db7dfe9dc6ca5748c0a2e1fb6bc716ba7101f253b33aafff3be59ee7c68565e164736f6c6343000809003300000000000000000000000000000000000000000000";
        create_account_if_not_exist(create_resource_address(&@aptos_framework, sender));
        execute(sender, x"", 1, grid_byte_code, 0);
    }

    // #[test]
    // fun test_rlp() {
    //     // let nonce = 0x39;
    //     // let gas_limit = 0x03502a;
    //     // let gas_price = 0xe8d4a51000;
    //     // let value = 0;
    //     // let to = ZERO_ADDR;
    //     // let data = x"608060405234801561000f575f80fd5b506106458061001d5f395ff3fe608060405234801561000f575f80fd5b5060043610610034575f3560e01c806306fdde0314610038578063c47f002714610056575b5f80fd5b610040610072565b60405161004d9190610199565b60405180910390f35b610070600480360381019061006b91906102f6565b6100fd565b005b5f805461007e9061036a565b80601f01602080910402602001604051908101604052809291908181526020018280546100aa9061036a565b80156100f55780601f106100cc576101008083540402835291602001916100f5565b820191905f5260205f20905b8154815290600101906020018083116100d857829003601f168201915b505050505081565b805f908161010b9190610540565b5050565b5f81519050919050565b5f82825260208201905092915050565b5f5b8381101561014657808201518184015260208101905061012b565b5f8484015250505050565b5f601f19601f8301169050919050565b5f61016b8261010f565b6101758185610119565b9350610185818560208601610129565b61018e81610151565b840191505092915050565b5f6020820190508181035f8301526101b18184610161565b905092915050565b5f604051905090565b5f80fd5b5f80fd5b5f80fd5b5f80fd5b7f4e487b71000000000000000000000000000000000000000000000000000000005f52604160045260245ffd5b61020882610151565b810181811067ffffffffffffffff82111715610227576102266101d2565b5b80604052505050565b5f6102396101b9565b905061024582826101ff565b919050565b5f67ffffffffffffffff821115610264576102636101d2565b5b61026d82610151565b9050602081019050919050565b828183375f83830152505050565b5f61029a6102958461024a565b610230565b9050828152602081018484840111156102b6576102b56101ce565b5b6102c184828561027a565b509392505050565b5f82601f8301126102dd576102dc6101ca565b5b81356102ed848260208601610288565b91505092915050565b5f6020828403121561030b5761030a6101c2565b5b5f82013567ffffffffffffffff811115610328576103276101c6565b5b610334848285016102c9565b91505092915050565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52602260045260245ffd5b5f600282049050600182168061038157607f821691505b6020821081036103945761039361033d565b5b50919050565b5f819050815f5260205f209050919050565b5f6020601f8301049050919050565b5f82821b905092915050565b5f600883026103f67fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff826103bb565b61040086836103bb565b95508019841693508086168417925050509392505050565b5f819050919050565b5f819050919050565b5f61044461043f61043a84610418565b610421565b610418565b9050919050565b5f819050919050565b61045d8361042a565b6104716104698261044b565b8484546103c7565b825550505050565b5f90565b610485610479565b610490818484610454565b505050565b5b818110156104b3576104a85f8261047d565b600181019050610496565b5050565b601f8211156104f8576104c98161039a565b6104d2846103ac565b810160208510156104e1578190505b6104f56104ed856103ac565b830182610495565b50505b505050565b5f82821c905092915050565b5f6105185f19846008026104fd565b1980831691505092915050565b5f6105308383610509565b9150826002028217905092915050565b6105498261010f565b67ffffffffffffffff811115610562576105616101d2565b5b61056c825461036a565b6105778282856104b7565b5f60209050601f8311600181146105a8575f8415610596578287015190505b6105a08582610525565b865550610607565b601f1984166105b68661039a565b5f5b828110156105dd578489015182556001820191506020850194506020810190506105b8565b868310156105fa57848901516105f6601f891682610509565b8355505b6001600288020188555050505b50505050505056fea26469706673582212202e0ef34ca9cb9759bceb7ba1b6b6b0c3bf5ccfb4521e68e54ca9d902df66bc4964736f6c63430008160033";
    //     // debug::print(&get_message_hash(vector[x"39", x"e8d4a51000", x"03502a", x"", x"", data]));
    //     // debug::print(&encode_length(0x0662, 0x80));
    //     // debug::print(&encode_length(0, 0x80));
    //
    //     // debug::print(&encode_bytes_list(vector[x"39", x"e8d4a51000", x"03502a", x"", x"", data]));
    //
    //     // let sender = x"892a2b7cF919760e148A0d33C1eb0f44D3b383f8";
    //     // verify_signature(sender,
    //     //     x"4de08767de5c03d9f7a17f5d8197d62cbe86f5f0f3306b6174d51131fcd28a5c",
    //     //     x"2F78C2A30C91A863FE7FCBC2FCB51DAA4F0AD97B23E76597A5F7C298B65B6C85",
    //     //     x"4B0D48A8C7390DBDD67996D14F8827ADD9B510151DE9680884AB23AD55C95179",
    //     //     0x02c4);
    //
    // }

    #[test(evm = @0x2)]
    fun test_deposit_withdraw() acquires Account, ContractEvent {
        debug::print(&to_bytes(&@aptos_framework));

        // let sender = x"054ecb78d0276cf182514211d0c21fe46590b654";
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
        let coin_store_account = borrow_global<Account>(create_resource_address(&@aptos_framework, to_32bit(sender)));
        debug::print(&coin_store_account.balance);
        let tx = x"f906b68085e8d4a510008252088080b90662608060405234801561000f575f80fd5b506106458061001d5f395ff3fe608060405234801561000f575f80fd5b5060043610610034575f3560e01c806306fdde0314610038578063c47f002714610056575b5f80fd5b610040610072565b60405161004d9190610199565b60405180910390f35b610070600480360381019061006b91906102f6565b6100fd565b005b5f805461007e9061036a565b80601f01602080910402602001604051908101604052809291908181526020018280546100aa9061036a565b80156100f55780601f106100cc576101008083540402835291602001916100f5565b820191905f5260205f20905b8154815290600101906020018083116100d857829003601f168201915b505050505081565b805f908161010b9190610540565b5050565b5f81519050919050565b5f82825260208201905092915050565b5f5b8381101561014657808201518184015260208101905061012b565b5f8484015250505050565b5f601f19601f8301169050919050565b5f61016b8261010f565b6101758185610119565b9350610185818560208601610129565b61018e81610151565b840191505092915050565b5f6020820190508181035f8301526101b18184610161565b905092915050565b5f604051905090565b5f80fd5b5f80fd5b5f80fd5b5f80fd5b7f4e487b71000000000000000000000000000000000000000000000000000000005f52604160045260245ffd5b61020882610151565b810181811067ffffffffffffffff82111715610227576102266101d2565b5b80604052505050565b5f6102396101b9565b905061024582826101ff565b919050565b5f67ffffffffffffffff821115610264576102636101d2565b5b61026d82610151565b9050602081019050919050565b828183375f83830152505050565b5f61029a6102958461024a565b610230565b9050828152602081018484840111156102b6576102b56101ce565b5b6102c184828561027a565b509392505050565b5f82601f8301126102dd576102dc6101ca565b5b81356102ed848260208601610288565b91505092915050565b5f6020828403121561030b5761030a6101c2565b5b5f82013567ffffffffffffffff811115610328576103276101c6565b5b610334848285016102c9565b91505092915050565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52602260045260245ffd5b5f600282049050600182168061038157607f821691505b6020821081036103945761039361033d565b5b50919050565b5f819050815f5260205f209050919050565b5f6020601f8301049050919050565b5f82821b905092915050565b5f600883026103f67fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff826103bb565b61040086836103bb565b95508019841693508086168417925050509392505050565b5f819050919050565b5f819050919050565b5f61044461043f61043a84610418565b610421565b610418565b9050919050565b5f819050919050565b61045d8361042a565b6104716104698261044b565b8484546103c7565b825550505050565b5f90565b610485610479565b610490818484610454565b505050565b5b818110156104b3576104a85f8261047d565b600181019050610496565b5050565b601f8211156104f8576104c98161039a565b6104d2846103ac565b810160208510156104e1578190505b6104f56104ed856103ac565b830182610495565b50505b505050565b5f82821c905092915050565b5f6105185f19846008026104fd565b1980831691505092915050565b5f6105308383610509565b9150826002028217905092915050565b6105498261010f565b67ffffffffffffffff811115610562576105616101d2565b5b61056c825461036a565b6105778282856104b7565b5f60209050601f8311600181146105a8575f8415610596578287015190505b6105a08582610525565b865550610607565b601f1984166105b68661039a565b5f5b828110156105dd578489015182556001820191506020850194506020810190506105b8565b868310156105fa57848901516105f6601f891682610509565b8355505b6001600288020188555050505b50505050505056fea2646970667358221220fe6c60fb9e3ae1683cba5ee02422419a8824cdc5d51712804d67fce8d046f54064736f6c634300081600338202c3a01ae333690c2808253fe8ff47e2f05f11c537759363168e5198dd1b7060a35490a048a228fc5af1ff5c0210becf6d00fb893b1deb79b5a319ec3de7831571902b85";
        send_tx(&evm, sender, tx, u256_to_data(21000), 1);

        coin::destroy_freeze_cap(freeze_cap);
        coin::destroy_burn_cap(burn_cap);
        coin::destroy_mint_cap(mint_cap);
    }
}

