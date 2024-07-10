// Copyright © Aptos Foundation
// SPDX-License-Identifier: Apache-2.0

use crate::{assert_success, build_package, tests::common, MoveHarness};
use aptos_crypto::{
    ed25519::{Ed25519PrivateKey, Ed25519Signature},
    SigningKey, ValidCryptoMaterialStringExt,
};
use aptos_types::{
    account_address::{create_resource_address, AccountAddress},
    event::EventHandle,
    state_store::{state_key::StateKey, table::TableHandle},
};
use move_core_types::parser::parse_struct_tag;
use serde::{Deserialize, Serialize};

#[derive(Deserialize, Serialize)]
struct TokenDataId {
    creator: AccountAddress,
    collection: Vec<u8>,
    name: Vec<u8>,
}

#[derive(Deserialize, Serialize)]
struct TokenId {
    token_data_id: TokenDataId,
    property_version: u64,
}

#[derive(Deserialize, Serialize)]
struct MintProofChallenge {
    account_address: AccountAddress,
    module_name: String,
    struct_name: String,
    receiver_account_sequence_number: u64,
    receiver_account_address: AccountAddress,
    token_data_id: TokenDataId,
}

#[derive(Deserialize, Serialize)]
struct TokenStore {
    tokens: TableHandle,
    direct_transfer: bool,
    deposit_events: EventHandle,
    withdraw_events: EventHandle,
    burn_events: EventHandle,
    mutate_token_property_events: EventHandle,
}

#[test]
fn publish_under_resource_account() {
    let mut h = MoveHarness::new();

    let acc = h.new_account_at(AccountAddress::from_hex_literal("0xcafe").unwrap());
    let resource_address = create_resource_address(*acc.address(), &[]);

    // give a named address to the `mint_nft` module publisher
    let mut build_options = aptos_framework::BuildOptions::default();
    build_options.named_addresses.insert("atomic_bridge".to_string(), *acc.address());
    build_options.named_addresses.insert("denylister".to_string(), *acc.address());
    build_options.named_addresses.insert("master_minter".to_string(), *acc.address());
    build_options.named_addresses.insert("minter".to_string(), *acc.address());
    build_options.named_addresses.insert("moveth".to_string(), *acc.address());
    build_options.named_addresses.insert("pauser".to_string(), *acc.address());

    // build the package from our example code
    let package = build_package(
        common::test_dir_path("/Users/andygmove/Downloads/repos/movement/protocol-units/bridge/move-modules"),
        build_options,
    )
    .expect("building package must succeed");

    let code = package.extract_code();
    let metadata = package
        .extract_metadata()
        .expect("extracting package metadata must succeed");

    // create the resource account and publish the module under the resource account's address
    let result = h.run_transaction_payload(
        &acc,
        aptos_cached_packages::aptos_stdlib::resource_account_create_resource_account_and_publish_package(
            vec![],
            bcs::to_bytes(&metadata).expect("PackageMetadata has BCS"),
            code,
        ),
    );  
    // Log the result for debugging purposes
    println!("Transaction result: {:?}", result);
    assert_success!(result);

}