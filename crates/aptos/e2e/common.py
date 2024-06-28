# Copyright © Aptos Foundation
# SPDX-License-Identifier: Apache-2.0

import os
from dataclasses import dataclass
from enum import Enum

NODE_PORT = 8080
METRICS_PORT = 9101
FAUCET_PORT = 8081


class Network(Enum):
    DEVNET = "devnet"
    TESTNET = "testnet"
    MAINNET = "mainnet"

    def __str__(self):
        return self.value


# Information for some accounts we use for testing.
@dataclass
class AccountInfo:
    private_key: str
    public_key: str
    account_address: str


# This is an account that use for testing, for example to create it with the init
# account, send funds to it, etc. This is not the account created by the `aptos init`
# test. To get details about that account use get_account_info on the RunHelper.
OTHER_ACCOUNT_ONE = AccountInfo(
    private_key="0xe2f8b838fad789a19065c7a8d970073023e7d00f447911ce2422f0849b75e390",
    public_key="0x72564039aee0e1d463a6a09d88663433f879b57978a5bc8582a16584e4e4b2fd",
    account_address="0x996679d644a2f991a96e871870b2c1b2a51eec67ceb230a305857e4fe6aa9b4b",
)


def build_image_name(image_repo_with_project: str, tag: str):
    # If no repo is specified, leave it that way. Otherwise make sure we have a slash
    # between the image repo and the image name.
    image_repo_with_project = image_repo_with_project.rstrip("/")
    if image_repo_with_project != "":
        image_repo_with_project = f"{image_repo_with_project}/"
    return f"{image_repo_with_project}tools:{tag}"


# Exception to use when a test fails, for the CLI did something unexpected, an
# expected output was missing, etc. This is just a convenience, the framework
# will still work if a different error is raised.
#
# For errors within the framework itself, use RuntimeError.
class TestError(Exception):
    pass
