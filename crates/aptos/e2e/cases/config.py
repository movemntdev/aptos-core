# Copyright © Aptos Foundation
# SPDX-License-Identifier: Apache-2.0

import json

from common import TestError
from test_helpers import RunHelper
from test_results import test_case


@test_case
def test_config_show_profiles(run_helper: RunHelper, test_name=None):
    # Show the profile
    response = run_helper.run_command(
        test_name,
        [
            "movement",
            "config",
            "show-profiles",
        ],
    )

    expected_profile = run_helper.get_account_info()
    profile = json.loads(response.stdout)["Result"]["default"]
    if (
        profile["has_private_key"] != True
        or profile["public_key"] != expected_profile.public_key
        or profile["account"] != expected_profile.account_address
    ):
        raise TestError(
            f"[aptos config show-profiles] shows incorrect profile {profile} -- \n expected {expected_profile}"
        )
