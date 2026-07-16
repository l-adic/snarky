#!/usr/bin/env bash
# Check the IPA verifier model against a kimchi/proof-systems-generated transcript fixture
# (fixtures/ipa_opening_vesta.json, produced by tools/ipa-fixture-dump). Driver:
# scripts/check_ipa_fixture.lean. Requires a prior `lake build Bulletproof`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_ipa_fixture.lean
