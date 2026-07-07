#!/usr/bin/env bash
# Replay the permutation argument's row semantics on production kimchi data
# (fixtures/perm_vesta.json). Driver: scripts/check_perm_fixture.lean.
# Requires a prior `lake build Kimchi`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_perm_fixture.lean
