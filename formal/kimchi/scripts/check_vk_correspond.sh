#!/usr/bin/env bash
# Check the verifier-key <-> index correspondence by value: every committed column of
# the production VK (fixtures/kimchi_proof_vesta.json) must be the value-MSM of the
# Lagrange-basis commitments against its derived column (fixtures/index_vesta.json).
# Driver: scripts/check_vk_correspond.lean. Requires a prior `lake build Kimchi`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_vk_correspond.lean
