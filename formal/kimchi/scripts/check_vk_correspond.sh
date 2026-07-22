#!/usr/bin/env bash
# The CHUNKED verifier-key <-> index correspondence, by value: every committed column of
# the production nc=2 VK (fixtures/kimchi_proof_vesta_nc2.json) must, chunk by chunk, be
# the value-MSM of the Lagrange-basis chunk commitments against its derived column
# (fixtures/index_vesta.json) -- selectors carrying the per-chunk fixed blinder.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_vk_correspond.lean
