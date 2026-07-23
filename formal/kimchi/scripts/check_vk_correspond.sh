#!/usr/bin/env bash
# The verifier-key <-> index correspondence, by value, at BOTH production chunking
# regimes on Vesta (Pallas has no index fixture): every committed column of the nc=1
# VK (fixtures/kimchi_proof_vesta.json, zk_rows=3) and of the nc=2 VK
# (fixtures/kimchi_proof_vesta_nc2.json, zk_rows=5) must, chunk by chunk, be the
# value-MSM of that key's Lagrange-basis chunk commitments against its derived column.
# The sigma columns are the MODEL's own derivation (Index.build? on
# fixtures/index_vesta.json at each regime's zk_rows, then Index.sigmaAddrRow — so the
# model's sigma-zeroing branch is adjudicated against production at zk_rows=5, and the
# un-zeroed addresses at zk_rows=3); selectors carry the per-chunk fixed blinder.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_vk_correspond.lean
