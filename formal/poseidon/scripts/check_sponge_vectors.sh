#!/usr/bin/env bash
# Check the Poseidon sponge (Poseidon/Basic.lean) against mina_poseidon
# absorb/squeeze traces (fixtures/poseidon_fq_vectors.json, produced by poseidon_dump).
# Driver: scripts/check_sponge_vectors.lean. Requires a prior `lake build Poseidon`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_sponge_vectors.lean
