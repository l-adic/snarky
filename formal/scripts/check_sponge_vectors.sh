#!/usr/bin/env bash
# Check the Poseidon sponge (Kimchi/Sponge/Poseidon.lean) against mina_poseidon
# absorb/squeeze traces (fixtures/poseidon_fq_vectors.json, produced by poseidon_dump).
# Driver: scripts/check_sponge_vectors.lean. Requires a prior `lake build Kimchi`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_sponge_vectors.lean
