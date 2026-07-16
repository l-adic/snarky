#!/usr/bin/env bash
# Check the Fq-sponge and map-to-curve (Kimchi/Sponge) against DefaultFqSponge op traces
# and group_map vectors (fixtures/{fq_sponge,group_map}_vectors.json, from sponge_dump).
# Driver: scripts/check_fq_sponge.lean. Requires a prior `lake build Poseidon`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_fq_sponge.lean
