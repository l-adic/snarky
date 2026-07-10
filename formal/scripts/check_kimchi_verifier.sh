#!/usr/bin/env bash
# Check the executable kimchi verifier against a complete production wire proof
# (fixtures/kimchi_proof_vesta.json, produced by tools/fixture-dump's kimchi_proof_dump).
# Driver: scripts/check_kimchi_verifier.lean. Requires a prior `lake build Kimchi`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_kimchi_verifier.lean
