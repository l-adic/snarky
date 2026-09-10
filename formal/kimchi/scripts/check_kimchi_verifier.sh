#!/usr/bin/env bash
# Check the executable kimchi verifier against complete production wire proofs —
# fixtures/kimchi_proof_vesta.json (nc=1), fixtures/kimchi_proof_{vesta,pallas}_nc2.json
# (nc=2, both curves), the live-EndoMul/VarBaseMul proof, and a deployed pickles wrap
# proof with its old accumulators (fixtures/kimchi_proof_pallas_pickles.json), produced by
# tools/fixture-dump's kimchi_proof_dump* binaries. Each run checks the accept bit, a
# verify-level corruption matrix, and the Wire.check parse rejections.
# Driver: scripts/check_kimchi_verifier.lean, run interpreted as CI runs it (`--run`; without
# it the file only elaborates). Requires a prior `lake build Kimchi`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean --run scripts/check_kimchi_verifier.lean
