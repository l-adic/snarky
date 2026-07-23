#!/usr/bin/env bash
# Check the executable kimchi verifier against complete production wire proofs —
# the three-fixture matrix: fixtures/kimchi_proof_vesta.json (nc=1) and
# fixtures/kimchi_proof_{vesta,pallas}_nc2.json (nc=2, both curves), produced by
# tools/fixture-dump's kimchi_proof_dump / kimchi_proof_dump_nc2. Each run checks the
# accept bit, a verify-level corruption matrix, and the Wire.check parse rejections.
# Driver: scripts/check_kimchi_verifier.lean. Requires a prior `lake build Kimchi`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_kimchi_verifier.lean
