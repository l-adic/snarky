#!/usr/bin/env bash
# Adjudicate the chunk layer's recombination formulas against production kimchi output
# (fixtures/ipa_chunked_{vesta,pallas}.json). Driver: scripts/check_chunked_fixture.lean.
# Requires a prior `lake build Kimchi`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_chunked_fixture.lean
