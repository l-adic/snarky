#!/usr/bin/env bash
# Check the closed-form verifier linearization against the production scalar side
# (fixtures/linearization_vesta.json, produced by tools/fixture-dump's linearization_dump).
# Driver: scripts/check_linearization.lean. Requires a prior `lake build Kimchi`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_linearization.lean
