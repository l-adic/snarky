#!/usr/bin/env bash
# Gate the bulletproof PCS soundness surface: standard axioms + the declared FS axioms +
# the Pasta trust base only. Requires a prior `lake build Bulletproof`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_axioms.lean
