#!/usr/bin/env bash
# Gate the schnorr exemplar's axiom closure: standard axioms only.
# Requires a prior `lake build Schnorr`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_axioms.lean
