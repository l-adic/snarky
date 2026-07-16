#!/usr/bin/env bash
# Gate the Snarky interpreter laws' axiom closure: pure core Lean, standard axioms only.
# Requires a prior `lake build Snarky`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_axioms.lean
