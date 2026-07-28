#!/usr/bin/env bash
# Axiom-closure gate for the poseidon sponge surface (see check_axioms.lean).
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_axioms.lean
