#!/usr/bin/env bash
# Gate the pickles linearization results' axiom closure: standard axioms only, plus the
# two declared native_decide certificates in Pickles/Reflect/Certificate.lean.
# Requires a prior `lake build Pickles` (and hence `make gen-linearization`).
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_axioms.lean
