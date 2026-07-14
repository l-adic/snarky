#!/usr/bin/env bash
# Compile the DSL multiply circuit to a wired kimchi index and check Satisfies
# (copy constraints included). Driver: scripts/check_snarky_index.lean.
# Requires a prior `lake build Snarky`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_snarky_index.lean
