#!/usr/bin/env bash
# Replay the index model on a mixed-gate production circuit
# (fixtures/index_vesta.json). Driver: scripts/check_index_fixture.lean.
# Requires a prior `lake build Kimchi`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_index_fixture.lean
