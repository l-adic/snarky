#!/usr/bin/env bash
# Check every witness-carrying PureScript harness result
# (packages/pickles-circuit-diffs/circuits/results/*.json) against the index model.
# Driver: scripts/check_ps_witness.lean. Requires a prior `lake build Kimchi` and a
# harness run with CIRCUIT_DIFFS_WITNESS_EXPORT=1.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_ps_witness.lean
