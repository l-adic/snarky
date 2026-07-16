#!/usr/bin/env bash
# Check every witness-carrying PureScript harness result
# (packages/pickles-circuit-diffs/circuits/results/*.json) against the index model.
# Driver: scripts/check_ps_witness.lean. Requires a prior `lake build Kimchi` and a
# harness run with CIRCUIT_DIFFS_WITNESS_EXPORT=1. Standalone (this package's own
# workspace); from the aggregator use:
#   cd formal && lake env lean kimchi/scripts/check_ps_witness.lean
set -euo pipefail
cd "$(dirname "$0")/.."
KIMCHI_PS_RESULTS_DIR="../../packages/pickles-circuit-diffs/circuits/results" \
  lake env lean scripts/check_ps_witness.lean
