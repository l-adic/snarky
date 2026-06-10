#!/usr/bin/env bash
#
# The single pickles-bench launcher. Builds the bench workspace and runs
# the suite's own CLI (`Bench.Pickles.Main` — see `--help`, `--only
# compile|prove`) under the measurement pipeline:
#
#   * always: `--trace-gc` (raw log -> prof/bench-run.log, terminal kept
#     clean), machine-readable results -> bench-results/<sha>-<date>.json,
#     per-trial GC stats attached via parse_gclog.mjs.
#   * `--cpu-prof` (consumed here, not forwarded): additionally capture a
#     V8 CPU profile into prof/ — JS-side ranking only (the profiler is
#     blind inside Rust napi calls; the exact JS/Rust split is in the
#     results JSON from the FFI wrappers). Map frames back to PureScript
#     with packages/pickles-bench/resolve_profile.mjs.
#
# Everything else on the command line is forwarded to the bench CLI:
#   tools/bench.sh                      # full suite (compile + prove)
#   tools/bench.sh --only prove        # one group
#   tools/bench.sh --cpu-prof --only prove
#
# Compare two runs (flags wall-time regressions, exits 1):
#   node packages/pickles-bench/compare.mjs <baseline.json> <candidate.json>
#
# This workspace is separate from the root (own spago.yaml `workspace:`
# section, purs-backend-es backend). `spago run` does not work with the
# purs-backend-es backend, hence the node launcher. The run happens from
# the REPO ROOT so `srs-cache/` and kimchi-napi resolve.
#
# NOTE: results are machine-specific — only compare runs from the same
# box, and never run two benches concurrently.
#
# Full suite ≈ 15+ minutes (3 timed compiles + prove warmup + 3 timed
# proves).

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BENCH_DIR="$REPO_ROOT/packages/pickles-bench"
# Pinned node — the artifact records the version, and baselines are only
# comparable on the same V8.
export PATH="$HOME/.nvm/versions/node/v23.11.1/bin:$PATH"

# Our one flag; the rest is forwarded to the bench CLI.
NODE_FLAGS=(--trace-gc)
ARGS=()
for a in "$@"; do
  case "$a" in
    --cpu-prof) NODE_FLAGS+=(--cpu-prof --cpu-prof-dir "$REPO_ROOT/prof") ;;
    *) ARGS+=("$a") ;;
  esac
done

echo "==> Building pickles-bench workspace (purs-backend-es -> output-es/) ..."
( cd "$BENCH_DIR" && npx spago build )

cd "$REPO_ROOT"
mkdir -p bench-results prof
RUN_LOG="prof/bench-run.log"

echo "==> Running suite (node ${NODE_FLAGS[*]}; log: $RUN_LOG) ..."
# The raw --trace-gc firehose (one line per GC, thousands per trial) goes
# to the LOG ONLY — it is input for parse_gclog.mjs, not for humans. The
# terminal shows just the bench's own output (markers, splits, results).
node "${NODE_FLAGS[@]}" packages/pickles-bench/run.mjs "${ARGS[@]}" 2>&1 \
  | tee "$RUN_LOG" \
  | grep -vE '^\[[0-9]+(:0x[0-9a-f]+)?\] ' || true

# The bench prints `[bench-results] <path>` for the JSON it wrote.
RESULTS_FILE=$(grep -oP '(?<=^\[bench-results\] ).*' "$RUN_LOG" | tail -1)
if [ -z "$RESULTS_FILE" ]; then
  echo "ERROR: no [bench-results] line found in the run output" >&2
  exit 1
fi

echo "==> Attaching GC stats from the trace-gc log ..."
node packages/pickles-bench/parse_gclog.mjs "$RUN_LOG" "$RESULTS_FILE"

echo "==> Results: $RESULTS_FILE"
