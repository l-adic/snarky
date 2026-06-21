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
# comparable on the same V8. If it isn't installed, warn LOUDLY rather than
# silently falling through to a different node (which would skew the comparison).
PINNED_NODE="$HOME/.nvm/versions/node/v23.11.1/bin"
if [ -x "$PINNED_NODE/node" ]; then
  export PATH="$PINNED_NODE:$PATH"
else
  echo "WARN: pinned node v23.11.1 not at $PINNED_NODE — using $(command -v node) ($(node --version 2>/dev/null)). PS and o1js MUST use the SAME node for a fair comparison; install v23.11.1 (nvm install 23.11.1) or edit this PATH." >&2
fi
echo "==> node: $(node --version) ($(command -v node))"

# With `--cpu-prof`, the newest profile in prof/ is auto-summarized by
# packages/pickles-bench/analyze_cpuprofile.mjs (self-time by category /
# module / frame — sizes dispatch+currying overhead vs bigint core vs Run
# machinery). Re-run it manually on any saved .cpuprofile.
#
# Our one flag; the rest is forwarded to the bench CLI.
#
# Deliberately NO GC tuning (e.g. --max-semi-space-size): measured
# 2026-06-11 as noise-level for this workload once the compile bench
# stopped running with prove's prepared state resident, and changing node
# flags breaks comparability with older baselines. The flags are recorded
# in the results JSON (`nodeFlags`) — only compare runs with identical
# flags.
NODE_FLAGS=(--trace-gc --expose-gc)
ARGS=()
for a in "$@"; do
  case "$a" in
    --cpu-prof) CPU_PROF=1; NODE_FLAGS+=(--cpu-prof --cpu-prof-dir "$REPO_ROOT/prof") ;;
    # --wasm: run against the wasm32-wasip1-threads build of kimchi-napi
    # (see packages/kimchi-napi/index.js). The artifact gets a `backend`
    # field + filename infix so wasm runs never pollute the native
    # baseline history compare.mjs reads.
    --wasm) KIMCHI_BACKEND=wasm; export KIMCHI_BACKEND ;;
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
node "${NODE_FLAGS[@]}" packages/pickles-bench/run.mjs ${ARGS[@]+"${ARGS[@]}"} 2>&1 \
  | stdbuf -oL tee "$RUN_LOG" \
  | grep --line-buffered -vE '^\[[0-9]+(:0x[0-9a-f]+)?\] ' || true

# The bench prints `[bench-results] <path>` for the JSON it wrote.
RESULTS_FILE=$(sed -n 's/^\[bench-results\] //p' "$RUN_LOG" | tail -1)
if [ -z "$RESULTS_FILE" ]; then
  echo "ERROR: no [bench-results] line found in the run output" >&2
  exit 1
fi

echo "==> Attaching GC stats from the trace-gc log ..."
node packages/pickles-bench/parse_gclog.mjs "$RUN_LOG" "$RESULTS_FILE"

if [ "${KIMCHI_BACKEND:-}" = "wasm" ]; then
  RESULTS_FILE=$(node -e '
    const fs = require("fs");
    const f = process.argv[1];
    const a = JSON.parse(fs.readFileSync(f, "utf8"));
    a.backend = "wasm";
    const out = f.replace(/^(bench-results\/)/, "$1wasm-");
    fs.writeFileSync(out, JSON.stringify(a, null, 2));
    fs.unlinkSync(f);
    console.log(out);
  ' "$RESULTS_FILE")
  echo "==> wasm backend: artifact tagged + renamed -> $RESULTS_FILE"
fi

if [ "${CPU_PROF:-}" = "1" ]; then
  CPU_PROFILE=$(ls -t prof/*.cpuprofile 2>/dev/null | head -1 || true)
  if [ -n "$CPU_PROFILE" ]; then
    echo "==> CPU profile summary ($CPU_PROFILE) ..."
    node packages/pickles-bench/analyze_cpuprofile.mjs "$CPU_PROFILE"
  fi
fi

echo "==> Results: $RESULTS_FILE"
