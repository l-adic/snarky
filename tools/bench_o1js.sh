#!/usr/bin/env bash
#
# o1js counterpart of tools/bench.sh: builds and runs the o1js-bench
# suite under the SAME measurement pipeline — node --trace-gc with the
# raw log captured, results JSON in bench-results/, GC reclaim attached
# per [bench-window] by the PS suite's parse_gclog.mjs (the o1js
# harness emits identical window markers).
#
# Cross-suite comparisons are tables, not regression gates: the suites
# share metrics (wall, reclaim/trial, rows) but not internals (no
# js/rust split on the o1js side — its kimchi is WASM inside the JS
# heap).
#
#   tools/bench_o1js.sh            # full suite, WASM backend (the default)
#   tools/bench_o1js.sh --native   # @o1js/native backend (napi-rs, native
#                                  # OS threads — the tightest pairing
#                                  # against our kimchi-napi stack)
#   tools/bench_o1js.sh --cpu-prof # additionally capture a V8 CPU profile
#                                  # into prof/ (whole-process, exactly
#                                  # like tools/bench.sh — there are no
#                                  # in-process profiler start/stops in
#                                  # either suite)
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Pinned node — same pin as tools/bench.sh; cross-suite tables are only
# valid when both suites ran on the same node binary.
export PATH="$HOME/.nvm/versions/node/v23.11.1/bin:$PATH"
BENCH_DIR="$REPO_ROOT/o1js-bench"
LOG="$REPO_ROOT/prof/o1js-bench-run.log"

NODE_FLAGS=(--trace-gc)
export O1JS_BACKEND="${O1JS_BACKEND:-wasm}"
for arg in "$@"; do
  case "$arg" in
    --cpu-prof) NODE_FLAGS+=(--cpu-prof --cpu-prof-dir "$REPO_ROOT/prof") ;;
    --native) export O1JS_BACKEND=native ;;
  esac
done
echo "==> o1js backend: $O1JS_BACKEND"

cd "$BENCH_DIR"

if [ ! -d node_modules ]; then
  echo "==> Installing o1js-bench dependencies ..."
  npm install
fi

echo "==> Building o1js-bench (tsc -> dist/) ..."
npx tsc

mkdir -p "$REPO_ROOT/prof"
echo "==> Running suite (node --trace-gc; log: prof/o1js-bench-run.log) ..."
# Run from o1js-bench/; the harness writes results to ../bench-results/.
node "${NODE_FLAGS[@]}" dist/bench.js 2>&1 | tee "$LOG"

RESULTS=$(grep -o '\[bench-results\] .*' "$LOG" | tail -1 | cut -d' ' -f2)
RESULTS="$BENCH_DIR/$RESULTS"

echo "==> Attaching GC stats from the trace-gc log ..."
node "$REPO_ROOT/packages/pickles-bench/parse_gclog.mjs" "$LOG" "$RESULTS"

echo "==> Results: $RESULTS"
