#!/usr/bin/env bash
#
# o1js bench launcher — the mirror of tools/bench.sh for the o1js side. Builds
# bench/o1js (tsc) and runs it under the SAME measurement pipeline: node
# --trace-gc (raw log -> prof/, terminal kept clean), the shared bench-harness
# emits identical [bench-window] markers, and parse_gclog.mjs attaches GC
# reclaim/trial to the same artifact schema.
#
#   tools/bench_o1js.sh            # wasm backend (o1js default)
#   tools/bench_o1js.sh --native  # @o1js/native (napi — pairs with PS native)
#
# Same node binary as bench.sh (v23.11.1) so the JS runtime is constant across
# the PS/o1js comparison. Results -> bench-results/<...>.json (o1js- / wasm-
# infix from writeArtifact). Run from the repo root.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
O1JS_DIR="$REPO_ROOT/bench/o1js"
# Pinned node (same as tools/bench.sh) — warn loudly if absent rather than
# silently using a different node, which would skew the PS/o1js comparison.
PINNED_NODE="$HOME/.nvm/versions/node/v23.11.1/bin"
if [ -x "$PINNED_NODE/node" ]; then
  export PATH="$PINNED_NODE:$PATH"
else
  echo "WARN: pinned node v23.11.1 not at $PINNED_NODE — using $(command -v node) ($(node --version 2>/dev/null)). PS and o1js MUST use the SAME node; install v23.11.1 or edit this PATH." >&2
fi
echo "==> node: $(node --version) ($(command -v node))"

BACKEND=wasm
NODE_FLAGS=(--trace-gc --expose-gc)
CPU_PROF=
ONLY=
while [ $# -gt 0 ]; do
  case "$1" in
    --native) BACKEND=native ;;
    # Mirror tools/bench.sh: capture a V8 CPU profile into prof/. NOTE: profiles
    # the main node process — clean for o1js NATIVE (single process), but for
    # o1js WASM the prover runs in per-trial CHILD processes, so this profiles
    # the orchestrator, not the prover. (V8 --cpu-prof also doesn't see napi/
    # worker isolates, same as the PS side.)
    --cpu-prof) CPU_PROF=1; NODE_FLAGS+=(--cpu-prof --cpu-prof-dir "$REPO_ROOT/prof") ;;
    # Mirror tools/bench.sh --only: restrict to one phase (compile|prove) via O1JS_ONLY.
    --only) ONLY="$2"; shift ;;
    --only=*) ONLY="${1#*=}" ;;
    *) ;;
  esac
  shift
done
export O1JS_BACKEND="$BACKEND"
[ -n "$ONLY" ] && export O1JS_ONLY="$ONLY"

echo "==> Building o1js bench (tsc -> dist/) ..."
( cd "$O1JS_DIR" && npx tsc )

cd "$REPO_ROOT"
mkdir -p bench-results prof
RUN_LOG="prof/bench-o1js-run.log"

echo "==> Running o1js bench (backend=$BACKEND; node $(node --version); flags ${NODE_FLAGS[*]}) ..."
# Line-buffer tee|grep so markers reach the terminal / cpu_timeline reader live.
node "${NODE_FLAGS[@]}" "$O1JS_DIR/dist/bench.js" 2>&1 \
  | stdbuf -oL tee "$RUN_LOG" \
  | grep --line-buffered -vE '^\[[0-9]+(:0x[0-9a-f]+)?\] ' || true

RESULTS_FILE=$(sed -n 's/^\[bench-results\] //p' "$RUN_LOG" | tail -1)
if [ -z "$RESULTS_FILE" ]; then
  echo "ERROR: no [bench-results] line found in the run output" >&2
  exit 1
fi

echo "==> Attaching GC stats from the trace-gc log ..."
node packages/pickles-bench/parse_gclog.mjs "$RUN_LOG" "$RESULTS_FILE"

if [ "${CPU_PROF:-}" = "1" ]; then
  CPU_PROFILE=$(ls -t prof/*.cpuprofile 2>/dev/null | head -1 || true)
  if [ -n "$CPU_PROFILE" ]; then
    echo "==> CPU profile summary ($CPU_PROFILE) ..."
    node packages/pickles-bench/analyze_cpuprofile.mjs "$CPU_PROFILE" || true
  fi
fi

echo "==> Results: $RESULTS_FILE"
