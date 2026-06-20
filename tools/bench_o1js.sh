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
export PATH="$HOME/.nvm/versions/node/v23.11.1/bin:$PATH"

BACKEND=wasm
for a in "$@"; do
  case "$a" in
    --native) BACKEND=native ;;
    *) ;;
  esac
done
export O1JS_BACKEND="$BACKEND"

echo "==> Building o1js bench (tsc -> dist/) ..."
( cd "$O1JS_DIR" && npx tsc )

cd "$REPO_ROOT"
mkdir -p bench-results prof
RUN_LOG="prof/bench-o1js-run.log"

echo "==> Running o1js bench (backend=$BACKEND; node $(node --version)) ..."
node --trace-gc --expose-gc "$O1JS_DIR/dist/bench.js" 2>&1 \
  | tee "$RUN_LOG" \
  | grep -vE '^\[[0-9]+(:0x[0-9a-f]+)?\] ' || true

RESULTS_FILE=$(sed -n 's/^\[bench-results\] //p' "$RUN_LOG" | tail -1)
if [ -z "$RESULTS_FILE" ]; then
  echo "ERROR: no [bench-results] line found in the run output" >&2
  exit 1
fi

echo "==> Attaching GC stats from the trace-gc log ..."
node packages/pickles-bench/parse_gclog.mjs "$RUN_LOG" "$RESULTS_FILE"

echo "==> Results: $RESULTS_FILE"
