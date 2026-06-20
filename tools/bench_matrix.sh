#!/usr/bin/env bash
#
# Full bench matrix: snarky-PS vs o1js × native vs wasm, ITERS iterations each,
# one JSON artifact per iteration, then a combined summary.md.
#
#   tools/bench_matrix.sh [ITERS]      # default 3
#
# Per iteration the four configs run in this order, each >= GAP seconds apart so
# a PS<->o1js pairing is never a thermal artifact (override with BENCH_GAP_SECS):
#     ps-native -> o1js-native -> ps-wasm -> o1js-wasm
#
# Outputs (all under bench-results/, prefixed with a per-run id):
#     <runid>-{ps,o1js}-{native,wasm}-i<N>.json   one per iteration
#     <runid>-...-i<N>.log                         raw run log (kept for triage)
#     <runid>-summary.md                           the combined summary
#
# PREREQS (see bench/README.md): performance power profile, idle machine, the
# native + wasm kimchi-napi builds, SRS fetched, gen-linearization done,
# `cd bench/o1js && npm install`. Same node both stacks (the launchers pin
# v23.11.1) so the comparison is runtime-constant.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

ITERS="${1:-3}"
GAP="${BENCH_GAP_SECS:-60}"
RUNID="$(date +%Y%m%d-%H%M%S)"
PREFIX="bench-results/${RUNID}"
mkdir -p bench-results

prof="$(powerprofilesctl get 2>/dev/null || echo unknown)"
echo "==> matrix run ${RUNID}: ${ITERS} iters x 4 configs, gap ${GAP}s, power=${prof}"
[ "$prof" = performance ] || echo "    WARNING: power profile is '${prof}', want 'performance' (powerprofilesctl set performance)"

# Run one config; $1=tag (ps-native|o1js-native|ps-wasm|o1js-wasm), $2=iter.
run_cfg() {
  local tag="$1" i="$2"
  local out="${PREFIX}-${tag}-i${i}.json"
  local log="${PREFIX}-${tag}-i${i}.log"
  echo "[$(date +%T)] iter ${i}  ${tag}"
  case "$tag" in
    ps-native)   BENCH_RESULTS_FILE="$out" tools/bench.sh            > "$log" 2>&1 ;;
    o1js-native) BENCH_RESULTS_FILE="$out" tools/bench_o1js.sh --native > "$log" 2>&1 ;;
    ps-wasm)
      # bench.sh tags wasm artifacts by inserting `wasm-` after `bench-results/`;
      # move it back to our flat name so the aggregator finds it.
      BENCH_RESULTS_FILE="$out" tools/bench.sh --wasm > "$log" 2>&1
      mv "bench-results/wasm-${RUNID}-${tag}-i${i}.json" "$out" 2>/dev/null || true
      ;;
    o1js-wasm)   BENCH_RESULTS_FILE="$out" tools/bench_o1js.sh      > "$log" 2>&1 ;;
  esac
  if [ -f "$out" ]; then echo "          -> $out"; else echo "          !! MISSING $out (see $log)"; fi
}

for i in $(seq 1 "$ITERS"); do
  for tag in ps-native o1js-native ps-wasm o1js-wasm; do
    run_cfg "$tag" "$i"
    sleep "$GAP"
  done
done

echo "==> aggregating -> ${PREFIX}-summary.md"
node tools/bench_summary.mjs ${PREFIX}-*-i*.json > "${PREFIX}-summary.md"
echo "==> DONE"
echo "    summary:    ${PREFIX}-summary.md"
echo "    artifacts:  ${PREFIX}-*-i*.json"
cat "${PREFIX}-summary.md"
