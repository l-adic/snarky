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

# Per-config timeout (seconds): no config should hang the whole matrix. o1js-wasm
# is the long pole (per-trial fresh processes, ~10-12 min); default leaves room.
TIMEOUT="${BENCH_TIMEOUT:-2400}"

# --- single-tenant lock (#7): a second bench MUST NOT start concurrently — it
# skews numbers and was the direct cause of the deadlocks. mkdir is atomic.
LOCK="$REPO_ROOT/bench-results/.matrix.lock"
if ! mkdir "$LOCK" 2>/dev/null; then
  echo "ERROR: another bench holds $LOCK ($(cat "$LOCK/info" 2>/dev/null)). Refusing to start." >&2
  echo "       Concurrent benches invalidate numbers and can deadlock. If stale: rm -rf '$LOCK'." >&2
  exit 1
fi
echo "pid $$ started $(date)" > "$LOCK/info"
trap 'rm -rf "$LOCK"' EXIT

prof="$(powerprofilesctl get 2>/dev/null || echo unknown)"
load1="$(awk '{print $1}' /proc/loadavg 2>/dev/null || echo '?')"
busy="$(pgrep -fc 'run\.mjs|dist/bench\.js' 2>/dev/null || echo 0)"
echo "==> matrix run ${RUNID}: ${ITERS} iters x 4 configs, gap ${GAP}s, timeout ${TIMEOUT}s/config"
echo "    power=${prof}  load1=${load1}  competing-bench-procs=${busy}"
[ "$prof" = performance ] || echo "    WARNING: power profile '${prof}' != performance (see README §1 for the intel_pstate/sysfs fallback if powerprofilesctl is absent)."
awk -v l="$load1" 'BEGIN{exit !(l+0 > 2)}' 2>/dev/null && echo "    WARNING: load average ${load1} is high — the box may not be idle; numbers will be skewed."
[ "${busy:-0}" -gt 0 ] 2>/dev/null && echo "    WARNING: ${busy} competing run.mjs/bench.js process(es) — STOP them; concurrent benches deadlock and corrupt results."

# Run one config under a timeout; $1=tag, $2=iter. On timeout: mark MISSING,
# kill stragglers, continue (one bad config must not eat the whole run).
run_cfg() {
  local tag="$1" i="$2"
  local out="${PREFIX}-${tag}-i${i}.json"
  local log="${PREFIX}-${tag}-i${i}.log"
  local rc=0
  echo "[$(date +%T)] iter ${i}  ${tag}  (timeout ${TIMEOUT}s)"
  case "$tag" in
    ps-native)   timeout "$TIMEOUT" env BENCH_RESULTS_FILE="$out" tools/bench.sh               > "$log" 2>&1 || rc=$? ;;
    o1js-native) timeout "$TIMEOUT" env BENCH_RESULTS_FILE="$out" tools/bench_o1js.sh --native > "$log" 2>&1 || rc=$? ;;
    ps-wasm)
      # bench.sh tags wasm artifacts by inserting `wasm-` after `bench-results/`;
      # move it back to our flat name so the aggregator finds it.
      timeout "$TIMEOUT" env BENCH_RESULTS_FILE="$out" tools/bench.sh --wasm > "$log" 2>&1 || rc=$?
      mv "bench-results/wasm-${RUNID}-${tag}-i${i}.json" "$out" 2>/dev/null || true
      ;;
    o1js-wasm)   timeout "$TIMEOUT" env BENCH_RESULTS_FILE="$out" tools/bench_o1js.sh          > "$log" 2>&1 || rc=$? ;;
  esac
  if [ "$rc" = 124 ]; then
    echo "          !! TIMEOUT after ${TIMEOUT}s — marking MISSING + killing stragglers"
    pkill -9 -f 'run\.mjs' 2>/dev/null || true
    pkill -9 -f 'dist/bench\.js' 2>/dev/null || true
  fi
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
