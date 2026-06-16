#!/usr/bin/env bash
#
# Builds and runs the example simulation on the purs-backend-es
# optimized output.
#
# The frontends are their OWN spago workspace
# (packages/example/app has a spago.yaml with a `workspace:` section, so
# the root workspace ignores it). Only this workspace uses the
# purs-backend-es backend; the root workspace stays on the plain JS
# backend so normal library development (and the example test suite)
# is unaffected.
#
# We `cd` into the workspace and build there (corefn ->
# purs-backend-es -> packages/example/app/output-es/), then
# execute the optimized entrypoint with node directly. `spago run`
# does NOT work with the purs-backend-es backend (spago re-invokes the
# backend as a runner with `--run`, which purs-backend-es rejects).
#
# The run performs the full one-block pipeline: SRS build + circuit
# compile, genesis, block generation, 8 base proofs + 7 merges, root
# proof verification. Expect ~10 minutes.
#
# Usage:
#   tools/run_simulation.sh [options]
#
# Options:
#   --split               Split-screen: simulation on top, a live tail of the
#                         worker setup log (snark-worker.log) below it, in a
#                         throwaway tmux session. The log is truncated fresh at
#                         the START of each run and NEVER deleted at the end, so
#                         you can scroll it (tmux copy-mode: prefix + [) and
#                         inspect it on disk afterward. Press Enter in the sim
#                         pane to throw the session away; the log file stays.
#
#   --pool-size N         worker threads                  (env SNARK_POOL_SIZE)
#   --job-timeout S       per-job timeout, seconds        (env SNARK_JOB_TIMEOUT_S)
#   --wasm                run the pool over the wasm kimchi backend, splitting
#                         rayon threads evenly across the pool (each instance
#                         gets cores/N). env KIMCHI_BACKEND=wasm +
#                         KIMCHI_WASM_RAYON_THREADS. Slower than native, and
#                         memory-bound (N+1 wasm instances, each up to ~4GB) —
#                         keep N small (2-3).
#
#   Fault injection (for exercising the pool's reliability paths):
#   --delay-ms MS         stall a job MS ms before proving (env SNARK_WORKER_DELAY_MS)
#   --delay-pct PCT       % of jobs to stall, default 50   (env SNARK_WORKER_DELAY_PCT)
#   --crash-pct PCT       % of jobs that crash the worker  (env SNARK_WORKER_CRASH_PCT)
#
# The config/fault flags just set the corresponding env vars for the run (and
# are passed through to the worker threads), so e.g.
#   tools/run_simulation.sh --split --job-timeout 10 --delay-ms 20000 --delay-pct 40
# stalls ~40% of jobs for 20s against a 10s timeout, so the pool times out and
# reassigns them. Any other args pass through to the simulation.

set -e

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SIM_DIR="$REPO_ROOT/packages/example/app"
WORKER_LOG="$REPO_ROOT/snark-worker.log"

# Print the Usage block (everything from "# Usage:" up to `set -e`).
usage() { sed -n '/^# Usage:/,/^set -e/p' "${BASH_SOURCE[0]}" | sed '$d' | sed 's/^# \{0,1\}//'; }

# A value-taking flag needs its argument.
need() { [ -n "$2" ] || { echo "error: $1 needs a value" >&2; exit 1; }; }

# Pull our own flags out of the args. Config/fault flags become env-var
# assignments (ENVV); everything else passes through to the simulation.
SPLIT=0
WASM=0
POOL_SIZE=4 # mirrors Main's defaultPoolSize; used for the --wasm rayon split
ENVV=()
ARGS=()
while [ $# -gt 0 ]; do
  case "$1" in
    --split) SPLIT=1; shift ;;
    --wasm) WASM=1; shift ;;
    --pool-size) need "$1" "${2:-}"; POOL_SIZE="$2"; ENVV+=("SNARK_POOL_SIZE=$2"); shift 2 ;;
    --job-timeout) need "$1" "${2:-}"; ENVV+=("SNARK_JOB_TIMEOUT_S=$2"); shift 2 ;;
    --delay-ms) need "$1" "${2:-}"; ENVV+=("SNARK_WORKER_DELAY_MS=$2"); shift 2 ;;
    --delay-pct) need "$1" "${2:-}"; ENVV+=("SNARK_WORKER_DELAY_PCT=$2"); shift 2 ;;
    --crash-pct) need "$1" "${2:-}"; ENVV+=("SNARK_WORKER_CRASH_PCT=$2"); shift 2 ;;
    -h | --help) usage; exit 0 ;;
    *) ARGS+=("$1"); shift ;;
  esac
done

# --wasm: select the wasm kimchi loader and split rayon threads evenly across
# the pool — each of the N+1 wasm instances (the N workers + the coordinator)
# gets cores/N, so they don't oversubscribe the cores. The env reaches the
# worker threads via the same ENVV pass-through used below.
if [ "$WASM" -eq 1 ]; then
  cores=$(nproc)
  per=$(( cores / POOL_SIZE )); [ "$per" -lt 1 ] && per=1
  ENVV+=("KIMCHI_BACKEND=wasm" "KIMCHI_WASM_RAYON_THREADS=$per")
  echo "==> wasm backend: $POOL_SIZE worker(s) × $per rayon threads (of $cores cores)"
  [ "$POOL_SIZE" -ge 4 ] && echo "    note: $((POOL_SIZE + 1)) wasm instances, each up to ~4GB — watch memory"
fi

# Build from inside the workspace dir (spago must be run there to
# detect the frontends workspace). Build BEFORE opening tmux so build
# errors surface in this terminal, not a transient pane.
echo "==> Building example frontends workspace (purs-backend-es -> output-es/) ..."
( cd "$SIM_DIR" && npx spago build )

# Run from the REPO ROOT: the SRS cache resolves at the relative path
# `srs-cache/` (populated by `make fetch-srs`), and kimchi-napi
# resolves from the root node_modules.
cd "$REPO_ROOT"

[ ${#ENVV[@]} -eq 0 ] || echo "==> config: ${ENVV[*]}"

if [ "$SPLIT" -eq 0 ]; then
  echo "==> Running optimized Snarky.Example.Main ..."
  exec env "${ENVV[@]}" node packages/example/app/terminal/run.mjs "${ARGS[@]}"
fi

if ! command -v tmux >/dev/null 2>&1; then
  echo "error: --split needs tmux on PATH (run without --split, or tail $WORKER_LOG yourself)" >&2
  exit 1
fi

# Fresh worker log for this run; kept on disk afterwards for debugging.
: > "$WORKER_LOG"

SESSION="snark-sim-$$"
# Pass the env-var assignments explicitly into the pane: a tmux pane inherits
# the tmux server's environment, not necessarily this shell's, so config/fault
# flags must be baked into the command to reach node (and its worker threads).
SIM_CMD="env ${ENVV[*]} node packages/example/app/terminal/run.mjs ${ARGS[*]}"
# After the run, hold the session open so the worker log stays readable;
# Enter (in this pane) throws the whole session away. The log file is left
# untouched on disk.
HOLD="echo; echo '── run finished — scroll the worker log (prefix + [); press Enter here to close ──'; read -r"

echo "==> Running Snarky.Example.Main in tmux (sim on top, worker log below); Enter in the sim pane closes it ..."
tmux new-session -d -s "$SESSION" "$SIM_CMD; $HOLD; tmux kill-session -t $SESSION"
tmux split-window -v -t "$SESSION" "tail -F $WORKER_LOG"
tmux select-pane -t "$SESSION".0

# Attach from a plain shell; switch the client if we're already inside tmux
# (avoids the "sessions should be nested" error). Either way, killing the
# session on Enter returns you here / to your previous session.
if [ -n "${TMUX:-}" ]; then
  tmux switch-client -t "$SESSION"
else
  tmux attach-session -t "$SESSION"
fi
