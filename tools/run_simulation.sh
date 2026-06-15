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
#   tools/run_simulation.sh            # plain run
#   tools/run_simulation.sh --split    # split-screen with the worker log
#
# With --split, the run opens in a throwaway tmux session: the simulation
# on top, a live `tail -F` of the snark worker setup log
# (snark-worker.log) below it. The log is truncated fresh at the START
# of each run and is NEVER deleted at the end — so after the run you can
# scroll it (tmux copy-mode: prefix + [) and inspect it on disk. When you
# are done, press Enter in the simulation pane to throw the session away;
# the log file stays. Any other args are passed through to the simulation.

set -e

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SIM_DIR="$REPO_ROOT/packages/example/app"
WORKER_LOG="$REPO_ROOT/snark-worker.log"

# Pull our own --split flag out of the args; everything else is passed
# through to the simulation entrypoint.
SPLIT=0
ARGS=()
for arg in "$@"; do
  case "$arg" in
    --split) SPLIT=1 ;;
    *) ARGS+=("$arg") ;;
  esac
done

# Build from inside the workspace dir (spago must be run there to
# detect the frontends workspace). Build BEFORE opening tmux so build
# errors surface in this terminal, not a transient pane.
echo "==> Building example frontends workspace (purs-backend-es -> output-es/) ..."
( cd "$SIM_DIR" && npx spago build )

# Run from the REPO ROOT: the SRS cache resolves at the relative path
# `srs-cache/` (populated by `make fetch-srs`), and kimchi-napi
# resolves from the root node_modules.
cd "$REPO_ROOT"

if [ "$SPLIT" -eq 0 ]; then
  echo "==> Running optimized Snarky.Example.Main ..."
  exec node packages/example/app/terminal/run.mjs "${ARGS[@]}"
fi

if ! command -v tmux >/dev/null 2>&1; then
  echo "error: --split needs tmux on PATH (run without --split, or tail $WORKER_LOG yourself)" >&2
  exit 1
fi

# Fresh worker log for this run; kept on disk afterwards for debugging.
: > "$WORKER_LOG"

SESSION="snark-sim-$$"
SIM_CMD="node packages/example/app/terminal/run.mjs ${ARGS[*]}"
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
