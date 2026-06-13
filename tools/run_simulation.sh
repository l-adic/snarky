#!/usr/bin/env bash
#
# Builds and runs the example simulation on the purs-backend-es
# optimized output.
#
# The example workspace is its OWN spago workspace
# (packages/example has a spago.yaml with a `workspace:`
# section, so the root workspace ignores it). Only this workspace uses
# the purs-backend-es backend; the root workspace stays on the plain JS
# backend so normal library development (and the example test suite)
# is unaffected.
#
# We `cd` into the workspace and build there (corefn ->
# purs-backend-es -> packages/example/output-es/), then
# execute the optimized entrypoint with node directly. `spago run`
# does NOT work with the purs-backend-es backend (spago re-invokes the
# backend as a runner with `--run`, which purs-backend-es rejects).
#
# The run performs the full one-block pipeline: SRS build + circuit
# compile, genesis, block generation, 4 base proofs + 3 merges, root
# proof verification. Expect ~10 minutes.

set -e

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SIM_DIR="$REPO_ROOT/packages/example"

# Build from inside the workspace dir (spago must be run there to
# detect the example workspace).
echo "==> Building example workspace (purs-backend-es -> output-es/) ..."
( cd "$SIM_DIR" && npx spago build )

# Run from the REPO ROOT: the SRS cache resolves at the relative path
# `srs-cache/` (populated by `make fetch-srs`), and kimchi-napi
# resolves from the root node_modules.
echo "==> Running optimized Snarky.Example.Main ..."
cd "$REPO_ROOT"
node packages/example/terminal/run.mjs "$@"
