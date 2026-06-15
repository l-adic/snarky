#!/usr/bin/env bash
#
# Terminal-wasm frontend: runs the SAME shared engine as the browser
# (Snarky.Example.Engine), over the wasm32-wasip1-threads kimchi backend,
# in the terminal — no UI framework, just stdout logs + the pinned
# scan-state tree. Single-instance (localSnarkBackend); the worker pool is
# the native app (tools/run_simulation.sh).
#
# Builds the app workspace (purs-backend-es -> output-es/), then runs
# WasmMain with KIMCHI_BACKEND=wasm so kimchi-napi loads the wasm node
# loader and sizes its rayon pool (= core count) at require time. Runs from
# the repo root so srs-cache/ and node_modules resolve. Expect it slower
# than native (wasm prove is ~2.7×).

set -e

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

echo "==> Building example frontends workspace (purs-backend-es -> output-es/) ..."
( cd "$REPO_ROOT/packages/example/app" && npx spago build )

echo "==> Running Snarky.Example.WasmMain over wasm kimchi ..."
cd "$REPO_ROOT"
exec env KIMCHI_BACKEND=wasm node packages/example/app/terminal/wasm-run.mjs "$@"
