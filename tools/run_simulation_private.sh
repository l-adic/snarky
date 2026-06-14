#!/usr/bin/env bash
#
# Privacy split of the example app: the browser proves the per-transaction
# BASE proofs locally (private witnesses stay on-device) and POSTs only the
# proofs + public ledger statements to the server, which merges them into a
# verified block root.
#
# Starts two processes:
#   - merge-server.mjs  (native kimchi backend) on :8099, serving POST /merge
#   - vite dev server   on :5173, serving the page + bundling the wasm worker
#
# vite proxies /merge -> :8099 (see web/vite.config.mjs), so the browser sees
# a same-origin endpoint. Once both are up, open:
#
#   http://localhost:5173/private.html
#
set -e
cd "$(dirname "${BASH_SOURCE[0]}")/../packages/example/app"

# Build the shared purs-backend-es output once (used by both servers).
npm run build:ps

# Clear any stale merge server from a previous run (it binds :8099).
lsof -ti tcp:8099 2>/dev/null | xargs kill -9 2>/dev/null || true

# Native merge server in the background; killed when this script exits.
( cd ../../.. && node packages/example/app/web/merge-server.mjs ) &
MERGE_PID=$!
trap 'kill "$MERGE_PID" 2>/dev/null || true' EXIT

echo "private split: open http://localhost:5173/private.html once vite is ready"
npx vite --config web/vite.config.mjs --host
