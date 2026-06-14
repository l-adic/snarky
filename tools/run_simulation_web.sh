#!/usr/bin/env bash
#
# Browser frontend of the example app. Thin wrapper over the npm
# scripts in packages/example/app/package.json (the workspace package
# that owns the web deps + build orchestration):
#
#   tools/run_simulation_web.sh           # npm run dev     (vite dev server, COOP/COEP)
#   tools/run_simulation_web.sh --build   # npm run bundle  (production bundle -> web/dist)
set -e
cd "$(dirname "${BASH_SOURCE[0]}")/../packages/example/app"
if [ "${1:-}" = "--build" ]; then
  npm run bundle
else
  npm run dev
fi
