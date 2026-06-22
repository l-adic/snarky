#!/usr/bin/env bash
# Thin wrapper — sets up the pinned node and delegates to bench_matrix.mjs.
# All orchestration logic lives in the JS script; see --help.
set -euo pipefail
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$REPO_ROOT/tools/lib/common.sh"
source "$REPO_ROOT/tools/lib/setup-node.sh"
cd "$REPO_ROOT"
exec node "$REPO_ROOT/tools/bench_matrix.mjs" "$@"
