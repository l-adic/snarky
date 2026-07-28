#!/usr/bin/env bash
# Dead-code GATE (nonzero exit on failure): every authored declaration must be reachable from
# the union of the packages' roots.txt manifests, and every script-surface root must appear in
# a scripts/ file. Driver: scripts/deadcode.lean. Requires a prior `lake build`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/deadcode.lean
