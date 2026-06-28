#!/usr/bin/env bash
# Reachability / dead-code report: lists authored Kimchi.* declarations not reachable from the
# API root set in roots.txt. Driver: scripts/deadcode.lean. Requires a prior `lake build Kimchi`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/deadcode.lean
