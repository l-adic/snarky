#!/usr/bin/env bash
# Run Batteries' environment linters (`#lint`) over the Kimchi.* declarations only
# (not Mathlib's). Exits non-zero on any finding so it can gate CI. Driver: scripts/lint.lean.
#
# Note: the project must be built first (`lake build Kimchi`) so the oleans exist.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "Running Lean environment linters on Kimchi ..."
if lake env lean scripts/lint.lean; then
  echo "✓ Lean linters OK"
else
  echo "✗ Lean linters reported findings (see above)"
  exit 1
fi
