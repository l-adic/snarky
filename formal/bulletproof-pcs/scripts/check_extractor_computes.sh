#!/usr/bin/env bash
# The data-valued extractor must actually compute, not merely typecheck: `Classical.choice`
# reaches everything over a Mathlib `Field`, so the axiom list cannot tell a computed witness
# from a choice-conjured one. Running it on a fixture can.
set -euo pipefail
cd "$(dirname "$0")/../.."
out=$(lake env lean bulletproof-pcs/scripts/check_extractor_computes.lean)
expected=$'(4, 6)\n(true, true)'
if [[ "$out" != "$expected" ]]; then
  echo "✗ extractor did not compute the expected witness"; echo "$out"; exit 1
fi
echo "✓ ipaExtract computes: depth-1 kimchi transcript extracts to its witness, both equations hold"
