#!/usr/bin/env bash
# The data-valued extractor must actually compute, not merely typecheck: `Classical.choice`
# reaches everything over a Mathlib `Field` — including ironwood's own `ipa_extractV` — so the
# axiom list cannot tell a computed witness from a choice-conjured one. Running it can.
set -euo pipefail
cd "$(dirname "$0")/../.."
out=$(lake env lean bulletproof-pcs/scripts/check_extractor_computes.lean)
expected=$'(4, 6)\n(true, true)\n(4, 6)\n(true, true)\nsome (4, 1)'
if [[ "$out" != "$expected" ]]; then
  echo "✗ extractor did not compute the expected witness"; echo "--- got ---"; echo "$out"; exit 1
fi
echo "✓ ipaExtract, openingOfAcceptV and kimchiOpeningOrBreak compute: the kimchi transcript"
echo "  extracts to its witness at every layer, including the full Schnorr-fork capstone"
