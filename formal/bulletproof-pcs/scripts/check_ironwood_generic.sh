#!/usr/bin/env bash
# The reuse claim behind this package's forking layer is that ironwood's Fiat-Shamir game and its
# escape counting are generic in the oracle CODOMAIN — they ask for `Fintype`/`Nonempty`/`Zero`,
# never a field. That is what lets the error divide by the 2^128 prechallenge domain instead of
# `Fintype.card F`, and what lets one game serve both `m = 0` (bare IPA) and `m > 0` (kimchi).
# The claim is load-bearing and invisible to the axiom gates, so it is checked by compilation:
# every example in the .lean file is discharged by `exact`ing the upstream theorem at
# `Fin (2 ^ 128)`. A failure here means the pinned ironwood no longer supports the instantiation.
set -euo pipefail
cd "$(dirname "$0")/../.."
if ! out=$(lake env lean bulletproof-pcs/scripts/check_ironwood_generic.lean 2>&1); then
  echo "✗ ironwood's game/counting layers no longer instantiate at the prechallenge codomain"
  echo "--- got ---"; echo "$out"; exit 1
fi
if [[ -n "$out" ]]; then
  echo "✗ unexpected output (expected none)"; echo "--- got ---"; echo "$out"; exit 1
fi
echo "✓ ironwood's PrefixDecode, scanner, escape triple, counting bound and coin-tree traversal"
echo "  all instantiate at codomain Fin (2^128); our Wins IS fsWinsFull at m = 0 by Iff.rfl"
