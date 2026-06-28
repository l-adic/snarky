#!/usr/bin/env bash
# Gate the headline theorems' axiom closure: fails unless every axiom is the standard logical
# set plus the two trusted Pasta point-count axioms. Subsumes a `sorryAx` grep. Driver:
# scripts/check_axioms.lean. Requires a prior `lake build Kimchi`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_axioms.lean
