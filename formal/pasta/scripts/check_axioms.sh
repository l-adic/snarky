#!/usr/bin/env bash
# Gate the Pasta trust base: derived theorems reduce to standard axioms + Hasse +
# CompElliptic certificates only (eigen is downstream-only). Requires `lake build Pasta`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/check_axioms.lean
