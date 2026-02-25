#!/usr/bin/env bash
# Query merlin for the type of an expression at a specific position.
# Runs inside nix develop for the mina project.
#
# Usage:
#   ./tools/merlin_type.sh <file_relative_to_mina> <line> <col>
#
# Examples:
#   # What type is `xi_actual` at line 989, col 12?
#   ./tools/merlin_type.sh src/lib/crypto/pickles/step_verifier.ml 989 12
#
#   # What type is the `sponge` parameter at line 833, col 10?
#   ./tools/merlin_type.sh src/lib/crypto/pickles/step_verifier.ml 833 10

set -euo pipefail

FILE="$1"
LINE="$2"
COL="$3"

MINA_DIR="/home/martyall/code/l-adic/snarky/mina"

cd "$MINA_DIR"

nix develop "git+file://${MINA_DIR}?submodules=1" --command bash -c "
ocamlmerlin single type-enclosing -position '${LINE}:${COL}' -filename '${FILE}' < '${FILE}' 2>/dev/null
" 2>/dev/null | python3 -c "
import json, sys
data = json.load(sys.stdin)
if data.get('class') == 'failure':
    print('ERROR:', data.get('value', 'unknown'))
    sys.exit(1)
seen = set()
for entry in data.get('value', []):
    typ = entry['type']
    if typ in seen:
        continue
    seen.add(typ)
    s, e = entry['start'], entry['end']
    span = f'L{s[\"line\"]}:{s[\"col\"]}-L{e[\"line\"]}:{e[\"col\"]}'
    # Truncate very long types (module sigs)
    if len(typ) > 500:
        typ = typ[:500] + '\n  ... (truncated)'
    print(f'{span}')
    print(f'  {typ}')
    print()
    if len(seen) >= 5:
        break
"
