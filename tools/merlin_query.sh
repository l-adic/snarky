#!/usr/bin/env bash
# Query OCaml merlin for type information at a specific position.
#
# Usage:
#   ./tools/merlin_query.sh <file> <line> <col>
#
# Example:
#   ./tools/merlin_query.sh src/lib/crypto/pickles/step_verifier.ml 890 10
#
# Must be run from the mina directory (or it will cd there).
# Requires nix with the mina flake.

set -euo pipefail

FILE="$1"
LINE="$2"
COL="$3"

MINA_DIR="/home/martyall/code/l-adic/snarky/mina"
PYTHON="/home/martyall/code/l-adic/snarky/.venv/bin/python3"

cd "$MINA_DIR"

RAW=$(nix develop "git+file://${MINA_DIR}?submodules=1" --command bash -c "
ocamlmerlin single type-enclosing -position '${LINE}:${COL}' -filename '${FILE}' < '${FILE}' 2>/dev/null
" 2>/dev/null)

echo "$RAW" | "$PYTHON" -c "
import json, sys
data = json.load(sys.stdin)
if data.get('class') == 'failure':
    print('ERROR:', data.get('value', 'unknown'))
    sys.exit(1)
entries = data.get('value', [])
# Show progressively wider enclosings
for i, entry in enumerate(entries):
    start = entry['start']
    end = entry['end']
    typ = entry['type']
    # Skip duplicates
    if i > 0 and typ == entries[i-1]['type']:
        continue
    span = f'L{start[\"line\"]}:{start[\"col\"]}-L{end[\"line\"]}:{end[\"col\"]}'
    print(f'[{i}] {span}')
    print(f'    {typ}')
    print()
    if i >= 6:
        remaining = len(entries) - i - 1
        if remaining > 0:
            print(f'  ... ({remaining} more enclosings)')
        break
"
