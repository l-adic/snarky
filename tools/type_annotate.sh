#!/usr/bin/env bash
# Annotate all let bindings in an OCaml function with their types from merlin.
#
# Usage:
#   ./tools/type_annotate.sh <file> <function_name>
#
# Example:
#   ./tools/type_annotate.sh src/lib/crypto/pickles/step_verifier.ml finalize_other_proof
#
# Outputs each let binding with its merlin-resolved type.

set -euo pipefail

FILE="$1"
FUNC="$2"

MINA_DIR="/home/martyall/code/l-adic/snarky/mina"
PYTHON="/home/martyall/code/l-adic/snarky/.venv/bin/python3"

cd "$MINA_DIR"

# First, find all let binding lines in the function using grep
# Then batch-query merlin for each
LINES=$(grep -n "let " "$FILE" | grep -v "^[[:space:]]*(\*" | awk -F: '{print $1}')

# Find the function start line
FUNC_START=$(grep -n "let ${FUNC}\b" "$FILE" | head -1 | cut -d: -f1)
if [ -z "$FUNC_START" ]; then
    echo "Function '$FUNC' not found in $FILE"
    exit 1
fi

# Find the rough end of the function (next top-level let at same or lesser indent)
# This is a heuristic - we'll query lines within a generous range
FUNC_END=$((FUNC_START + 500))
FILE_LINES=$(wc -l < "$FILE")
if [ "$FUNC_END" -gt "$FILE_LINES" ]; then
    FUNC_END="$FILE_LINES"
fi

echo "=== Type annotations for '$FUNC' in $FILE ==="
echo "=== Function starts at line $FUNC_START ==="
echo ""

# Build a batch of merlin queries
# We query the first identifier on each "let x = ..." line within the function
nix develop "git+file://${MINA_DIR}?submodules=1" --command bash -c "
grep -n 'let ' '${FILE}' | while IFS=: read -r line rest; do
    if [ \"\$line\" -ge ${FUNC_START} ] && [ \"\$line\" -le ${FUNC_END} ]; then
        # Find column of the binding name (after 'let ')
        col=\$(echo \"\$rest\" | sed 's/^[[:space:]]*//' | awk '{
            # Find position after \"let \"
            match(\$0, /let [a-zA-Z_(]/)
            if (RSTART > 0) print RSTART + 4
            else print 10
        }')
        result=\$(ocamlmerlin single type-enclosing -position \"\${line}:\${col}\" -filename '${FILE}' < '${FILE}' 2>/dev/null)
        echo \"LINE:\${line}:COL:\${col}:REST:\${rest}\"
        echo \"MERLIN:\${result}\"
    fi
done
" 2>/dev/null | "$PYTHON" -c "
import json, sys

lines = sys.stdin.read().split('\n')
i = 0
while i < len(lines):
    if lines[i].startswith('LINE:'):
        parts = lines[i].split(':', 5)
        line_num = parts[1]
        col = parts[3]
        source = parts[5] if len(parts) > 5 else ''

        i += 1
        if i < len(lines) and lines[i].startswith('MERLIN:'):
            merlin_json = lines[i][7:]
            try:
                data = json.loads(merlin_json)
                if data.get('class') == 'return' and data.get('value'):
                    # Find the narrowest type that covers just this binding
                    for entry in data['value']:
                        typ = entry['type']
                        # Skip module signatures (too verbose)
                        if typ.startswith('sig') or len(typ) > 200:
                            typ = typ[:100] + '...'
                        print(f'L{line_num:>4s}  {source.strip()[:70]}')
                        print(f'       :: {typ}')
                        print()
                        break
                else:
                    print(f'L{line_num:>4s}  {source.strip()[:70]}')
                    print(f'       :: <no type>')
                    print()
            except json.JSONDecodeError:
                print(f'L{line_num:>4s}  {source.strip()[:70]}')
                print(f'       :: <parse error>')
                print()
    i += 1
"
