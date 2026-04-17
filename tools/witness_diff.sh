#!/usr/bin/env bash
# Compare a PS witness dump against an OCaml witness fixture.
# Usage: witness_diff.sh <ocaml_fixture> <ps_dump> [row_labels_file]
#
# Finds the first (col, row) where the witnesses differ and optionally
# cross-references the row against a PS row-label dump.

set -e

OC="$1"
PS="$2"
LABELS="${3:-}"

if [ -z "$OC" ] || [ -z "$PS" ]; then
  echo "Usage: $0 <ocaml_fixture> <ps_dump> [row_labels_file]" >&2
  exit 1
fi

# Strip # header lines and diff
FIRST_DIFF=$(diff <(grep -v "^#" "$OC") <(grep -v "^#" "$PS") | head -1)

if [ -z "$FIRST_DIFF" ]; then
  echo "✓ Witnesses match byte-for-byte."
  exit 0
fi

# Extract line number from diff output (e.g., "108,114c108,114" → 108)
LINE_NUM=$(echo "$FIRST_DIFF" | sed 's/[^0-9].*//')

# Get the actual values
OC_LINE=$(grep -v "^#" "$OC" | sed -n "${LINE_NUM}p")
PS_LINE=$(grep -v "^#" "$PS" | sed -n "${LINE_NUM}p")

OC_COL=$(echo "$OC_LINE" | awk '{print $1}')
OC_ROW=$(echo "$OC_LINE" | awk '{print $2}')
OC_VAL=$(echo "$OC_LINE" | awk '{print $3}')
PS_VAL=$(echo "$PS_LINE" | awk '{print $3}')

echo "✗ First witness mismatch at col=$OC_COL row=$OC_ROW"
echo "  OCaml: $OC_VAL"
echo "  PS:    $PS_VAL"

# Cross-reference with row labels if provided
if [ -n "$LABELS" ] && [ -f "$LABELS" ]; then
  echo ""
  echo "  Row $OC_ROW context:"
  grep "^${OC_ROW}\.\." "$LABELS" | tail -1 | awk -F'\t' '{print "    " $2}'
fi
