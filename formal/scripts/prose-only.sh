#!/usr/bin/env bash
# Is a change to these files PROSE ONLY — every code line untouched?
#
#   scripts/prose-only.sh kimchi/Kimchi/Gate/Semantics/VarBaseMul.lean
#   scripts/prose-only.sh --base HEAD~1 <file>...
#
# Compares each file against its committed version with the comments stripped, so blank
# lines, re-wrapped prose and git's choice of diff algorithm cannot register — only a changed
# code line can. A comment pass that edits code is two changes, and the second hides in the
# first.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2   # -> formal/

base=HEAD
if [ "${1:-}" = "--base" ]; then base="$2"; shift 2; fi
[ $# -ge 1 ] || { echo "usage: prose-only.sh [--base <rev>] <file>..." >&2; exit 2; }

strip() {  # Lean source on stdin -> code lines only
  python3 -c '
import sys
depth = 0
for line in sys.stdin:
    out = []
    i = 0
    while i < len(line):
        two = line[i:i+2]
        if depth == 0 and two == "--":
            break
        if two == "/-":
            depth += 1; i += 2; continue
        if two == "-/" and depth > 0:
            depth -= 1; i += 2; continue
        if depth == 0:
            out.append(line[i])
        i += 1
    s = "".join(out).strip()
    if s:
        print(s)
'
}

bad=0
for f in "$@"; do
  rel="${f#formal/}"
  # an unreadable file strips to nothing on both sides and would pass: refuse it
  if [ ! -f "$rel" ]; then echo "✗ $rel: no such file"; bad=1; continue; fi
  if ! git cat-file -e "$base:./$rel" 2>/dev/null; then
    echo "✗ $rel: not in $base (a new file is not a prose-only change)"; bad=1; continue
  fi
  a=$(git show "$base:./$rel" 2>/dev/null | strip)
  b=$(strip < "$rel")
  if [ "$a" != "$b" ]; then
    echo "✗ $rel: code changed, not only prose"
    diff <(printf '%s\n' "$a") <(printf '%s\n' "$b") | head -20
    bad=1
  fi
done
[ "$bad" -eq 0 ] && echo "✓ prose only ($# file(s))"
exit "$bad"
