#!/usr/bin/env bash
# Lightweight style check for the Lean sources under formal/.
#
# Lean 4 has no autoformatter (no `lean fmt`), so this enforces the small set of
# mechanical conventions that keep Lean readable — the same ones Mathlib's
# text linter checks:
#   - lines at most 100 columns
#   - no trailing whitespace
#   - no tab characters
#   - every file ends with exactly one newline
#
# Usage:
#   check-style.sh        # check only; non-zero exit on any violation
#   check-style.sh --fix  # auto-correct the mechanical issues
#                         #   (trailing whitespace + final newline; the rest are
#                         #    reported for you to fix by hand)
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2   # -> formal/

fix=0
[ "${1:-}" = "--fix" ] && fix=1

# Collect our own source files (skip the Lake build dir, the vendored CompElliptic dependency
# submodule, .archon-seed/, which holds read-only copies of upstream sources staged for the
# prover harness, and .archon/, the prover harness's own state — all four carry style we do not
# own and none is committed here). The .archon/ clause matters for the *count* as much as for
# pickles/Pickles/Linearization/F{p,q}.lean are codegen output (pickles/scripts/
# gen_tokens.lean), one token per line with 255-bit field literals that run to the column
# limit. They are committed rather than gitignored — formal/'s CI checks out without the
# mina submodule and so cannot regenerate them — but they are not hand-written source and
# the formatter contract does not apply.
# the checks: .archon/logs/*/snapshots/*/baseline.lean is a pre-edit copy of a source file
# written once per snapshotting iteration, so without it the printed file count drifts upward
# over time (and a snapshot taken mid-edit can fail the gate for a reason outside the tree).
files=()
while IFS= read -r f; do files+=("$f"); done \
  < <(find . -name '*.lean' \
        -not -path '*/.lake/*' -not -path './vendor/*' -not -path './.archon-seed/*' \
        -not -path './.archon/*' \
        -not -path './pickles/Pickles/Linearization/F[pq].lean' | sort)

if [ "${#files[@]}" -eq 0 ]; then
  echo "no .lean files found under formal/"
  exit 0
fi

if [ "$fix" -eq 1 ]; then
  for f in "${files[@]}"; do
    sed -i 's/[[:space:]]*$//' "$f"                       # strip trailing whitespace
    [ -n "$(tail -c1 "$f")" ] && printf '\n' >> "$f"      # ensure final newline
  done
  echo "fixed: trailing whitespace + final newline"
fi

status=0
report() { # name, matches
  if [ -n "$2" ]; then printf '\n✗ %s:\n%s\n' "$1" "$2"; status=1; fi
}

report "lines over 100 columns" "$(grep -nE '.{101,}' "${files[@]}" 2>/dev/null)"
report "trailing whitespace"    "$(grep -nE '[[:blank:]]+$' "${files[@]}" 2>/dev/null)"
report "tab characters"         "$(grep -nP '\t'       "${files[@]}" 2>/dev/null)"

nonl=""
for f in "${files[@]}"; do [ -n "$(tail -c1 "$f")" ] && nonl="${nonl}${f}"$'\n'; done
report "missing final newline" "$nonl"

if [ "$status" -eq 0 ]; then
  echo "✓ Lean style OK (${#files[@]} files)"
fi
exit $status
