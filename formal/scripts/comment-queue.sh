#!/usr/bin/env bash
# The comment pass's work queue: the modules that owe the ratchet the most.
#
#   scripts/comment-queue.sh          # ranked modules, with the per-category counts
#   scripts/comment-queue.sh <module> # every violation of one module, for the pass itself
#
# A module's number is its share of scripts/comment-baseline.txt; clearing it is what lets
# that file's counts come down (see .claude/skills/comment-audit).
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2   # -> formal/

raw=$(COMMENT_GATE_LIST=1 lake env lean scripts/check_comments.lean 2>/dev/null)

# a violation line is "    <module-or-path>\t<what>"; the gate reports declarations by module
# and module docstrings by path, so fold the paths into module names
norm() {
  sed -e 's/^ *//' \
      -e 's#^\([a-z-]*\)/\([A-Za-z]*\)/#\2.#' -e 's#^[a-z-]*/##' \
      -e 's#/#.#g' -e 's#\.lean\t#\t#'
}

if [ $# -ge 1 ]; then
  printf '%s\n' "$raw" | awk -F'\t' 'NF > 1' | norm | awk -F'\t' -v m="$1" '$1 == m {print "  " $2}' 
  exit 0
fi

printf '%s\n' "$raw" | awk -F'\t' 'NF > 1' | norm | awk -F'\t' '
  { n[$1]++ }
  END { for (m in n) printf "%4d  %s\n", n[m], m }' | sort -rn
