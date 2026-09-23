#!/usr/bin/env bash
# The comment gate: scripts/check_comments.lean over the built libraries.
#
#   scripts/check-comments.sh              # counts against the ratchet
#   COMMENT_GATE_LIST=1 scripts/check-comments.sh   # every violation, by declaration
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2   # -> formal/
lake env lean scripts/check_comments.lean 2>&1 \
  | grep -vE "deprecated|^Note:|^$|Dot notation|^  String" \
  | sed '/^$/d'
exit "${PIPESTATUS[0]}"
