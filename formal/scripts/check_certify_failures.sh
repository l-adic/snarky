#!/usr/bin/env bash
# Regression for `certify-application`: an application's own failures are located at the
# application and its stage, an intact independent application beside it is still certified,
# and the exit status is nonzero. The selection is NoRecursionReturn beside HeterogeneousPrevs,
# NoRecursionReturn's files damaged one way per run: a malformed circuit dump, a malformed
# sidecar, a missing circuit dump.
#
# Usage: PICKLES_DUMP_DIR=<dumps> scripts/check_certify_failures.sh   (from formal/, after
# `lake build certify-application`)
set -euo pipefail
cd "$(dirname "$0")/.."
dumps="${PICKLES_DUMP_DIR:?PICKLES_DUMP_DIR is not set}"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cp -R "$dumps/NoRecursionReturn" "$dumps/HeterogeneousPrevs" "$work/"
restore() { rm -rf "$work/NoRecursionReturn"; cp -R "$dumps/NoRecursionReturn" "$work/"; }

expect() { # $1 = the damage, $2 = the located failure line's prefix
  local out
  if out="$(PICKLES_DUMP_DIR="$work" APPS=NoRecursionReturn,HeterogeneousPrevs \
      lake exe certify-application 2>&1)"; then
    echo "✗ $1: exit status 0"; echo "$out" | tail -5; exit 1
  fi
  grep -q "^$2" <<<"$out" || { echo "✗ $1: no line starting with '$2'"; echo "$out" | tail -8; exit 1; }
  grep -q "^✓ HeterogeneousPrevs/child: certified" <<<"$out" \
    && grep -q "^✓ HeterogeneousPrevs/application: certified" <<<"$out" \
    || { echo "✗ $1: the intact application was not certified"; echo "$out" | tail -8; exit 1; }
  grep -q "^✗ 1 of 3 application(s) failed: NoRecursionReturn/nrr" <<<"$out" \
    || { echo "✗ $1: the summary does not name the one failure"; echo "$out" | tail -3; exit 1; }
  echo "✓ $1: located at '$2', the intact application certified, exit status nonzero"
}

printf '{"branches": [' > "$work/NoRecursionReturn/nrr.json"
expect "a malformed circuit dump" "✗ NoRecursionReturn/nrr: dump:"
restore
printf '{' > "$work/NoRecursionReturn/shapes/nrr.json"
expect "a malformed sidecar" "✗ NoRecursionReturn/nrr: sidecar:"
restore
rm "$work/NoRecursionReturn/nrr.json"
expect "a missing circuit dump" "✗ NoRecursionReturn/nrr: missing required fixture:"
echo "── certify-application failure regressions OK ──"
