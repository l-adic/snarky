#!/usr/bin/env bash
# Regression for `certify-application`, one run: an application's own failures are located at
# the application and its stage, its dependents are blocked by it, an intact independent
# application beside them is certified, and the exit status is nonzero. The selection damages
# three applications at the load or certification stage and leaves NoRecursionReturn intact,
# so the run reconstructs HeterogeneousPrevs and NoRecursionReturn and nothing else:
#   TwoPhaseChain: a malformed sidecar, the key unknown, so an import of it matches nothing;
#   RecurseOverChunks: chunks2's circuit dump missing, the key known from its sidecar, so
#     recurse is blocked by it before any reconstruction;
#   HeterogeneousPrevs: child's circuit dump malformed, failing at certification after
#     reconstruction, so application is blocked by that certification failure.
#
# Usage: PICKLES_DUMP_DIR=<dumps> scripts/check_certify_failures.sh   (from formal/, after
# `lake build certify-application`)
set -euo pipefail
cd "$(dirname "$0")/.."
dumps="${PICKLES_DUMP_DIR:?PICKLES_DUMP_DIR is not set}"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
for app in NoRecursionReturn TwoPhaseChain RecurseOverChunks HeterogeneousPrevs; do
  cp -R "$dumps/$app" "$work/"
done
printf '{' > "$work/TwoPhaseChain/shapes/two_phase_chain.json"
rm "$work/RecurseOverChunks/chunks2.json"
printf '{"branches": [' > "$work/HeterogeneousPrevs/child.json"

if out="$(PICKLES_DUMP_DIR="$work" \
    APPS=NoRecursionReturn,TwoPhaseChain,RecurseOverChunks,HeterogeneousPrevs \
    lake exe certify-application 2>&1)"; then
  echo "✗ exit status 0 with three damaged applications"; echo "$out" | tail -8; exit 1
fi
expect() { # $1 = the expected line's prefix
  grep -q "^$1" <<<"$out" || { echo "✗ no line starting with '$1'"; echo "$out" | tail -12; exit 1; }
  echo "✓ $1"
}
expect "✗ TwoPhaseChain/two_phase_chain: sidecar:"
expect "✗ RecurseOverChunks/chunks2: missing required fixture:"
expect "✗ RecurseOverChunks/recurse: blocked by the failure of RecurseOverChunks/chunks2"
expect "✗ HeterogeneousPrevs/child: dump:"
expect "✗ HeterogeneousPrevs/application: blocked by certification failure of HeterogeneousPrevs/child"
expect "✓ NoRecursionReturn/nrr: certified"
expect "✗ 5 of 6 application(s) failed:"
echo "── certify-application failure regressions OK ──"
