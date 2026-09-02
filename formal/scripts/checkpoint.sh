#!/usr/bin/env bash
# Run every gate that must be green before a change is committed.
#
# One definition of "green", ordered cheapest-first so a failure surfaces before the expensive
# gates run. CI (.github/workflows/lean.yml) runs the same set plus the fixture drivers and the
# kernel replay; this is the local pre-commit pass.
#
# Usage:  formal/scripts/checkpoint.sh            # everything
#         formal/scripts/checkpoint.sh --fast     # skip lake lint and the fixture gate
set -uo pipefail
cd "$(dirname "$0")/.."

FAST=0
[[ "${1:-}" == "--fast" ]] && FAST=1

fail=0
run() {
  local name="$1"; shift
  printf '\n\033[1m── %s\033[0m\n' "$name"
  if "$@"; then
    printf '\033[32m   ok\033[0m\n'
  else
    printf '\033[31m   FAILED: %s\033[0m\n' "$name"
    fail=1
  fi
}

# Cheap and catches the most common refactor slips.
run "style (<=100 cols, no trailing ws/tabs, final newline)" bash scripts/check-style.sh
run "sorry census" bash scripts/check_sorry_census.sh
# Builds. The shared workspace means one Mathlib for every package.
run "build" lake build Kimchi Snarky Pasta Poseidon FixtureKit Bulletproof BulletproofFixture Schnorr

# Trust boundary, per package.
run "axioms (bulletproof-pcs)" bash bulletproof-pcs/scripts/check_axioms.sh
run "axioms (kimchi)" bash kimchi/scripts/check_axioms.sh
run "axioms (pasta)" bash pasta/scripts/check_axioms.sh
run "axioms (poseidon)" bash poseidon/scripts/check_axioms.sh
run "axioms (snarky)" bash snarky/scripts/check_axioms.sh
run "axioms (schnorr)" bash schnorr/scripts/check_axioms.sh

# Reachability from the packages' roots.txt: dead must be zero.
run "dead code" bash scripts/deadcode.sh

if [[ $FAST -eq 0 ]]; then
  run "IPA fixture" bash bulletproof-pcs/scripts/check_ipa_fixture.sh
  # De-privatizing a declaration without a docstring trips docBlame, and it is a CI gate.
  # One `lake lint` over all eight roots accumulates every import environment in one process and
  # gets OOM-killed (see the CAVEAT in lakefile.toml) — run one linter process per root, as CI does.
  run "env linters (one process per root)" bash -c '
    for m in Kimchi KimchiFixture Snarky Pasta Poseidon FixtureKit Bulletproof BulletproofFixture \
             Schnorr; do
      lake exe runLinter "$m" || exit 1
    done'
fi

printf '\n'
if [[ $fail -ne 0 ]]; then
  printf '\033[31m✗ checkpoint NOT clean — do not commit\033[0m\n'
  exit 1
fi
printf '\033[32m✓ checkpoint clean'
[[ $FAST -eq 1 ]] && printf ' (--fast: lake lint and the fixture gate were skipped)'
printf '\033[0m\n'
