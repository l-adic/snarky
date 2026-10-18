#!/usr/bin/env bash
# Dead-code GATE (nonzero exit on failure): every authored declaration must be reachable from
# the CI drivers' oleans, the snarky and pickles axiom gates' lists and the remaining packages'
# roots.txt manifests, and every script-surface root must appear in a scripts/ file. Driver:
# scripts/deadcode.lean. Requires a prior workspace build — that is `make lean-build`, or from
# here the explicit target list
# `lake build Kimchi Snarky Pasta Poseidon FixtureKit Bulletproof BulletproofFixture Pickles`.
# Bare `lake build` from this directory reports 0 jobs (the root package is a pure aggregator
# with no library and no defaultTargets) and would leave stale modules in place. The CI drivers
# are built here (a no-op once built): the gate reads their oleans.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build check-cs check-tags check-slot-chunks check-application-layouts \
  check-application-manifest check-rule-replay check-application-inputs \
  check-application-indices certify-application check-application-keys check-terminal \
  @pickles/check-sg-ok
lake env lean scripts/deadcode.lean
