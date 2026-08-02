#!/usr/bin/env bash
# Dead-code GATE (nonzero exit on failure): every authored declaration must be reachable from
# the union of the packages' roots.txt manifests, and every script-surface root must appear in
# a scripts/ file. Driver: scripts/deadcode.lean. Requires a prior workspace build — that is
# `make lean-build`, or from here the explicit target list
# `lake build Kimchi Snarky Pasta Poseidon FixtureKit Bulletproof BulletproofFixture`. Bare
# `lake build` from this directory reports 0 jobs (the root package is a pure aggregator with
# no library and no defaultTargets) and would leave stale modules in place.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/deadcode.lean
