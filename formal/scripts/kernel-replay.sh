#!/usr/bin/env bash
# Kernel-replay every library module through the toolchain's leanchecker.
#
# `lake build` already kernel-checks each declaration as it is elaborated, but the
# elaborator and metaprograms run first and CAN manipulate the environment ("environment
# hacking"); the axiom gates (`scripts/check_axioms.lean`) also run inside that same
# environment. leanchecker closes the loop underneath them: it re-reads the .olean
# files and replays every declaration through the kernel alone, detecting any
# environment tampering. See https://lean-lang.org/doc/reference/latest/ValidatingProofs/.
#
# leanchecker is lean4checker upstreamed into Lean: every toolchain since v4.28.0 ships it,
# and `lake env` puts the toolchain's bin directory first on PATH, so the checker is the
# pinned toolchain's own and nothing is built.
#
# scripts/prune-stale-oleans.sh runs first: leanchecker resolves modules by name-prefix
# over the LEAN_PATH oleans, so stale artifacts of deleted/renamed modules would be
# replayed as if they were part of the library (and can false-fail after refactors).
#
# Usage: scripts/kernel-replay.sh          (requires a prior workspace build: `make lean-build`,
#   or from formal/ the explicit target list
#   `lake build Kimchi Snarky Pasta Poseidon FixtureKit Bulletproof BulletproofFixture Pickles` — bare
#   `lake build` there reports 0 jobs, the root package being a pure aggregator, so the oleans
#   replayed below would be whatever is already on disk)
#   LEAN_NUM_THREADS=N to override the replay parallelism (default 2 — leanchecker replays
#   each module in a task on the runtime's thread pool, and each task loads a full
#   Mathlib-sized import environment, so keep this small on CI runners).
set -euo pipefail
cd "$(dirname "$0")/.."

scripts/prune-stale-oleans.sh

# The workspace library roots — keep in sync with lintDriverArgs in lakefile.toml.
LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" lake env leanchecker \
  Kimchi KimchiFixture Snarky Pasta Poseidon FixtureKit Bulletproof BulletproofFixture \
  Pickles
echo "✓ kernel replay clean (leanchecker, $(cat lean-toolchain))"
