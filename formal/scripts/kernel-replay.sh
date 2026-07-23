#!/usr/bin/env bash
# Kernel-replay every library module through lean4checker (leanprover/lean4checker).
#
# `lake build` already kernel-checks each declaration as it is elaborated, but the
# elaborator and metaprograms run first and CAN manipulate the environment ("environment
# hacking"); the axiom gates (`scripts/check_axioms.lean`) also run inside that same
# environment. lean4checker closes the loop underneath them: it re-reads the .olean
# files and replays every declaration through the kernel alone, detecting any
# environment tampering. See https://lean-lang.org/doc/reference/latest/ValidatingProofs/.
#
# Upstream has no tag for our toolchain (tags stop at v4.29.0-rc8), so we pin a commit
# and build it AGAINST our own pinned toolchain — the tool is small and its API surface
# is stable; bump REV alongside toolchain bumps if the build ever breaks.
#
# scripts/prune-stale-oleans.sh runs first: lean4checker resolves modules by name-prefix
# over the LEAN_PATH oleans, so stale artifacts of deleted/renamed modules would be
# replayed as if they were part of the library (and can false-fail after refactors).
#
# Usage: scripts/kernel-replay.sh          (requires a prior `lake build`)
#   LEAN4CHECKER_WORKERS=N to override the worker count (default 2 — each worker loads
#   a full Mathlib-sized import environment, so keep this small on CI runners).
set -euo pipefail
cd "$(dirname "$0")/.."

REV=91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709
dir=.lake/lean4checker
stamp="$REV-$(cat lean-toolchain)"

if [ ! -x "$dir/.lake/build/bin/lean4checker" ] \
    || [ "$(cat "$dir/.rev" 2>/dev/null || true)" != "$stamp" ]; then
  rm -rf "$dir"
  git clone --quiet https://github.com/leanprover/lean4checker.git "$dir"
  git -C "$dir" checkout --quiet "$REV"
  cp lean-toolchain "$dir/lean-toolchain"
  (cd "$dir" && lake build)
  echo "$stamp" > "$dir/.rev"
fi

scripts/prune-stale-oleans.sh

# The workspace library roots — keep in sync with lintDriverArgs in lakefile.toml.
# (The kimchi-demo executable root `Main` is not replayed: CI builds only the
# libraries, and the demo is not part of the trust surface.)
lake env "$dir/.lake/build/bin/lean4checker" \
  "--num-workers=${LEAN4CHECKER_WORKERS:-2}" \
  Kimchi KimchiFixture Snarky Pasta Poseidon FixtureKit Bulletproof BulletproofFixture
echo "✓ kernel replay clean (lean4checker $REV)"
