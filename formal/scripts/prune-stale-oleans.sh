#!/usr/bin/env bash
# Prune build artifacts for Lean modules whose SOURCE no longer exists.
#
# `lake build` never garbage-collects: a module that is deleted or renamed leaves its
# `.olean`/`.ilean` behind in the package build directory. Those stale artifacts stay on
# `lake env`'s LEAN_PATH, where they (a) shadow the current tree after branch switches
# (stale-olean import errors) and (b) get picked up by prefix-matching tools — the
# lean4checker kernel-replay gate resolves its module list from the search path, so a
# stale olean would be replayed as if it were part of the library. CI runs this before
# the lean4checker step; run it locally after deleting/renaming modules or switching
# branches.
#
# Usage: scripts/prune-stale-oleans.sh   (from anywhere; operates on this workspace)
set -euo pipefail
cd "$(dirname "$0")/.."

pruned=0
for pkg in pasta poseidon bulletproof-pcs kimchi snarky .; do
  lib="$pkg/.lake/build/lib/lean"
  [ -d "$lib" ] || continue
  while IFS= read -r o; do
    rel="${o#"$lib"/}"
    if [ ! -f "$pkg/${rel%.olean}.lean" ]; then
      echo "pruning stale module: ${pkg}: ${rel%.olean}"
      base="${o%.olean}"
      rm -f "$base.olean" "$base.ilean" "$base.olean.hash" "$base.ilean.hash" "$base.trace"
      irbase="$pkg/.lake/build/ir/${rel%.olean}"
      rm -f "$irbase.c" "$irbase.c.o" "$irbase.c.hash" "$irbase.c.o.export" \
        "$irbase.c.o.noexport" "$irbase.trace"
      pruned=$((pruned + 1))
    fi
  done < <(find "$lib" -name '*.olean')
done
echo "pruned $pruned stale module(s)"
