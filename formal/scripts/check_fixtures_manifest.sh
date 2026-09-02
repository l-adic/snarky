#!/usr/bin/env bash
# Fixture-provenance gate (external-audit A-7): every committed fixture is pinned by
# sha256 to a manifest that also records the proof-systems revision it was regenerated
# from. CI checks out without submodules and never regenerates, so without this pin one
# PR could move the model and its fixtures together ("fixture-side accommodation") with
# nothing noticing. The audit closed that gap once by regenerating byte-identical
# artifacts from the pinned checkout; this gate keeps the pin explicit between
# regenerations.
#
#   check_fixtures_manifest.sh            check hashes against the manifest
#   check_fixtures_manifest.sh --regen    re-pin (run after a deliberate regeneration
#                                         from tools/fixture-dump; record the
#                                         proof-systems bump in the commit message)
set -euo pipefail
cd "$(dirname "$0")/.."

manifest="scripts/fixtures.sha256"
dirs=(kimchi/fixtures poseidon/fixtures bulletproof-pcs/fixtures pickles/fixtures)

list_files() {
  # committed fixtures only: the *_debug.json sidecars are gitignored dev artifacts
  { for d in "${dirs[@]}"; do
      find "$d" -maxdepth 1 -type f \( -name '*.json' -o -name '.gitignore' \) \
        ! -name '*_debug.json'
    done; } | LC_ALL=C sort
}

rev() {
  git -C ../mina rev-parse HEAD 2>/dev/null || echo "UNKNOWN (mina submodule absent)"
}

if [[ "${1:-}" == "--regen" ]]; then
  { echo "# Fixture manifest: sha256 of every committed fixture, regenerated from"
    echo "# tools/fixture-dump against the mina submodule at the revision below"
    echo "# (pickles/fixtures excepted: those come from packages/pickles-codegen's"
    echo "# gen-linearization, which reads the same submodule)."
    echo "# Re-pin with scripts/check_fixtures_manifest.sh --regen after a deliberate"
    echo "# regeneration; a hash mismatch otherwise means a fixture was edited by hand."
    echo "# mina-submodule: $(rev)"
    list_files | xargs sha256sum; } > "$manifest"
  echo "re-pinned $manifest at mina $(rev)"
  exit 0
fi

if [[ ! -f "$manifest" ]]; then
  echo "✗ fixture manifest missing: $manifest (generate with --regen)"; exit 1
fi

# Hash check (the mina-submodule line is provenance metadata, not re-checked here:
# CI has no submodule; regeneration-time identity is the dump workflow's assertion).
if ! grep -v '^#' "$manifest" | sha256sum -c --quiet -; then
  echo "✗ fixture hash mismatch — a committed fixture differs from the pinned manifest."
  echo "  If this regeneration was deliberate, re-pin with --regen and record the"
  echo "  proof-systems revision in the commit message."
  exit 1
fi

# Completeness: every committed fixture must be IN the manifest (a new unpinned file
# is exactly the accommodation vector this gate exists for).
missing=$(comm -13 <(grep -v '^#' "$manifest" | awk '{print $2}' | LC_ALL=C sort) \
                   <(list_files | LC_ALL=C sort))
if [[ -n "$missing" ]]; then
  echo "✗ fixtures not in the manifest:"; echo "$missing"; exit 1
fi

echo "✓ all committed fixtures match the pinned manifest \
($(grep -cv '^#' "$manifest") files, mina $(grep '^# mina-submodule' "$manifest" | awk '{print $3}' | cut -c1-12))"
