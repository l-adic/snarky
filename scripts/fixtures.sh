#!/usr/bin/env bash
#
# Pack/unpack the circuit-diff OCaml fixtures.
#
# ALL fixtures under packages/pickles-circuit-diffs/circuits/ocaml are
# committed in gzipped form only (~13MB vs ~325MB raw — circuit JSON is
# highly repetitive: ~26x overall, up to ~40x for the chunks_* dumps).
# The plain .json/.jsonl are gitignored local working copies. The OCaml
# dump writers and the PureScript test reader are both unchanged: they
# only ever see plain files. Compression is purely a packaging step.
#
#   unpack : gunzip every committed *.gz -> plain file, but ONLY when
#            the plain file is missing or OLDER than the .gz. Idempotent,
#            a no-op on warm runs, and it never clobbers a fresher local
#            regen. Wired as a prerequisite of
#            `make test-pickles-circuit-diffs`.
#   pack   : gzip every plain fixture -> *.gz (reproducible: `-n` drops
#            the name/mtime header so identical content yields identical
#            bytes — the .gz only changes when the fixture truly does).
#            Run after regenerating fixtures, then `git add` the *.gz
#            and commit (the .gz delta lands in the same PR as the
#            generator change — staleness is visible in review).
#
# Usage: scripts/fixtures.sh {pack|unpack}

set -euo pipefail
shopt -s nullglob

DIR="packages/pickles-circuit-diffs/circuits/ocaml"

case "${1:-}" in
  pack)
    n=0
    for f in "$DIR"/*.json "$DIR"/*.jsonl; do
      gzip -9 -n -k -f "$f"
      n=$((n + 1))
    done
    echo "Packed $n fixture(s) -> *.gz. Now: git add $DIR/*.gz && commit."
    ;;
  unpack)
    n=0
    skipped=0
    for gz in "$DIR"/*.json.gz "$DIR"/*.jsonl.gz; do
      plain="${gz%.gz}"
      if [ -e "$plain" ] && [ ! "$gz" -nt "$plain" ]; then
        skipped=$((skipped + 1))
        continue
      fi
      gunzip -c "$gz" >"$plain"
      n=$((n + 1))
    done
    echo "Unpacked $n fixture(s); $skipped already current."
    ;;
  *)
    echo "Usage: scripts/fixtures.sh {pack|unpack}" >&2
    exit 1
    ;;
esac
