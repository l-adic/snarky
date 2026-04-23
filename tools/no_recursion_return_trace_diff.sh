#!/usr/bin/env bash
#
# Runs both sides of the No_recursion_return trace reproduction loop and diffs.
#
# - Builds + runs `mina/.../dump_no_recursion_return.exe` (OCaml) inside the
#   nix shell with KIMCHI_STUBS_STATIC_LIB pointing at a locally-built static
#   lib so the deterministic-RNG patch is picked up.
# - Builds + runs `Test.Pickles.Main` (PureScript) with the same seed and
#   trace-file env vars. The PS side's `Test.Pickles.Prove.NoRecursionReturn`
#   is the module that emits the matching trace.
# - Diffs the two trace files with line numbers.
#
# Output:
#   /tmp/no_recursion_return_ocaml.trace
#   /tmp/no_recursion_return_purescript.trace
#   /tmp/no_recursion_return_diff.txt   (also printed to stdout)
#
# Exit code:
#   0 if the trace files are byte-identical
#   1 if they differ
#   >1 if a build/run step failed
#
# Requirements:
#   - The local kimchi-stubs static lib must be built and staged at
#     /tmp/local_kimchi_stubs/lib/libkimchi_stubs.a. Build:
#       cd mina/src/lib/crypto/proof-systems && \
#         ~/.cargo/bin/cargo build -p kimchi-stubs --release && \
#         mkdir -p /tmp/local_kimchi_stubs/lib && \
#         cp target/release/libkimchi_stubs.a /tmp/local_kimchi_stubs/lib/
#
# Seed:
#   Pinned at 42 (same as simple_chain).

set -e

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OCAML_TRACE=/tmp/no_recursion_return_ocaml.trace
PS_TRACE=/tmp/no_recursion_return_purescript.trace
DIFF_OUT=/tmp/no_recursion_return_diff.txt
SEED=42

KIMCHI_STUBS_LOCAL=/tmp/local_kimchi_stubs

if [ ! -f "$KIMCHI_STUBS_LOCAL/lib/libkimchi_stubs.a" ]; then
  echo "FATAL: $KIMCHI_STUBS_LOCAL/lib/libkimchi_stubs.a missing." >&2
  echo "Build it with:" >&2
  echo "  cd $REPO_ROOT/mina/src/lib/crypto/proof-systems && \\" >&2
  echo "    ~/.cargo/bin/cargo build -p kimchi-stubs --release && \\" >&2
  echo "    mkdir -p $KIMCHI_STUBS_LOCAL/lib && \\" >&2
  echo "    cp target/release/libkimchi_stubs.a $KIMCHI_STUBS_LOCAL/lib/" >&2
  exit 2
fi

echo "==> Running OCaml dump_no_recursion_return.exe (seed=$SEED)..."
rm -f "$OCAML_TRACE"
nix develop mina#default -c bash -c "
  export KIMCHI_STUBS_STATIC_LIB=$KIMCHI_STUBS_LOCAL
  export KIMCHI_DETERMINISTIC_SEED=$SEED
  export PICKLES_TRACE_FILE=$OCAML_TRACE
  cd $REPO_ROOT/mina && \
    dune build src/lib/crypto/pickles/dump_no_recursion_return/dump_no_recursion_return.exe && \
    dune exec src/lib/crypto/pickles/dump_no_recursion_return/dump_no_recursion_return.exe
" >/dev/null 2>&1

if [ ! -f "$OCAML_TRACE" ]; then
  echo "FATAL: OCaml dump_no_recursion_return.exe did not produce a trace file." >&2
  exit 3
fi

OCAML_LINES=$(wc -l <"$OCAML_TRACE")
echo "  OCaml trace: $OCAML_LINES lines -> $OCAML_TRACE"

echo "==> Running PureScript Test.Pickles.Main (seed=$SEED)..."
rm -f "$PS_TRACE"
export PATH=$HOME/.nvm/versions/node/v22.22.2/bin:$PATH
cd "$REPO_ROOT"
KIMCHI_DETERMINISTIC_SEED=$SEED PICKLES_TRACE_FILE=$PS_TRACE \
  npx spago test -p pickles -- --example "NoRecursionReturn" >/dev/null 2>&1

if [ ! -f "$PS_TRACE" ]; then
  echo "FATAL: PureScript No_recursion_return test did not produce a trace file." >&2
  exit 4
fi

PS_LINES=$(wc -l <"$PS_TRACE")
echo "  PureScript trace: $PS_LINES lines -> $PS_TRACE"

echo "==> Diffing..."
diff -u --label OCaml "$OCAML_TRACE" --label PureScript "$PS_TRACE" >"$DIFF_OUT" && DIFF_EXIT=0 || DIFF_EXIT=$?

if [ "$DIFF_EXIT" = 0 ]; then
  echo "  MATCH: traces byte-identical ($OCAML_LINES lines)."
  exit 0
fi

echo "  DIVERGENCE detected:"
echo
head -60 "$DIFF_OUT"
echo
echo "Full diff at: $DIFF_OUT"
exit 1
