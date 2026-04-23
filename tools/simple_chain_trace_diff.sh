#!/usr/bin/env bash
#
# Runs both sides of the Simple_chain trace reproduction loop and diffs.
#
# - Builds + runs `mina/.../dump_simple_chain.exe` (OCaml) inside the nix
#   shell with KIMCHI_STUBS_STATIC_LIB pointing at a locally-built static
#   lib so the deterministic-RNG patch is picked up.
# - Builds + runs `Test.Pickles.Main` (PureScript) with the same seed and
#   trace-file env vars.
# - Diffs the two trace files with line numbers.
#
# Output:
#   /tmp/simple_chain_ocaml.trace
#   /tmp/simple_chain_purescript.trace
#   /tmp/simple_chain_diff.txt   (also printed to stdout)
#
# Exit code:
#   0 if the trace files are byte-identical
#   1 if they differ
#   >1 if a build/run step failed
#
# Requirements:
#   - The local kimchi-stubs static lib must be built and staged at
#     /tmp/local_kimchi_stubs/lib/libkimchi_stubs.a. See README in
#     packages/pickles/test/fixtures/ for how (or run
#     `~/.cargo/bin/cargo build -p kimchi-stubs --release` from
#     `mina/src/lib/crypto/proof-systems/`, then copy the lib).
#   - nix shell at git+file:///home/martyall/code/o1/mina?submodules=1
#     for the OCaml side.
#   - npm/spago for the PureScript side (uses ~/.nvm node 22).
#
# Seed:
#   Pinned at 42. Both sides use ChaCha20Rng::seed_from_u64(42) inside
#   their respective wrappers around kimchi prover create.

set -e

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OCAML_TRACE=/tmp/simple_chain_ocaml.trace
PS_TRACE=/tmp/simple_chain_purescript.trace
DIFF_OUT=/tmp/simple_chain_diff.txt
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

echo "==> Running OCaml dump_simple_chain.exe (seed=$SEED)..."
rm -f "$OCAML_TRACE"
nix develop git+file:///home/martyall/code/o1/mina\?submodules=1 -c bash -c "
  export KIMCHI_STUBS_STATIC_LIB=$KIMCHI_STUBS_LOCAL
  export KIMCHI_DETERMINISTIC_SEED=$SEED
  export PICKLES_TRACE_FILE=$OCAML_TRACE
  cd $REPO_ROOT/mina && \
    dune build src/lib/crypto/pickles/dump_simple_chain/dump_simple_chain.exe && \
    dune exec src/lib/crypto/pickles/dump_simple_chain/dump_simple_chain.exe
" >/dev/null 2>&1

if [ ! -f "$OCAML_TRACE" ]; then
  echo "FATAL: OCaml dump_simple_chain.exe did not produce a trace file." >&2
  exit 3
fi

OCAML_LINES=$(wc -l <"$OCAML_TRACE")
echo "  OCaml trace: $OCAML_LINES lines -> $OCAML_TRACE"

echo "==> Running PureScript Test.Pickles.Main (seed=$SEED)..."
rm -f "$PS_TRACE"
export PATH=$HOME/.nvm/versions/node/v22.22.2/bin:$PATH
cd "$REPO_ROOT"
KIMCHI_DETERMINISTIC_SEED=$SEED PICKLES_TRACE_FILE=$PS_TRACE \
  npx spago test -p pickles >/dev/null 2>&1

if [ ! -f "$PS_TRACE" ]; then
  echo "FATAL: PureScript Test.Pickles.Main did not produce a trace file." >&2
  exit 4
fi

PS_LINES=$(wc -l <"$PS_TRACE")
echo "  PureScript trace: $PS_LINES lines -> $PS_TRACE"

echo "==> Diffing..."
echo
diff -u "$OCAML_TRACE" "$PS_TRACE" | tee "$DIFF_OUT"
DIFF_EXIT=${PIPESTATUS[0]}

if [ "$DIFF_EXIT" -eq 0 ]; then
  echo
  echo "==> TRACES IDENTICAL (Simple_chain base case reproduces OCaml byte-for-byte)"
  exit 0
else
  echo
  echo "==> Traces differ. See $DIFF_OUT"
  echo "    Fix the topmost missing/divergent line in PureScript next."
  exit 1
fi
