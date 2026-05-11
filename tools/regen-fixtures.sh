#!/usr/bin/env bash
#
# Regenerate the committed OCaml-side test fixtures under
# `packages/pickles/test/fixtures/`.
#
# These fixtures drive the PS byte-identity tests:
#   - `*_base_case.trace`         — `[LABEL] VALUE` lines emitted by
#                                    `Pickles_trace` during an OCaml
#                                    prove-flow. Compared line-by-line
#                                    against the PS-side trace.
#   - `witness/ocaml_{step,wrap}_b{0,1}.txt` — 15-column kimchi
#                                    witness matrices for Simple_chain's
#                                    b0/b1 proofs, dumped by the patched
#                                    `ProverProof::create_recursive` via
#                                    `KIMCHI_WITNESS_DUMP`.
#
# CI cannot rebuild these (no nix / no mina build environment), so they
# live committed in-tree. Run this script locally after any OCaml-side
# change that alters what the dumpers emit; diff the result to review.
#
# Usage:
#   tools/regen-fixtures.sh              # regenerate all
#   tools/regen-fixtures.sh trace        # only the .trace files
#   tools/regen-fixtures.sh witness      # only the witness matrices
#   tools/regen-fixtures.sh nrr          # only No_recursion_return
#   tools/regen-fixtures.sh simple       # only Simple_chain
#   tools/regen-fixtures.sh tree         # only Tree_proof_return
#
# Environment / prerequisites:
#   - Nix shell at `git+file:///home/martyall/code/o1/mina?submodules=1`
#     (builds OCaml dumpers).
#   - `~/.cargo/bin/cargo` to build the kimchi-stubs static lib with the
#     deterministic-RNG patch:
#
#       cd mina/src/lib/crypto/proof-systems && \
#         ~/.cargo/bin/cargo build -p kimchi-stubs --release && \
#         mkdir -p /tmp/local_kimchi_stubs/lib && \
#         cp target/release/libkimchi_stubs.a /tmp/local_kimchi_stubs/lib/
#
#   - Seed is pinned at 42 (matches the PS-side test setup).
#
# Exit:
#   0  — all requested fixtures regenerated successfully
#   >0 — one of the dumpers failed (stderr shows which)

set -e

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
FIXTURE_DIR="$REPO_ROOT/packages/pickles/test/fixtures"
WITNESS_DIR="$FIXTURE_DIR/witness"
KIMCHI_STUBS_LOCAL=/tmp/local_kimchi_stubs
SEED=42
NIX_FLAKE='git+file:///home/martyall/code/o1/mina?submodules=1'

if [ ! -f "$KIMCHI_STUBS_LOCAL/lib/libkimchi_stubs.a" ]; then
  echo "FATAL: $KIMCHI_STUBS_LOCAL/lib/libkimchi_stubs.a missing." >&2
  echo "Build it with:" >&2
  echo "  cd $REPO_ROOT/mina/src/lib/crypto/proof-systems && \\" >&2
  echo "    ~/.cargo/bin/cargo build -p kimchi-stubs --release && \\" >&2
  echo "    mkdir -p $KIMCHI_STUBS_LOCAL/lib && \\" >&2
  echo "    cp target/release/libkimchi_stubs.a $KIMCHI_STUBS_LOCAL/lib/" >&2
  exit 2
fi

mode="${1:-all}"

want_nrr=false
want_simple=false
want_tree=false
want_witness=false

case "$mode" in
  all)
    want_nrr=true; want_simple=true; want_tree=true; want_witness=true ;;
  trace)
    want_nrr=true; want_simple=true; want_tree=true ;;
  witness)
    want_witness=true ;;
  nrr)
    want_nrr=true ;;
  simple)
    want_simple=true; want_witness=true ;;
  tree)
    want_tree=true ;;
  *)
    echo "Unknown mode: $mode" >&2
    echo "Usage: $0 [all|trace|witness|nrr|simple|tree]" >&2
    exit 1 ;;
esac

run_dumper() {
  local exe_path="$1"
  local env_setup="$2"
  echo "==> Running $exe_path" >&2
  nix develop "$NIX_FLAKE" -c bash -c "
    export KIMCHI_STUBS_STATIC_LIB=$KIMCHI_STUBS_LOCAL
    export KIMCHI_DETERMINISTIC_SEED=$SEED
    $env_setup
    cd $REPO_ROOT/mina && \
      dune build $exe_path && \
      dune exec $exe_path
  " >/dev/null
}

if $want_nrr; then
  OUT="$FIXTURE_DIR/no_recursion_return_base_case.trace"
  # NRR has 2 kimchi proves per run (counters 0 = step_b0, 1 = wrap_b0).
  rm -f /tmp/regen_nrr_*.witness
  run_dumper "src/lib/crypto/pickles/dump_no_recursion_return/dump_no_recursion_return.exe" \
    "export PICKLES_TRACE_FILE=$OUT
     export KIMCHI_WITNESS_DUMP=/tmp/regen_nrr_%c.witness
     export KIMCHI_WITNESS_DUMP_SIDE=oc"
  echo "  -> $OUT ($(wc -l <"$OUT") lines)" >&2

  WITNESS_NRR_DIR="$FIXTURE_DIR/witness_nrr"
  mkdir -p "$WITNESS_NRR_DIR"
  for src in 0:step_b0 1:wrap_b0; do
    counter="${src%%:*}"
    name="${src##*:}"
    dst="$WITNESS_NRR_DIR/ocaml_${name}.txt"
    if [ ! -f "/tmp/regen_nrr_${counter}.witness" ]; then
      echo "FATAL: dump_no_recursion_return did not emit /tmp/regen_nrr_${counter}.witness" >&2
      exit 3
    fi
    cp "/tmp/regen_nrr_${counter}.witness" "$dst"
    echo "  -> $dst ($(wc -l <"$dst") lines)" >&2
  done
fi

if $want_simple; then
  OUT="$FIXTURE_DIR/simple_chain_base_case.trace"
  WITNESS_ENV=""
  if $want_witness; then
    # dump_simple_chain emits counters 0..9 (b0..b4, step + wrap each).
    # We only commit b0/b1.
    WITNESS_ENV="export KIMCHI_WITNESS_DUMP=/tmp/regen_sc_%c.witness"
    rm -f /tmp/regen_sc_*.witness
  fi
  run_dumper "src/lib/crypto/pickles/dump_simple_chain/dump_simple_chain.exe" \
    "export PICKLES_TRACE_FILE=$OUT
     $WITNESS_ENV"
  echo "  -> $OUT ($(wc -l <"$OUT") lines)" >&2

  if $want_witness; then
    mkdir -p "$WITNESS_DIR"
    for src in 0:step_b0 1:wrap_b0 2:step_b1 3:wrap_b1; do
      counter="${src%%:*}"
      name="${src##*:}"
      dst="$WITNESS_DIR/ocaml_${name}.txt"
      if [ ! -f "/tmp/regen_sc_${counter}.witness" ]; then
        echo "FATAL: dump_simple_chain did not emit /tmp/regen_sc_${counter}.witness" >&2
        exit 3
      fi
      cp "/tmp/regen_sc_${counter}.witness" "$dst"
      echo "  -> $dst ($(wc -l <"$dst") lines)" >&2
    done
  fi
fi

if $want_tree; then
  OUT="$FIXTURE_DIR/tree_proof_return_base_case.trace"
  run_dumper "src/lib/crypto/pickles/dump_tree_proof_return/dump_tree_proof_return.exe" \
    "export PICKLES_TRACE_FILE=$OUT"
  echo "  -> $OUT ($(wc -l <"$OUT") lines)" >&2
fi

echo
echo "==> Done. Review with:" >&2
echo "    git diff --stat $FIXTURE_DIR" >&2
echo "    git diff $FIXTURE_DIR" >&2
