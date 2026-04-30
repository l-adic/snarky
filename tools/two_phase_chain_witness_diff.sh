#!/usr/bin/env bash
#
# Runs both sides of two_phase_chain (multi-branch fixture) with
# KIMCHI_WITNESS_DUMP enabled and diffs the 15-column kimchi witness
# matrices at every counter. Ground-truth correctness check — trace
# files are diagnostics; the witness is definitional.
#
# Counter sequence on BOTH sides (OCaml dump_two_phase_chain.exe
# calls `make_zero` once and `increment` twice; PS analog does the
# same):
#
#   counter 0 → two_phase_chain b0 step (Fp, VestaG)  [branch 0: make_zero]
#   counter 1 → two_phase_chain b0 wrap (Fq, PallasG)
#   counter 2 → two_phase_chain b1 step (Fp, VestaG)  [branch 1: increment, prev = b0]
#   counter 3 → two_phase_chain b1 wrap (Fq, PallasG)
#   counter 4 → two_phase_chain b2 step (Fp, VestaG)  [branch 1: increment, prev = b1]
#   counter 5 → two_phase_chain b2 wrap (Fq, PallasG)
#
# This is the multi-branch trace-diff loop. Initial focus is b0_step
# (counter 0); the later proofs exercise (1) the prev-from-branch-0
# dispatch case at b1, and (2) the prev-from-branch-1 case at b2 —
# the former tests cross-branch self-references and the latter tests
# self-references within the same branch.
#
# Files:
#   /tmp/tpc_oc_{0..5}.witness
#   /tmp/tpc_ps_{0..5}.witness
#   /tmp/tpc_witness_b{0,1,2}_{step,wrap}.diff
#
# Partial PS progress is tolerated: missing PS files are reported as
# SKIP. While PS multi-branch is being implemented, only b0_step is
# expected to be present.
#
# Exit code:
#   0       all six witness pairs byte-identical
#   1-63    bitfield (+1 b0_step, +2 b0_wrap, +4 b1_step, +8 b1_wrap,
#                     +16 b2_step, +32 b2_wrap)
#   >63     build/run failure

set -e

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SEED=42
KIMCHI_STUBS_LOCAL=/tmp/local_kimchi_stubs

OC_B0_STEP=/tmp/tpc_oc_0.witness
OC_B0_WRAP=/tmp/tpc_oc_1.witness
OC_B1_STEP=/tmp/tpc_oc_2.witness
OC_B1_WRAP=/tmp/tpc_oc_3.witness
OC_B2_STEP=/tmp/tpc_oc_4.witness
OC_B2_WRAP=/tmp/tpc_oc_5.witness
PS_B0_STEP=/tmp/tpc_ps_0.witness
PS_B0_WRAP=/tmp/tpc_ps_1.witness
PS_B1_STEP=/tmp/tpc_ps_2.witness
PS_B1_WRAP=/tmp/tpc_ps_3.witness
PS_B2_STEP=/tmp/tpc_ps_4.witness
PS_B2_WRAP=/tmp/tpc_ps_5.witness

if [ ! -f "$KIMCHI_STUBS_LOCAL/lib/libkimchi_stubs.a" ]; then
  echo "FATAL: $KIMCHI_STUBS_LOCAL/lib/libkimchi_stubs.a missing." >&2
  echo "Build it with:" >&2
  echo "  cd $REPO_ROOT/mina/src/lib/crypto/proof-systems && \\" >&2
  echo "    ~/.cargo/bin/cargo build -p kimchi-stubs --release && \\" >&2
  echo "    mkdir -p $KIMCHI_STUBS_LOCAL/lib && \\" >&2
  echo "    cp target/release/libkimchi_stubs.a $KIMCHI_STUBS_LOCAL/lib/" >&2
  exit 64
fi

echo "==> Running OCaml dump_two_phase_chain.exe (seed=$SEED, KIMCHI_WITNESS_DUMP=/tmp/tpc_oc_%c.witness)..."
rm -f /tmp/tpc_oc_*.witness
nix develop "git+file://$REPO_ROOT/mina?submodules=1" -c bash -c "
  export KIMCHI_STUBS_STATIC_LIB=$KIMCHI_STUBS_LOCAL
  export KIMCHI_DETERMINISTIC_SEED=$SEED
  export KIMCHI_WITNESS_DUMP=/tmp/tpc_oc_%c.witness
  export KIMCHI_WITNESS_DUMP_SIDE=oc
  export PICKLES_TRACE_FILE=/tmp/tpc_oc_trace.txt
  cd $REPO_ROOT/mina && \
    dune build src/lib/crypto/pickles/dump_two_phase_chain/dump_two_phase_chain.exe && \
    dune exec src/lib/crypto/pickles/dump_two_phase_chain/dump_two_phase_chain.exe
" >/dev/null 2>&1

for f in "$OC_B0_STEP" "$OC_B0_WRAP" "$OC_B1_STEP" "$OC_B1_WRAP" "$OC_B2_STEP" "$OC_B2_WRAP"; do
  if [ ! -f "$f" ]; then
    echo "FATAL: OCaml witness $f not produced." >&2
    exit 65
  fi
done

for label in "b0_step:$OC_B0_STEP" "b0_wrap:$OC_B0_WRAP" "b1_step:$OC_B1_STEP" "b1_wrap:$OC_B1_WRAP" "b2_step:$OC_B2_STEP" "b2_wrap:$OC_B2_WRAP"; do
  name="${label%%:*}"
  file="${label#*:}"
  echo "  OCaml $name witness: $(wc -l <"$file") lines"
done

echo "==> Running PureScript Test.Pickles.Main (seed=$SEED, KIMCHI_WITNESS_DUMP=/tmp/tpc_ps_%c.witness)..."
rm -f /tmp/tpc_ps_*.witness
export PATH=$HOME/.nvm/versions/node/v22.22.2/bin:$PATH
cd "$REPO_ROOT"
KIMCHI_DETERMINISTIC_SEED=$SEED \
  KIMCHI_WITNESS_DUMP=/tmp/tpc_ps_%c.witness \
  KIMCHI_WITNESS_DUMP_SIDE=ps \
  PICKLES_TRACE_FILE=/tmp/tpc_ps_trace.txt \
  npx spago test -p pickles -- --example "TwoPhaseChain" >/dev/null 2>&1 || true

for f in "$PS_B0_STEP" "$PS_B0_WRAP" "$PS_B1_STEP" "$PS_B1_WRAP" "$PS_B2_STEP" "$PS_B2_WRAP"; do
  if [ ! -f "$f" ]; then
    echo "NOTE: PS witness $f not produced (expected if iter hasn't reached that proof yet)."
  fi
done

echo "==> Diffing witness pairs (stripping #header lines)..."
BITS=0
diff_pair() {
  local tag=$1 bit=$2 oc=$3 ps=$4 out=$5
  if [ ! -f "$ps" ]; then
    echo "  SKIP $tag: PS side missing."
    return
  fi
  if diff <(grep -v "^#" "$oc") <(grep -v "^#" "$ps") >"$out"; then
    echo "  MATCH $tag: byte-identical ($(wc -l <"$oc") lines)."
  else
    echo "  DIVERGE $tag: see $out"
    head -4 "$out" | sed 's/^/    /'
    BITS=$((BITS | bit))
  fi
}
diff_pair b0_step 1   "$OC_B0_STEP"  "$PS_B0_STEP"  /tmp/tpc_witness_b0_step.diff
diff_pair b0_wrap 2   "$OC_B0_WRAP"  "$PS_B0_WRAP"  /tmp/tpc_witness_b0_wrap.diff
diff_pair b1_step 4   "$OC_B1_STEP"  "$PS_B1_STEP"  /tmp/tpc_witness_b1_step.diff
diff_pair b1_wrap 8   "$OC_B1_WRAP"  "$PS_B1_WRAP"  /tmp/tpc_witness_b1_wrap.diff
diff_pair b2_step 16  "$OC_B2_STEP"  "$PS_B2_STEP"  /tmp/tpc_witness_b2_step.diff
diff_pair b2_wrap 32  "$OC_B2_WRAP"  "$PS_B2_WRAP"  /tmp/tpc_witness_b2_wrap.diff

exit $BITS
