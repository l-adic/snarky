#!/usr/bin/env bash
#
# Runs both sides of Simple_chain (b0 base case + b1..b4 inductive cases)
# with KIMCHI_WITNESS_DUMP enabled and diffs the 15-column kimchi witness
# matrices at every counter. Ground-truth correctness check — trace files
# are diagnostics; the witness is definitional.
#
# Counter sequence on BOTH sides (OCaml dump_simple_chain.exe calls
# `step` five times — b0, b1, b2, b3, b4; PS analog does the same):
#
#   counter 0 → Simple_chain b0 step (Fp, VestaG)
#   counter 1 → Simple_chain b0 wrap (Fq, PallasG)
#   counter 2 → Simple_chain b1 step (Fp, VestaG)
#   counter 3 → Simple_chain b1 wrap (Fq, PallasG)
#   counter 4 → Simple_chain b2 step (Fp, VestaG)
#   counter 5 → Simple_chain b2 wrap (Fq, PallasG)
#   counter 6 → Simple_chain b3 step (Fp, VestaG)
#   counter 7 → Simple_chain b3 wrap (Fq, PallasG)
#   counter 8 → Simple_chain b4 step (Fp, VestaG)
#   counter 9 → Simple_chain b4 wrap (Fq, PallasG)
#
# Files:
#   /tmp/sc_oc_{0..9}.witness
#   /tmp/sc_ps_{0..9}.witness
#   /tmp/sc_witness_b{0,1,2,3,4}_{step,wrap}.diff
#
# Partial PS progress is tolerated: missing PS files are reported as SKIP.
#
# Exit code:
#   0        all ten witness pairs byte-identical
#   1-1023   bitfield of which pair diverged (+1 b0_step, +2 b0_wrap,
#            +4 b1_step, +8 b1_wrap, +16 b2_step, +32 b2_wrap,
#            +64 b3_step, +128 b3_wrap, +256 b4_step, +512 b4_wrap)
#   >1023    build/run failure

set -e

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SEED=42
KIMCHI_STUBS_LOCAL=/tmp/local_kimchi_stubs

OC_B0_STEP=/tmp/sc_oc_0.witness
OC_B0_WRAP=/tmp/sc_oc_1.witness
OC_B1_STEP=/tmp/sc_oc_2.witness
OC_B1_WRAP=/tmp/sc_oc_3.witness
OC_B2_STEP=/tmp/sc_oc_4.witness
OC_B2_WRAP=/tmp/sc_oc_5.witness
OC_B3_STEP=/tmp/sc_oc_6.witness
OC_B3_WRAP=/tmp/sc_oc_7.witness
OC_B4_STEP=/tmp/sc_oc_8.witness
OC_B4_WRAP=/tmp/sc_oc_9.witness
PS_B0_STEP=/tmp/sc_ps_0.witness
PS_B0_WRAP=/tmp/sc_ps_1.witness
PS_B1_STEP=/tmp/sc_ps_2.witness
PS_B1_WRAP=/tmp/sc_ps_3.witness
PS_B2_STEP=/tmp/sc_ps_4.witness
PS_B2_WRAP=/tmp/sc_ps_5.witness
PS_B3_STEP=/tmp/sc_ps_6.witness
PS_B3_WRAP=/tmp/sc_ps_7.witness
PS_B4_STEP=/tmp/sc_ps_8.witness
PS_B4_WRAP=/tmp/sc_ps_9.witness

if [ ! -f "$KIMCHI_STUBS_LOCAL/lib/libkimchi_stubs.a" ]; then
  echo "FATAL: $KIMCHI_STUBS_LOCAL/lib/libkimchi_stubs.a missing." >&2
  echo "Build it with:" >&2
  echo "  cd $REPO_ROOT/mina/src/lib/crypto/proof-systems && \\" >&2
  echo "    ~/.cargo/bin/cargo build -p kimchi-stubs --release && \\" >&2
  echo "    mkdir -p $KIMCHI_STUBS_LOCAL/lib && \\" >&2
  echo "    cp target/release/libkimchi_stubs.a $KIMCHI_STUBS_LOCAL/lib/" >&2
  exit 16
fi

echo "==> Running OCaml dump_simple_chain.exe (seed=$SEED, KIMCHI_WITNESS_DUMP=/tmp/sc_oc_%c.witness)..."
rm -f /tmp/sc_oc_*.witness
nix develop mina#default -c bash -c "
  export KIMCHI_STUBS_STATIC_LIB=$KIMCHI_STUBS_LOCAL
  export KIMCHI_DETERMINISTIC_SEED=$SEED
  export KIMCHI_WITNESS_DUMP=/tmp/sc_oc_%c.witness
  export KIMCHI_WITNESS_DUMP_SIDE=oc
  cd $REPO_ROOT/mina && \
    dune build src/lib/crypto/pickles/dump_simple_chain/dump_simple_chain.exe && \
    dune exec src/lib/crypto/pickles/dump_simple_chain/dump_simple_chain.exe
" >/dev/null 2>&1

for f in "$OC_B0_STEP" "$OC_B0_WRAP" "$OC_B1_STEP" "$OC_B1_WRAP" "$OC_B2_STEP" "$OC_B2_WRAP" "$OC_B3_STEP" "$OC_B3_WRAP" "$OC_B4_STEP" "$OC_B4_WRAP"; do
  if [ ! -f "$f" ]; then
    echo "FATAL: OCaml witness $f not produced." >&2
    exit 17
  fi
done

for label in "b0_step:$OC_B0_STEP" "b0_wrap:$OC_B0_WRAP" "b1_step:$OC_B1_STEP" "b1_wrap:$OC_B1_WRAP" "b2_step:$OC_B2_STEP" "b2_wrap:$OC_B2_WRAP" "b3_step:$OC_B3_STEP" "b3_wrap:$OC_B3_WRAP" "b4_step:$OC_B4_STEP" "b4_wrap:$OC_B4_WRAP"; do
  name="${label%%:*}"
  file="${label#*:}"
  echo "  OCaml $name witness: $(wc -l <"$file") lines"
done

echo "==> Running PureScript Test.Pickles.Main (seed=$SEED, KIMCHI_WITNESS_DUMP=/tmp/sc_ps_%c.witness)..."
rm -f /tmp/sc_ps_*.witness
export PATH=$HOME/.nvm/versions/node/v22.22.2/bin:$PATH
cd "$REPO_ROOT"
KIMCHI_DETERMINISTIC_SEED=$SEED \
  KIMCHI_WITNESS_DUMP=/tmp/sc_ps_%c.witness \
  KIMCHI_WITNESS_DUMP_SIDE=ps \
  npx spago test -p pickles -- --example "SimpleChain" >/dev/null 2>&1

for f in "$PS_B0_STEP" "$PS_B0_WRAP" "$PS_B1_STEP" "$PS_B1_WRAP" "$PS_B2_STEP" "$PS_B2_WRAP" "$PS_B3_STEP" "$PS_B3_WRAP" "$PS_B4_STEP" "$PS_B4_WRAP"; do
  if [ ! -f "$f" ]; then
    echo "NOTE: PS witness $f not produced (may be expected if iter hasn't reached that proof yet)."
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
diff_pair b0_step 1    "$OC_B0_STEP"  "$PS_B0_STEP"  /tmp/sc_witness_b0_step.diff
diff_pair b0_wrap 2    "$OC_B0_WRAP"  "$PS_B0_WRAP"  /tmp/sc_witness_b0_wrap.diff
diff_pair b1_step 4    "$OC_B1_STEP"  "$PS_B1_STEP"  /tmp/sc_witness_b1_step.diff
diff_pair b1_wrap 8    "$OC_B1_WRAP"  "$PS_B1_WRAP"  /tmp/sc_witness_b1_wrap.diff
diff_pair b2_step 16   "$OC_B2_STEP"  "$PS_B2_STEP"  /tmp/sc_witness_b2_step.diff
diff_pair b2_wrap 32   "$OC_B2_WRAP"  "$PS_B2_WRAP"  /tmp/sc_witness_b2_wrap.diff
diff_pair b3_step 64   "$OC_B3_STEP"  "$PS_B3_STEP"  /tmp/sc_witness_b3_step.diff
diff_pair b3_wrap 128  "$OC_B3_WRAP"  "$PS_B3_WRAP"  /tmp/sc_witness_b3_wrap.diff
diff_pair b4_step 256  "$OC_B4_STEP"  "$PS_B4_STEP"  /tmp/sc_witness_b4_step.diff
diff_pair b4_wrap 512  "$OC_B4_WRAP"  "$PS_B4_WRAP"  /tmp/sc_witness_b4_wrap.diff

exit $BITS
