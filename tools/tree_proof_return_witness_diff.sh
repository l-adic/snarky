#!/usr/bin/env bash
#
# Runs both sides of Tree_proof_return (b0 base case + b1 inductive
# case) with KIMCHI_WITNESS_DUMP enabled and diffs the 15-column kimchi
# witness matrices at every counter. This is the ground-truth
# correctness check — trace files are diagnostics; the witness fed
# into kimchi is definitional.
#
# Counter sequence on BOTH sides (OCaml dump_tree_proof_return.exe
# calls `No_recursion_return.step` first, then `Tree_proof_return.step`
# twice — once for b0 and once for b1; PS analog does the same):
#
#   counter 0 → No_recursion_return step  (Fp, VestaG, 1 public input)
#   counter 1 → No_recursion_return wrap  (Fq, PallasG, 40 public inputs)
#   counter 2 → Tree_proof_return b0 step (Fp, VestaG, 67 public inputs)
#   counter 3 → Tree_proof_return b0 wrap (Fq, PallasG, 40 public inputs)
#   counter 4 → Tree_proof_return b1 step (Fp, VestaG, 67 public inputs)
#   counter 5 → Tree_proof_return b1 wrap (Fq, PallasG, 40 public inputs)
#
# Files:
#   /tmp/tree_oc_{0..5}.witness
#   /tmp/tree_ps_{0..5}.witness
#   /tmp/tree_witness_{nrr_step,nrr_wrap,tree_b{0,1}_{step,wrap}}.diff
#
# Partial PS progress (e.g. PS doesn't yet produce b1 witnesses) is
# tolerated: missing PS files are reported as SKIP, not FAIL.
#
# Exit code:
#   0    all six witness pairs byte-identical
#   1-63 bitfield of which pair diverged (+1 nrr_step, +2 nrr_wrap,
#        +4 tree_b0_step, +8 tree_b0_wrap, +16 tree_b1_step,
#        +32 tree_b1_wrap)
#   >63  build/run failure

set -e

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SEED=42
KIMCHI_STUBS_LOCAL=/tmp/local_kimchi_stubs

OC_NRR_STEP=/tmp/tree_oc_0.witness
OC_NRR_WRAP=/tmp/tree_oc_1.witness
OC_TREE_B0_STEP=/tmp/tree_oc_2.witness
OC_TREE_B0_WRAP=/tmp/tree_oc_3.witness
OC_TREE_B1_STEP=/tmp/tree_oc_4.witness
OC_TREE_B1_WRAP=/tmp/tree_oc_5.witness
PS_NRR_STEP=/tmp/tree_ps_0.witness
PS_NRR_WRAP=/tmp/tree_ps_1.witness
PS_TREE_B0_STEP=/tmp/tree_ps_2.witness
PS_TREE_B0_WRAP=/tmp/tree_ps_3.witness
PS_TREE_B1_STEP=/tmp/tree_ps_4.witness
PS_TREE_B1_WRAP=/tmp/tree_ps_5.witness

if [ ! -f "$KIMCHI_STUBS_LOCAL/lib/libkimchi_stubs.a" ]; then
  echo "FATAL: $KIMCHI_STUBS_LOCAL/lib/libkimchi_stubs.a missing." >&2
  echo "Build it with:" >&2
  echo "  cd $REPO_ROOT/mina/src/lib/crypto/proof-systems && \\" >&2
  echo "    ~/.cargo/bin/cargo build -p kimchi-stubs --release && \\" >&2
  echo "    mkdir -p $KIMCHI_STUBS_LOCAL/lib && \\" >&2
  echo "    cp target/release/libkimchi_stubs.a $KIMCHI_STUBS_LOCAL/lib/" >&2
  exit 16
fi

echo "==> Running OCaml dump_tree_proof_return.exe (seed=$SEED, KIMCHI_WITNESS_DUMP=/tmp/tree_oc_%c.witness)..."
rm -f /tmp/tree_oc_*.witness
nix develop mina#default -c bash -c "
  export KIMCHI_STUBS_STATIC_LIB=$KIMCHI_STUBS_LOCAL
  export KIMCHI_DETERMINISTIC_SEED=$SEED
  export KIMCHI_WITNESS_DUMP=/tmp/tree_oc_%c.witness
  export KIMCHI_WITNESS_DUMP_SIDE=oc
  cd $REPO_ROOT/mina && \
    dune build src/lib/crypto/pickles/dump_tree_proof_return/dump_tree_proof_return.exe && \
    dune exec src/lib/crypto/pickles/dump_tree_proof_return/dump_tree_proof_return.exe
" >/dev/null 2>&1

for f in "$OC_NRR_STEP" "$OC_NRR_WRAP" "$OC_TREE_B0_STEP" "$OC_TREE_B0_WRAP" "$OC_TREE_B1_STEP" "$OC_TREE_B1_WRAP"; do
  if [ ! -f "$f" ]; then
    echo "FATAL: OCaml witness $f not produced." >&2
    exit 17
  fi
done

for label in "nrr_step:$OC_NRR_STEP" "nrr_wrap:$OC_NRR_WRAP" "tree_b0_step:$OC_TREE_B0_STEP" "tree_b0_wrap:$OC_TREE_B0_WRAP" "tree_b1_step:$OC_TREE_B1_STEP" "tree_b1_wrap:$OC_TREE_B1_WRAP"; do
  name="${label%%:*}"
  file="${label#*:}"
  echo "  OCaml $name witness: $(wc -l <"$file") lines"
done

echo "==> Running PureScript Test.Pickles.Main (seed=$SEED, KIMCHI_WITNESS_DUMP=/tmp/tree_ps_%c.witness)..."
rm -f /tmp/tree_ps_*.witness
export PATH=$HOME/.nvm/versions/node/v22.22.2/bin:$PATH
cd "$REPO_ROOT"
KIMCHI_DETERMINISTIC_SEED=$SEED \
  KIMCHI_WITNESS_DUMP=/tmp/tree_ps_%c.witness \
  KIMCHI_WITNESS_DUMP_SIDE=ps \
  npx spago test -p pickles -- --example "TreeProofReturn" >/dev/null 2>&1

for f in "$PS_NRR_STEP" "$PS_NRR_WRAP" "$PS_TREE_B0_STEP" "$PS_TREE_B0_WRAP" "$PS_TREE_B1_STEP" "$PS_TREE_B1_WRAP"; do
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
diff_pair nrr_step     1  "$OC_NRR_STEP"      "$PS_NRR_STEP"      /tmp/tree_witness_nrr_step.diff
diff_pair nrr_wrap     2  "$OC_NRR_WRAP"      "$PS_NRR_WRAP"      /tmp/tree_witness_nrr_wrap.diff
diff_pair tree_b0_step 4  "$OC_TREE_B0_STEP"  "$PS_TREE_B0_STEP"  /tmp/tree_witness_tree_b0_step.diff
diff_pair tree_b0_wrap 8  "$OC_TREE_B0_WRAP"  "$PS_TREE_B0_WRAP"  /tmp/tree_witness_tree_b0_wrap.diff
diff_pair tree_b1_step 16 "$OC_TREE_B1_STEP"  "$PS_TREE_B1_STEP"  /tmp/tree_witness_tree_b1_step.diff
diff_pair tree_b1_wrap 32 "$OC_TREE_B1_WRAP"  "$PS_TREE_B1_WRAP"  /tmp/tree_witness_tree_b1_wrap.diff

exit $BITS
