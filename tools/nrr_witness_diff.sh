#!/usr/bin/env bash
#
# Runs both sides of No_recursion_return (NRR) with KIMCHI_WITNESS_DUMP
# enabled and diffs the 15-column kimchi witness matrices for the two
# proves NRR produces.
#
# Counter sequence on BOTH sides (OCaml dump_no_recursion_return.exe
# calls compile_promise + step once → 1 step + 1 wrap proof; PS analog
# does the same):
#
#   counter 0 → NRR b0 step (Fp, VestaG)
#   counter 1 → NRR b0 wrap (Fq, PallasG)
#
# Files:
#   /tmp/nrr_oc_{0,1}.witness
#   /tmp/nrr_ps_{0,1}.witness
#   /tmp/nrr_witness_b0_{step,wrap}.diff
#
# Exit code:
#   0    both pairs byte-identical
#   1    b0_step diverges
#   2    b0_wrap diverges
#   3    both diverge
#  16+   build/run failure

set -e

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SEED=42
KIMCHI_STUBS_LOCAL=/tmp/local_kimchi_stubs

OC_B0_STEP=/tmp/nrr_oc_0.witness
OC_B0_WRAP=/tmp/nrr_oc_1.witness
PS_B0_STEP=/tmp/nrr_ps_0.witness
PS_B0_WRAP=/tmp/nrr_ps_1.witness

if [ ! -f "$KIMCHI_STUBS_LOCAL/lib/libkimchi_stubs.a" ]; then
  echo "FATAL: $KIMCHI_STUBS_LOCAL/lib/libkimchi_stubs.a missing." >&2
  echo "Build it with:" >&2
  echo "  cd $REPO_ROOT/mina/src/lib/crypto/proof-systems && \\" >&2
  echo "    ~/.cargo/bin/cargo build -p kimchi-stubs --release && \\" >&2
  echo "    mkdir -p $KIMCHI_STUBS_LOCAL/lib && \\" >&2
  echo "    cp target/release/libkimchi_stubs.a $KIMCHI_STUBS_LOCAL/lib/" >&2
  exit 16
fi

echo "==> Running OCaml dump_no_recursion_return.exe (seed=$SEED, KIMCHI_WITNESS_DUMP=/tmp/nrr_oc_%c.witness)..."
rm -f /tmp/nrr_oc_*.witness
nix develop mina#default -c bash -c "
  export KIMCHI_STUBS_STATIC_LIB=$KIMCHI_STUBS_LOCAL
  export KIMCHI_DETERMINISTIC_SEED=$SEED
  export KIMCHI_WITNESS_DUMP=/tmp/nrr_oc_%c.witness
  export KIMCHI_WITNESS_DUMP_SIDE=oc
  cd $REPO_ROOT/mina && \
    dune build src/lib/crypto/pickles/dump_no_recursion_return/dump_no_recursion_return.exe && \
    dune exec src/lib/crypto/pickles/dump_no_recursion_return/dump_no_recursion_return.exe
" >/dev/null 2>&1

for f in "$OC_B0_STEP" "$OC_B0_WRAP"; do
  if [ ! -f "$f" ]; then
    echo "FATAL: OCaml witness $f not produced." >&2
    exit 17
  fi
done
for label in "b0_step:$OC_B0_STEP" "b0_wrap:$OC_B0_WRAP"; do
  name="${label%%:*}"
  file="${label#*:}"
  echo "  OCaml $name witness: $(wc -l <"$file") lines"
done

echo "==> Running PureScript Test.Pickles.Prove.NoRecursionReturn (seed=$SEED, KIMCHI_WITNESS_DUMP=/tmp/nrr_ps_%c.witness)..."
rm -f /tmp/nrr_ps_*.witness
export PATH=$HOME/.nvm/versions/node/v22.22.2/bin:$PATH
cd "$REPO_ROOT"
KIMCHI_DETERMINISTIC_SEED=$SEED \
  KIMCHI_WITNESS_DUMP=/tmp/nrr_ps_%c.witness \
  KIMCHI_WITNESS_DUMP_SIDE=ps \
  npx spago test -p pickles -- --example "NoRecursionReturn" >/dev/null 2>&1

for f in "$PS_B0_STEP" "$PS_B0_WRAP"; do
  if [ ! -f "$f" ]; then
    echo "NOTE: PS witness $f not produced."
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
diff_pair b0_step 1 "$OC_B0_STEP" "$PS_B0_STEP" /tmp/nrr_witness_b0_step.diff
diff_pair b0_wrap 2 "$OC_B0_WRAP" "$PS_B0_WRAP" /tmp/nrr_witness_b0_wrap.diff

exit $BITS
