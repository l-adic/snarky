#!/usr/bin/env bash
#
# Runs both sides of the side-loaded main scenario with
# KIMCHI_WITNESS_DUMP enabled and diffs the 15-column kimchi witness
# matrices at every counter.
#
# Counter sequence on BOTH sides (OCaml dump_side_loaded_main.exe
# compiles two pickles tags — child (No_recursion, mpv=N0) and main
# (Side_loaded prev, mpv=N1) — then drives one child step + one main
# step; PS analog `Test.Pickles.Prove.SideLoadedMain` does the same):
#
#   counter 0 → child  b0 step (Fp, VestaG)
#   counter 1 → child  b0 wrap (Fq, PallasG)
#   counter 2 → main   b1 step (Fp, VestaG, side-loaded prev = child b0)
#   counter 3 → main   b1 wrap (Fq, PallasG)
#
# Files:
#   /tmp/sl_oc_{0..3}.witness
#   /tmp/sl_ps_{0..3}.witness
#   /tmp/sl_witness_{child,main}_{step,wrap}.diff
#
# Partial PS progress is tolerated: missing PS files are reported as SKIP.
#
# Exit code:
#   0     all four pairs byte-identical
#   1-15  bitfield (+1 child_step, +2 child_wrap, +4 main_step, +8 main_wrap)
#   16+   build/run failure

set -e

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SEED=42
KIMCHI_STUBS_LOCAL=/tmp/local_kimchi_stubs

OC_CHILD_STEP=/tmp/sl_oc_0.witness
OC_CHILD_WRAP=/tmp/sl_oc_1.witness
OC_MAIN_STEP=/tmp/sl_oc_2.witness
OC_MAIN_WRAP=/tmp/sl_oc_3.witness
PS_CHILD_STEP=/tmp/sl_ps_0.witness
PS_CHILD_WRAP=/tmp/sl_ps_1.witness
PS_MAIN_STEP=/tmp/sl_ps_2.witness
PS_MAIN_WRAP=/tmp/sl_ps_3.witness

if [ ! -f "$KIMCHI_STUBS_LOCAL/lib/libkimchi_stubs.a" ]; then
  echo "FATAL: $KIMCHI_STUBS_LOCAL/lib/libkimchi_stubs.a missing." >&2
  echo "Build it with:" >&2
  echo "  cd $REPO_ROOT/mina/src/lib/crypto/proof-systems && \\" >&2
  echo "    ~/.cargo/bin/cargo build -p kimchi-stubs --release && \\" >&2
  echo "    mkdir -p $KIMCHI_STUBS_LOCAL/lib && \\" >&2
  echo "    cp target/release/libkimchi_stubs.a $KIMCHI_STUBS_LOCAL/lib/" >&2
  exit 16
fi

echo "==> Running OCaml dump_side_loaded_main.exe (seed=$SEED, KIMCHI_WITNESS_DUMP=/tmp/sl_oc_%c.witness)..."
rm -f /tmp/sl_oc_*.witness
nix develop mina#default -c bash -c "
  export KIMCHI_STUBS_STATIC_LIB=$KIMCHI_STUBS_LOCAL
  export KIMCHI_DETERMINISTIC_SEED=$SEED
  export KIMCHI_WITNESS_DUMP=/tmp/sl_oc_%c.witness
  export KIMCHI_WITNESS_DUMP_SIDE=oc
  cd $REPO_ROOT/mina && \
    dune build src/lib/crypto/pickles/dump_side_loaded_main/dump_side_loaded_main.exe && \
    dune exec src/lib/crypto/pickles/dump_side_loaded_main/dump_side_loaded_main.exe
" >/dev/null 2>&1

for f in "$OC_CHILD_STEP" "$OC_CHILD_WRAP" "$OC_MAIN_STEP" "$OC_MAIN_WRAP"; do
  if [ ! -f "$f" ]; then
    echo "FATAL: OCaml witness $f not produced." >&2
    exit 17
  fi
done
for label in "child_step:$OC_CHILD_STEP" "child_wrap:$OC_CHILD_WRAP" "main_step:$OC_MAIN_STEP" "main_wrap:$OC_MAIN_WRAP"; do
  name="${label%%:*}"
  file="${label#*:}"
  echo "  OCaml $name witness: $(wc -l <"$file") lines"
done

echo "==> Running PureScript Test.Pickles.Prove.SideLoadedMain (seed=$SEED, KIMCHI_WITNESS_DUMP=/tmp/sl_ps_%c.witness)..."
rm -f /tmp/sl_ps_*.witness
export PATH=$HOME/.nvm/versions/node/v22.22.2/bin:$PATH
cd "$REPO_ROOT"
KIMCHI_DETERMINISTIC_SEED=$SEED \
  KIMCHI_WITNESS_DUMP=/tmp/sl_ps_%c.witness \
  KIMCHI_WITNESS_DUMP_SIDE=ps \
  npx spago test -p pickles -- --example "SideLoadedMain" >/dev/null 2>&1

for f in "$PS_CHILD_STEP" "$PS_CHILD_WRAP" "$PS_MAIN_STEP" "$PS_MAIN_WRAP"; do
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
diff_pair child_step 1 "$OC_CHILD_STEP" "$PS_CHILD_STEP" /tmp/sl_witness_child_step.diff
diff_pair child_wrap 2 "$OC_CHILD_WRAP" "$PS_CHILD_WRAP" /tmp/sl_witness_child_wrap.diff
diff_pair main_step  4 "$OC_MAIN_STEP"  "$PS_MAIN_STEP"  /tmp/sl_witness_main_step.diff
diff_pair main_wrap  8 "$OC_MAIN_WRAP"  "$PS_MAIN_WRAP"  /tmp/sl_witness_main_wrap.diff

exit $BITS
