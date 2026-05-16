#!/usr/bin/env bash
#
# Runs the chunks2 base case (b0) on both sides with
# KIMCHI_WITNESS_DUMP enabled and diffs the kimchi witness pair:
#
#   counter 0 → chunks2 step proof (Fp, VestaG, num_chunks = 2)
#   counter 1 → chunks2 wrap proof (Fq, PallasG, num_chunks = 1)
#
# The OCaml side is `dump_chunks2.exe`; the PS side is
# `Test.Pickles.Prove.Chunks2`.
#
# Files:
#   /tmp/chunks2_oc_{0,1}.witness
#   /tmp/chunks2_ps_{0,1}.witness
#   /tmp/chunks2_witness_{step,wrap}.diff
#
# Exit code:
#   0    both pairs byte-identical
#   1-3  bitfield (+1 step, +2 wrap)
#   >3   build/run failure
#
# Note: PS prover requires `ulimit -s unlimited` + `node --stack-size`
# because of the 131k mul chain. Witness dumps happen at the start of
# each kimchi proof creation, so downstream prover failure (e.g.,
# constraint mismatch from yet-unfixed chunking code paths) is
# tolerated — the diff catches divergence regardless.

set -e

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SEED=42
OC_STEP=/tmp/chunks2_oc_0.witness
OC_WRAP=/tmp/chunks2_oc_1.witness
PS_STEP=/tmp/chunks2_ps_0.witness
PS_WRAP=/tmp/chunks2_ps_1.witness

echo "==> Running OCaml dump_chunks2.exe (seed=$SEED, KIMCHI_WITNESS_DUMP=/tmp/chunks2_oc_%c.witness)..."
rm -f /tmp/chunks2_oc_*.witness
nix develop mina#default -c bash -c "
  export KIMCHI_DETERMINISTIC_SEED=$SEED
  export KIMCHI_WITNESS_DUMP=/tmp/chunks2_oc_%c.witness
  export KIMCHI_WITNESS_DUMP_SIDE=oc
  cd $REPO_ROOT/mina && \
    dune build src/lib/crypto/pickles/dump_chunks2/dump_chunks2.exe && \
    dune exec src/lib/crypto/pickles/dump_chunks2/dump_chunks2.exe
" >/dev/null 2>&1 || true

for f in "$OC_STEP" "$OC_WRAP"; do
  if [ ! -f "$f" ]; then
    echo "FATAL: OCaml witness $f not produced." >&2
    exit 16
  fi
  echo "  OCaml $(basename "$f" .witness): $(wc -l <"$f") lines"
done

echo "==> Running PureScript Test.Pickles.Prove.Chunks2 (seed=$SEED, ulimit -s unlimited, --stack-size=16000)..."
rm -f /tmp/chunks2_ps_*.witness
export PATH="$HOME/.nvm/versions/node/v23.11.1/bin:$PATH"
cd "$REPO_ROOT"
npx spago build -p pickles >/dev/null 2>&1
(
  ulimit -s unlimited
  KIMCHI_DETERMINISTIC_SEED=$SEED \
    KIMCHI_WITNESS_DUMP=/tmp/chunks2_ps_%c.witness \
    KIMCHI_WITNESS_DUMP_SIDE=ps \
    node --stack-size=16000 \
      -e "import('./output/Test.Pickles.Main/index.js').then(m => m.main())" \
      "node" "--example" "Chunks2" \
      >/dev/null 2>&1 || true
)

for f in "$PS_STEP" "$PS_WRAP"; do
  if [ ! -f "$f" ]; then
    echo "NOTE: PS witness $f not produced (PS prover failed before kimchi reached this proof)."
  else
    echo "  PS $(basename "$f" .witness): $(wc -l <"$f") lines"
  fi
done

echo "==> Diffing witness pairs (stripping #header lines)..."
BITS=0
diff_pair() {
  local tag=$1 bit=$2 oc=$3 ps=$4 out=$5
  if [ ! -f "$ps" ]; then
    echo "  SKIP $tag: PS side missing."
    BITS=$((BITS | bit))
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
diff_pair step 1 "$OC_STEP" "$PS_STEP" /tmp/chunks2_witness_step.diff
diff_pair wrap 2 "$OC_WRAP" "$PS_WRAP" /tmp/chunks2_witness_wrap.diff

exit $BITS
