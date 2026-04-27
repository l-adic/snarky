#!/usr/bin/env bash
#
# Runs both sides of the No_recursion_return loop with KIMCHI_WITNESS_DUMP
# enabled, then diffs the kimchi witness matrices. This is the ground-truth
# check — trace files are diagnostics, witness matrices are definitional.
#
# Both PS and OCaml funnel through `kimchi/src/prover.rs:create_recursive`,
# which dumps the 15-column witness on both sides when KIMCHI_WITNESS_DUMP
# is set. `%c` in the env var is replaced with a monotonic counter:
#
#   counter=0 → step proof (Fp / VestaG, 1 public input at N=0)
#   counter=1 → wrap proof (Fq / PallasG, 40 public inputs)
#
# Output:
#   /tmp/nrr_oc_0.witness  — OCaml step
#   /tmp/nrr_oc_1.witness  — OCaml wrap
#   /tmp/nrr_ps_0.witness  — PS    step
#   /tmp/nrr_ps_1.witness  — PS    wrap
#   /tmp/nrr_witness_step.diff
#   /tmp/nrr_witness_wrap.diff
#
# Exit code:
#   0  both witness matrices byte-identical
#   1  step witness differs
#   2  wrap witness differs
#   3  both differ
#   >3 a build/run step failed

set -e

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SEED=42
KIMCHI_STUBS_LOCAL=/tmp/local_kimchi_stubs

OC_STEP=/tmp/nrr_oc_0.witness
OC_WRAP=/tmp/nrr_oc_1.witness
PS_STEP=/tmp/nrr_ps_0.witness
PS_WRAP=/tmp/nrr_ps_1.witness
STEP_DIFF=/tmp/nrr_witness_step.diff
WRAP_DIFF=/tmp/nrr_witness_wrap.diff

if [ ! -f "$KIMCHI_STUBS_LOCAL/lib/libkimchi_stubs.a" ]; then
  echo "FATAL: $KIMCHI_STUBS_LOCAL/lib/libkimchi_stubs.a missing." >&2
  echo "Build it with:" >&2
  echo "  cd $REPO_ROOT/mina/src/lib/crypto/proof-systems && \\" >&2
  echo "    ~/.cargo/bin/cargo build -p kimchi-stubs --release && \\" >&2
  echo "    mkdir -p $KIMCHI_STUBS_LOCAL/lib && \\" >&2
  echo "    cp target/release/libkimchi_stubs.a $KIMCHI_STUBS_LOCAL/lib/" >&2
  exit 10
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

if [ ! -f "$OC_STEP" ]; then
  echo "FATAL: OCaml step witness ($OC_STEP) not produced." >&2
  exit 11
fi
if [ ! -f "$OC_WRAP" ]; then
  echo "FATAL: OCaml wrap witness ($OC_WRAP) not produced." >&2
  exit 12
fi

OC_STEP_LINES=$(wc -l <"$OC_STEP")
OC_WRAP_LINES=$(wc -l <"$OC_WRAP")
echo "  OCaml step witness: $OC_STEP_LINES lines"
echo "  OCaml wrap witness: $OC_WRAP_LINES lines"

echo "==> Running PureScript Test.Pickles.Main (seed=$SEED, KIMCHI_WITNESS_DUMP=/tmp/nrr_ps_%c.witness)..."
rm -f /tmp/nrr_ps_*.witness
export PATH=$HOME/.nvm/versions/node/v22.22.2/bin:$PATH
cd "$REPO_ROOT"
KIMCHI_DETERMINISTIC_SEED=$SEED \
  KIMCHI_WITNESS_DUMP=/tmp/nrr_ps_%c.witness \
  KIMCHI_WITNESS_DUMP_SIDE=ps \
  npx spago test -p pickles -- --example "NRR" >/dev/null 2>&1

if [ ! -f "$PS_STEP" ]; then
  echo "FATAL: PS step witness ($PS_STEP) not produced." >&2
  exit 13
fi
if [ ! -f "$PS_WRAP" ]; then
  echo "FATAL: PS wrap witness ($PS_WRAP) not produced." >&2
  exit 14
fi

PS_STEP_LINES=$(wc -l <"$PS_STEP")
PS_WRAP_LINES=$(wc -l <"$PS_WRAP")
echo "  PS    step witness: $PS_STEP_LINES lines"
echo "  PS    wrap witness: $PS_WRAP_LINES lines"

echo "==> Diffing step witnesses (stripping #header lines)..."
diff <(grep -v "^#" "$OC_STEP") <(grep -v "^#" "$PS_STEP") >"$STEP_DIFF" && STEP_EXIT=0 || STEP_EXIT=$?

echo "==> Diffing wrap witnesses (stripping #header lines)..."
diff <(grep -v "^#" "$OC_WRAP") <(grep -v "^#" "$PS_WRAP") >"$WRAP_DIFF" && WRAP_EXIT=0 || WRAP_EXIT=$?

EXIT=0
if [ "$STEP_EXIT" = 0 ]; then
  echo "  MATCH: step witness byte-identical ($OC_STEP_LINES lines)."
else
  echo "  DIVERGE: step witness differs. See $STEP_DIFF:"
  head -6 "$STEP_DIFF"
  EXIT=$((EXIT + 1))
fi
if [ "$WRAP_EXIT" = 0 ]; then
  echo "  MATCH: wrap witness byte-identical ($OC_WRAP_LINES lines)."
else
  echo "  DIVERGE: wrap witness differs. See $WRAP_DIFF:"
  head -6 "$WRAP_DIFF"
  EXIT=$((EXIT + 2))
fi

exit $EXIT
