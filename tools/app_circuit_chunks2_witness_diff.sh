#!/usr/bin/env bash
#
# Runs the standalone chunks2 application circuit on both sides
# (OCaml `dump_app_circuit_chunks2_witness.exe` and PS
# `Test.Pickles.CircuitDiffs.Main` filtered to the witness-dump entry)
# with KIMCHI_WITNESS_DUMP enabled and diffs the kimchi witness columns.
#
# This isolates the chunks2 leaf application body from Pickles'
# step/wrap scaffolding: the body is compiled to a standalone kimchi
# constraint system, the kimchi prover runs once, and the witness dump
# captures only the app body's variable assignments.
#
# Files:
#   /tmp/app_circuit_chunks2_oc_0.witness
#   /tmp/app_circuit_chunks2_ps_0.witness
#   /tmp/app_circuit_chunks2_witness.diff
#
# Exit code:
#   0  byte-identical
#   1  diverged
#   >1 build/run failure
#
# Note: the PS prover requires `--stack-size=16000` (or larger) because
# the 131k mul chain isn't stack-safe in the current Snarky state-monad
# bind. Reducing iters or making the loop tail-recursive would lift
# that requirement.

set -e

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OC_WITNESS=/tmp/app_circuit_chunks2_oc_0.witness
PS_WITNESS=/tmp/app_circuit_chunks2_ps_0.witness
DIFF_OUT=/tmp/app_circuit_chunks2_witness.diff

echo "==> Running OCaml dump_app_circuit_chunks2_witness.exe (KIMCHI_WITNESS_DUMP=$OC_WITNESS)..."
rm -f "$OC_WITNESS"
nix develop mina#default -c bash -c "
  export KIMCHI_WITNESS_DUMP=$OC_WITNESS
  export KIMCHI_WITNESS_DUMP_SIDE=oc
  cd $REPO_ROOT/mina && \
    dune build src/lib/crypto/pickles/dump_app_circuit_chunks2_witness/dump_app_circuit_chunks2_witness.exe && \
    dune exec src/lib/crypto/pickles/dump_app_circuit_chunks2_witness/dump_app_circuit_chunks2_witness.exe
" >/dev/null 2>&1

if [ ! -f "$OC_WITNESS" ]; then
  echo "FATAL: OCaml witness $OC_WITNESS not produced." >&2
  exit 16
fi
echo "  OCaml witness: $(wc -l <"$OC_WITNESS") lines"

echo "==> Running PureScript prover (KIMCHI_WITNESS_DUMP=$PS_WITNESS, --stack-size=16000)..."
rm -f "$PS_WITNESS"
export PATH="$HOME/.nvm/versions/node/v23.11.1/bin:$PATH"
cd "$REPO_ROOT"
npx spago build -p pickles-circuit-diffs >/dev/null 2>&1
# Witness is dumped at the start of pallasCreateProofWithPrev. Downstream
# prover failure (e.g., constraint mismatch) is ignored — we only need
# the file. The diff below catches divergence either way.
KIMCHI_WITNESS_DUMP="$PS_WITNESS" \
  KIMCHI_WITNESS_DUMP_SIDE=ps \
  node --stack-size=16000 \
    -e "import('./output/Test.Pickles.CircuitDiffs.Main/index.js').then(m => m.main())" \
    "node" "--example" "app_circuit_chunks2 witness" \
    >/dev/null 2>&1 || true

if [ ! -f "$PS_WITNESS" ]; then
  echo "FATAL: PS witness $PS_WITNESS not produced." >&2
  exit 17
fi
echo "  PS witness: $(wc -l <"$PS_WITNESS") lines"

echo "==> Diffing witness files (stripping #header lines)..."
if diff <(grep -v "^#" "$OC_WITNESS") <(grep -v "^#" "$PS_WITNESS") >"$DIFF_OUT"; then
  echo "  MATCH: byte-identical ($(wc -l <"$OC_WITNESS") lines)."
  exit 0
else
  echo "  DIVERGE: see $DIFF_OUT"
  head -4 "$DIFF_OUT" | sed 's/^/    /'
  exit 1
fi
