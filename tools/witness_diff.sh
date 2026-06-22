#!/usr/bin/env bash
#
# Witness-equivalence harness (consolidated). For a given circuit, runs the
# prover on BOTH the OCaml (kimchi-stubs) and PureScript sides with
# KIMCHI_WITNESS_DUMP enabled, then diffs the 15-column kimchi witness
# matrices counter-by-counter (stripping `#`-header lines). The witness is
# the definitional ground-truth correctness check.
#
# Consolidated witness-equivalence harness (all circuits in one script). Both sides funnel
# through `ProverProof::create_recursive`, whose KIMCHI_WITNESS_DUMP hook
# emits one file per proof with `%c` = a monotonic counter; each counter is
# mapped to a label below.
#
# Usage:
#   tools/witness_diff.sh <circuit> [<circuit> ...]   diff one or more circuits
#   tools/witness_diff.sh all                         all circuits except chunks4
#   tools/witness_diff.sh all --slow                  all circuits incl. chunks4
#   tools/witness_diff.sh --list                      list known circuits
#   tools/witness_diff.sh --pair <ocaml> <ps> [labels]  diff two raw files
#
# Circuits: simple_chain nrr tree_proof_return two_phase_chain sideload
#           chunks2 chunks4 app_circuit_chunks2
#
# Prereqs: nix (mina dev shell), mina submodule, node 23. Seed is pinned at
# KIMCHI_DETERMINISTIC_SEED (default 42). Missing witness files report SKIP
# (e.g. an inductive iteration the PS side hasn't reached). Exit 0 iff every
# present pair is byte-identical.

set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$REPO/tools/lib/common.sh"
SEED="${KIMCHI_DETERMINISTIC_SEED:-42}"
source "$REPO/tools/lib/setup-node.sh"

source "$REPO/tools/lib/circuits.sh"
ALL="$ALL_CIRCUITS"

# circuit -> "dumper|ps_pkg|ps_main|ps_example|<space-separated counter-ordered labels>"
cfg() {
  case "$1" in
    simple_chain)
      echo "dump_simple_chain|pickles|Test.Pickles.Main|SimpleChain|b0_step b0_wrap b1_step b1_wrap b2_step b2_wrap b3_step b3_wrap b4_step b4_wrap" ;;
    simple_chain_n2)
      echo "dump_simple_chain_n2_fixtures|pickles|Test.Pickles.Main|SimpleChainN2|b0_step b0_wrap b1_step b1_wrap b2_step b2_wrap" ;;
    nrr)
      echo "dump_no_recursion_return|pickles|Test.Pickles.Main|NoRecursionReturn|step_b0 wrap_b0" ;;
    tree_proof_return)
      echo "dump_tree_proof_return|pickles|Test.Pickles.Main|TreeProofReturn|nrr_step nrr_wrap tree_b0_step tree_b0_wrap tree_b1_step tree_b1_wrap tree_b2_step tree_b2_wrap tree_b3_step tree_b3_wrap tree_b4_step tree_b4_wrap" ;;
    two_phase_chain)
      echo "dump_two_phase_chain|pickles|Test.Pickles.Main|TwoPhaseChain|b0_step b0_wrap b1_step b1_wrap b2_step b2_wrap" ;;
    sideload)
      echo "dump_side_loaded_main|pickles|Test.Pickles.Main|SideLoadedMain|child_step child_wrap main_step main_wrap" ;;
    chunks2)
      echo "dump_chunks2|pickles|Test.Pickles.Main|Chunks2|step wrap" ;;
    chunks4)
      echo "dump_chunks4|pickles|Test.Pickles.Main|Chunks4|step wrap" ;;
    app_circuit_chunks2)
      echo "dump_app_circuit_chunks2_witness|pickles-circuit-diffs|Test.Pickles.CircuitDiffs.Main|app_circuit_chunks2 witness|app" ;;
    *) return 1 ;;
  esac
}

# diff_pair <oc> <ps> <tag> [labels_file]  -> 0 match, 1 diverge, 2 skip
# On divergence, reports the first (col,row) mismatch + the two values, and
# (if given) the PS row-label-stack context for that row.
diff_pair() {
  local oc="$1" ps="$2" tag="$3" labels="${4:-}"
  if [ ! -f "$oc" ]; then echo "  SKIP  $tag (OCaml witness missing)"; return 2; fi
  if [ ! -f "$ps" ]; then echo "  SKIP  $tag (PS witness missing)"; return 2; fi
  local first
  first=$(diff <(grep -v '^#' "$oc") <(grep -v '^#' "$ps") | head -1)
  if [ -z "$first" ]; then
    echo "  MATCH $tag ($(grep -vc '^#' "$oc") rows)"
    return 0
  fi
  local ln ocl psl col row ocv psv
  ln=$(echo "$first" | sed 's/[^0-9].*//')
  ocl=$(grep -v '^#' "$oc" | sed -n "${ln}p")
  psl=$(grep -v '^#' "$ps" | sed -n "${ln}p")
  col=$(echo "$ocl" | awk '{print $1}'); row=$(echo "$ocl" | awk '{print $2}')
  ocv=$(echo "$ocl" | awk '{print $3}'); psv=$(echo "$psl" | awk '{print $3}')
  echo "  DIFF  $tag — first mismatch at col=$col row=$row"
  echo "          OCaml: $ocv"
  echo "          PS:    $psv"
  if [ -n "$labels" ] && [ -f "$labels" ]; then
    echo "          row $row context: $(grep "^${row}\\.\\." "$labels" | tail -1 | awk -F'\t' '{print $2}')"
  fi
  return 1
}

run_ocaml() { # circuit dumper
  local c="$1" dumper="$2"
  rm -f "/tmp/wd_${c}_oc_"*.witness
  # Use the RELATIVE flake-ref (mina#default) from the repo root: an
  # absolute path-ref makes nix snapshot a clean store copy that drops the
  # dirty in-tree proof-systems submodule (missing Cargo.lock → eval error).
  ( cd "$REPO" && nix develop mina#default -c bash -c "
    export KIMCHI_DETERMINISTIC_SEED=$SEED
    export KIMCHI_WITNESS_DUMP=/tmp/wd_${c}_oc_%c.witness
    export KIMCHI_WITNESS_DUMP_SIDE=oc
    cd mina && \
      dune build 'src/lib/crypto/pickles/$dumper/$dumper.exe' && \
      dune exec 'src/lib/crypto/pickles/$dumper/$dumper.exe'
  " ) >/dev/null 2>&1 || true
}

run_ps() { # circuit ps_pkg ps_main ps_example
  local c="$1" pkg="$2" main="$3" example="$4"
  rm -f "/tmp/wd_${c}_ps_"*.witness
  ( cd "$REPO" && npx spago build -p "$pkg" >/dev/null 2>&1
    ulimit -s unlimited 2>/dev/null || true
    KIMCHI_DETERMINISTIC_SEED="$SEED" \
    KIMCHI_WITNESS_DUMP="/tmp/wd_${c}_ps_%c.witness" \
    KIMCHI_WITNESS_DUMP_SIDE=ps \
      node --stack-size=16000 \
        -e "import('./output/${main}/index.js').then(m => m.main())" \
        node --example "$example" >/dev/null 2>&1 || true )
}

run_circuit() {
  local c="$1" spec dumper pkg main example labels
  spec=$(cfg "$c") || { echo "unknown circuit: $c (try --list)" >&2; return 99; }
  IFS='|' read -r dumper pkg main example labels <<<"$spec"

  echo "== $c =="
  echo "  -> OCaml ($dumper)…"; run_ocaml "$c" "$dumper"
  echo "  -> PureScript ($main --example \"$example\")…"; run_ps "$c" "$pkg" "$main" "$example"

  local n=0 fails=0 rc
  for lbl in $labels; do
    diff_pair "/tmp/wd_${c}_oc_${n}.witness" "/tmp/wd_${c}_ps_${n}.witness" "$lbl"
    rc=$?; [ "$rc" -eq 1 ] && fails=$((fails + 1))
    n=$((n + 1))
  done
  if [ "$fails" -eq 0 ]; then echo "  => $c: all present pairs match"; else echo "  => $c: $fails diverged"; fi
  return "$fails"
}

usage() { sed -n '2,/^# present pair/p' "${BASH_SOURCE[0]}" | sed 's/^#\{0,1\} \{0,1\}//'; }

case "${1:-}" in
  ""|-h|--help) usage; exit 0 ;;
  --list) echo "$ALL" | tr ' ' '\n'; exit 0 ;;
  --pair)
    shift
    [ $# -ge 2 ] || { echo "usage: $0 --pair <ocaml_witness> <ps_witness> [labels]" >&2; exit 1; }
    diff_pair "$1" "$2" "pair" "${3:-}"; exit $?
    ;;
  all)
    shift; slow=false; [ "${1:-}" = "--slow" ] && slow=true
    total=0
    for c in $ALL; do
      if [ "$c" = "chunks4" ] && ! $slow; then
        echo "== chunks4 == (skipped; pass --slow to include the multi-hour prove)"
        continue
      fi
      run_circuit "$c" || total=$((total + 1))
    done
    exit "$total"
    ;;
  *)
    total=0
    for c in "$@"; do run_circuit "$c" || total=$((total + 1)); done
    exit "$total"
    ;;
esac
