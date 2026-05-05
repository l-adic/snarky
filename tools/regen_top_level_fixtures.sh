#!/usr/bin/env bash
# Regenerate top-level step_main_* / wrap_main_* circuit-diff fixtures
# from the production OCaml compile path.
#
# Each `dump_*.exe` driver in `mina/src/lib/crypto/pickles/dump_*` runs
# the same `Pickles.compile_promise` call the production code does.
# With `PICKLES_STEP_CS_DUMP` / `PICKLES_WRAP_CS_DUMP` set (added in
# `compile.ml`'s step/wrap CS construction blocks), each driver writes
# one `<stem>{.json,_cached_constants.json,_gate_labels.jsonl}` triple
# per CS construction, with `%c` substituted by a monotonic counter so
# multi-rule compiles emit one file per step / wrap CS.
#
# This script:
#   1. Builds the necessary dump drivers in mina.
#   2. Runs each driver into a temp dir with `KIMCHI_DETERMINISTIC_SEED=42`.
#   3. Copies each `<stem>` triple to its corresponding fixture filename
#      under `packages/pickles-circuit-diffs/circuits/ocaml/`.
#
# Replaces the `Step_main_for_dump` / `Wrap_main_for_dump` synthetic
# dump path that previously parallel-rewrote rule bodies. See
# `docs/sideload-child-cs-loop-handoff.md` for context on why the
# synthetic dump diverged from production.

set -euo pipefail

cd "$(dirname "$0")/.."
SNARKY_ROOT="$(pwd)"
FIXTURES_DIR="${SNARKY_ROOT}/packages/pickles-circuit-diffs/circuits/ocaml"
TMP="${TMP:-/tmp/regen_top_level_fixtures}"
DRIVER_BIN_DIR="${SNARKY_ROOT}/mina/_build/default/src/lib/crypto/pickles"

DRIVERS=(
  dump_simple_chain
  dump_simple_chain_n2
  dump_no_recursion_return
  dump_add_one_return
  dump_tree_proof_return
  dump_two_phase_chain
  dump_side_loaded_main
)

echo ">> Building drivers in mina..."
( cd mina && dune build $(for d in "${DRIVERS[@]}"; do
    echo -n " src/lib/crypto/pickles/${d}/${d}.exe"
  done) )

echo ">> Running drivers into ${TMP}..."
rm -rf "${TMP}"
mkdir -p "${TMP}"
for d in "${DRIVERS[@]}"; do
  echo "   - ${d}"
  PICKLES_STEP_CS_DUMP="${TMP}/${d}_step_%c" \
  PICKLES_WRAP_CS_DUMP="${TMP}/${d}_wrap_%c" \
  KIMCHI_DETERMINISTIC_SEED=42 \
  "${DRIVER_BIN_DIR}/${d}/${d}.exe" >/dev/null
done

# Copy a (stem) → fixture: stem.json, stem_cached_constants.json,
# stem_gate_labels.jsonl all go to the corresponding fixture name.
copy_fixture () {
  local src_stem="$1" dst_name="$2"
  cp "${src_stem}.json" "${FIXTURES_DIR}/${dst_name}.json"
  cp "${src_stem}_cached_constants.json" "${FIXTURES_DIR}/${dst_name}_cached_constants.json"
  cp "${src_stem}_gate_labels.jsonl" "${FIXTURES_DIR}/${dst_name}_gate_labels.jsonl"
}

# %c index → fixture mapping per driver. Each %c=k corresponds to the
# k-th step / wrap CS the driver constructs (in compile_promise order).

# dump_simple_chain: 1 rule (Simple_chain N1) → 1 step + 1 wrap.
copy_fixture "${TMP}/dump_simple_chain_step_0"  step_main_simple_chain_circuit
copy_fixture "${TMP}/dump_simple_chain_wrap_0"  wrap_main_circuit

# dump_simple_chain_n2: 1 rule (Simple_chain with prevs=[self;self], N2) → 1 step + 1 wrap.
# The driver's prove step intentionally fails verification (dummy prev
# proofs don't satisfy the recursion equation); compile + CS dump
# complete first, so the fixtures are captured. Run with `set +e`
# tolerance, or run the driver expecting non-zero exit.
copy_fixture "${TMP}/dump_simple_chain_n2_step_0"  step_main_simple_chain_n2_circuit
copy_fixture "${TMP}/dump_simple_chain_n2_wrap_0"  wrap_main_n2_circuit

# dump_no_recursion_return: 1 rule (No_recursion_return) → 1 step + 1 wrap.
# The wrap fixture for NRR isn't currently in the test set; we still
# copy it so the file is available for any future test addition.
copy_fixture "${TMP}/dump_no_recursion_return_step_0"  step_main_no_recursion_return_circuit
# (no wrap_main_no_recursion_return_circuit fixture currently)

# dump_add_one_return: 1 rule (Add_one_return) → 1 step + 1 wrap.
copy_fixture "${TMP}/dump_add_one_return_step_0"  step_main_add_one_return_circuit
copy_fixture "${TMP}/dump_add_one_return_wrap_0"  wrap_main_add_one_return_circuit

# dump_tree_proof_return: 2 rules (NRR + TPR self) → 2 step + 1 wrap.
# step_0 is NRR (the inner rule); step_1 is TPR proper. Only TPR's
# step is tested currently. NRR step CS in this context (inside TPR
# compile) may differ from the standalone dump_no_recursion_return
# step CS — different known_wrap_keys, etc. — so we don't conflate
# them.
copy_fixture "${TMP}/dump_tree_proof_return_step_1"  step_main_tree_proof_return_circuit
copy_fixture "${TMP}/dump_tree_proof_return_wrap_0"  wrap_main_tree_proof_return_circuit
# (step_main_no_recursion_return_aux_circuit reserved for the
# step_0 output if we want to test it separately)

# dump_two_phase_chain: 2 rules (make_zero + increment) → 2 step + 1 wrap.
# Only the wrap fixture is in the test set. step_main_two_phase_chain_*
# fixtures don't exist (the per-rule app-circuit fixtures are the
# `app_circuit_two_phase_chain_*` sub-circuits, not full step_mains).
copy_fixture "${TMP}/dump_two_phase_chain_wrap_0"  wrap_main_two_phase_chain_circuit

# dump_side_loaded_main: 2 compiles (child + parent) → 2 step + 2 wrap.
copy_fixture "${TMP}/dump_side_loaded_main_step_0"  step_main_side_loaded_child_circuit
copy_fixture "${TMP}/dump_side_loaded_main_step_1"  step_main_side_loaded_main_circuit
copy_fixture "${TMP}/dump_side_loaded_main_wrap_1"  wrap_main_side_loaded_main_circuit
# (wrap_0 is the child wrap CS; not currently in the test set)

# step_main_simple_chain_n2_circuit and wrap_main_n2_circuit have NO
# corresponding production driver yet. They remain whatever was
# previously committed (= synthetic-vs-synthetic). Add a
# `dump_simple_chain_n2` driver in mina to migrate them.

echo ">> Done. Fixtures regenerated in ${FIXTURES_DIR}"
