#!/usr/bin/env bash
# Regenerate chunked-circuit fixtures for chunking implementation work
# (docs/chunking.md Phase 0).
#
# These fixtures are NOT committed to git — the chunks2 step CS alone is
# ~56MB (the application body forces a 2^16-row circuit; chunks4/8 push
# the row count to 2^17/2^18). To work on chunking, run this script
# locally before invoking the corresponding circuit-diff tests.
#
# Output: packages/pickles-circuit-diffs/circuits/ocaml/chunks{2,4,8}_{step,wrap}_main_circuit.json
# (plus the *_cached_constants.json / *_gate_labels.jsonl / *_labels.jsonl
# triple per stem, same shape as the other top-level fixtures).
#
# Required tools:
#   - nix (to enter the mina dev shell for the OCaml build)
#   - mina submodule initialized
#
# Optional env:
#   - CHUNKS_VARIANTS — space-separated list of variants to regen
#     (default: "2 4 8"). Set to "2" to skip the multi-hour chunks4/8 runs.

set -euo pipefail

cd "$(dirname "$0")/.."
SNARKY_ROOT="$(pwd)"
FIXTURES_DIR="${SNARKY_ROOT}/packages/pickles-circuit-diffs/circuits/ocaml"
TMP="${TMP:-/tmp/regen_chunks_fixtures}"
DRIVER_BIN_DIR="${SNARKY_ROOT}/mina/_build/default/src/lib/crypto/pickles"
VARIANTS="${CHUNKS_VARIANTS:-2 4 8}"

DRIVERS=()
for n in $VARIANTS; do
  DRIVERS+=("dump_chunks${n}")
done

echo ">> Building chunks drivers in mina..."
nix develop mina#default -c bash -c "cd mina && dune build $(
  for d in "${DRIVERS[@]}"; do
    printf " src/lib/crypto/pickles/%s/%s.exe" "$d" "$d"
  done)"

echo ">> Running drivers into ${TMP}..."
rm -rf "${TMP}"
mkdir -p "${TMP}" "${FIXTURES_DIR}"
for d in "${DRIVERS[@]}"; do
  echo "   - ${d} (this is slow: 2^17..2^19 Field.muls)"
  PICKLES_STEP_CS_DUMP="${TMP}/${d}_step_%c" \
  PICKLES_WRAP_CS_DUMP="${TMP}/${d}_wrap_%c" \
  KIMCHI_DETERMINISTIC_SEED=42 \
  "${DRIVER_BIN_DIR}/${d}/${d}.exe" >/dev/null
done

copy_fixture () {
  local src_stem="$1" dst_name="$2"
  cp "${src_stem}.json" "${FIXTURES_DIR}/${dst_name}.json"
  cp "${src_stem}_cached_constants.json" "${FIXTURES_DIR}/${dst_name}_cached_constants.json"
  cp "${src_stem}_gate_labels.jsonl" "${FIXTURES_DIR}/${dst_name}_gate_labels.jsonl"
  cp "${src_stem}_labels.jsonl" "${FIXTURES_DIR}/${dst_name}_labels.jsonl"
}

for n in $VARIANTS; do
  copy_fixture "${TMP}/dump_chunks${n}_step_0" "chunks${n}_step_main_circuit"
  copy_fixture "${TMP}/dump_chunks${n}_wrap_0" "chunks${n}_wrap_main_circuit"
done

echo ">> Done. Fixtures regenerated in ${FIXTURES_DIR}"
echo "   (chunks{2,4,8}_{step,wrap}_main_circuit.json + companions)"
