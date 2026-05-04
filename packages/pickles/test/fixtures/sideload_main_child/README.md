# sideload_main_child fixture

OCaml-produced VK + wrap proof + statement + Pickles wrapping for the
side-loaded child of `dump_side_loaded_main.ml` — i.e., the `No_recursion`
program (mpv = N0, public input = Field, asserts `self == 0` after
`dummy_constraints ()`).

PS's `Test.Pickles.Sideload.Loader.loadFixture` consumes this directory
unchanged. It is the runtime data the side-loaded slot of `Simple_chain`
(parent rule) needs at prove time — analogous to OCaml's handler:

```ocaml
let%bind.Promise vk =
  Side_loaded.Verification_key.of_compiled_promise No_recursion.tag in
step ~handler:(handler No_recursion.example_input
                       (Side_loaded.Proof.of_proof No_recursion.example_proof)
                       vk)
     Field.Constant.one
```

## Files

- `vk.serde.json`    — kimchi `VerifierIndex` (Fq codec, 21 top-level keys).
                       Used by PS as `vestaVerifierIndexFromSerdeJson`'s input.
- `proof.serde.json` — kimchi proof_with_public (Fq codec, 5 top-level keys),
                       with `prev_challenges` already populated via
                       `Wrap_hack.pad_accumulator`. Loaded by PS via
                       `vestaProofFromSerdeJson`; no reconstruction.
- `wrapping.json`    — Pickles wrapping fields not in the kimchi proof:
                       deferred-values, branch_data, sponge digest,
                       prev_evals, redundant wire_proof bytes. yojson_full.
- `statement.json`   — public state: a single field encoded as a hex string.
                       For this fixture, the value is `Field.Constant.zero`
                       (= the public input passed to `step` per
                       `dump_side_loaded_main.ml:103`).

## Schema

Identical to `packages/pickles/test/fixtures/sideload/nrr/` — same four
file names, same JSON shapes, same Rust serde codec for the kimchi
artefacts. PS's loader needs no changes to consume either.

## Reconstructed PS-side, NOT in fixture

Two pieces of `Side_loaded.Verification_key.t` are reconstructed from
the kimchi VK + static rule metadata, so they are **deliberately
absent** from the fixture:

- `actual_wrap_domain_size`: derived from `vk.domain.log_size_of_group`
  via `Common.actual_wrap_domain_size`, mirroring `compile.ml:1031-1032`.
- `max_proofs_verified`: static rule property; for this fixture's
  No_recursion child, it is `N0` (baked into the consuming PS test as
  a type-level parameter).

Any disagreement between OCaml's `of_compiled_promise` and the PS-side
reconstruction will surface as a witness divergence in the side-loaded
witness diff loop, which is the desired failure mode (sharp signal, no
silent masking by duplicated fixture fields).

## Regenerating

From the repo root, with the nix shell:

```
mkdir -p packages/pickles/test/fixtures/sideload_main_child
nix develop mina#default -c bash -c '
  cd mina && \
  KIMCHI_DETERMINISTIC_SEED=42 \
  SIDELOAD_FIXTURE_DIR=../packages/pickles/test/fixtures/sideload_main_child \
  KIMCHI_WITNESS_DUMP=../packages/pickles/test/fixtures/witness_sideload/witness_%c_regen.txt \
  _build/default/src/lib/crypto/pickles/dump_side_loaded_main/dump_side_loaded_main.exe'
```

The seed pins the kimchi RNG so successive regenerations are bit-identical.
The same run also rewrites the `witness_sideload/` golden dumps if the
`KIMCHI_WITNESS_DUMP` template above is used (the existing golden dumps
must continue to match these JSON fixtures, since both come from the
same OCaml run).

## See also

- `packages/pickles/test/fixtures/witness_sideload/` — the four kimchi
  witness golden dumps from the same OCaml run; counter 2
  (`ocaml_main_step_b1.txt`) is the convergence target.
- `mina/src/lib/crypto/pickles/dump_side_loaded_main/dump_side_loaded_main.ml`
  — the OCaml binary that produces both this directory and
  `witness_sideload/`.
- `Test.Pickles.Sideload.Loader.loadFixture` — the PS reader; should
  consume this directory unchanged.
