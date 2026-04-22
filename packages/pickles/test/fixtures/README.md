# Pickles OCaml-side fixtures

These files are dumped by the OCaml pickles implementation and pinned
in-tree as **ground truth** for the PureScript byte-identity tests.

## What's here

| File | Producer | What the PS side compares against |
|---|---|---|
| `no_recursion_return_base_case.trace` | `dump_no_recursion_return.exe` | `Test.Pickles.Prove.NoRecursionReturn` |
| `simple_chain_base_case.trace` | `dump_simple_chain.exe` | `Test.Pickles.Prove.SimpleChain` |
| `tree_proof_return_base_case.trace` | `dump_tree_proof_return.exe` | `Test.Pickles.Prove.TreeProofReturn` |
| `witness/ocaml_step_b{0,1}.txt` | `dump_simple_chain.exe` + `KIMCHI_WITNESS_DUMP` | kimchi witness matrices the step proof solves |
| `witness/ocaml_wrap_b{0,1}.txt` | same | kimchi witness matrices the wrap proof solves |

The `.trace` files are `[LABEL] DECIMAL_VALUE` lines emitted by
`mina/src/lib/crypto/pickles/pickles_trace.ml` during a real OCaml
prove-flow; the `Pickles.Trace` module on the PS side emits the same
labels so the two files can be `diff`-ed.

## Why they're committed

Regenerating them requires:

- a nix environment (`mina#default` flake) to build the OCaml dumpers,
- a cargo toolchain to build the `kimchi-stubs` static lib with the
  deterministic-RNG patch applied,
- the mina submodule checked out at a specific revision.

None of those are available in CI. Committing the fixtures lets CI
run the byte-identity tests without touching OCaml.

## Regenerating

Use the script at the repo root:

```sh
tools/regen-fixtures.sh          # all fixtures
tools/regen-fixtures.sh trace    # just the .trace files
tools/regen-fixtures.sh witness  # just the witness matrices
tools/regen-fixtures.sh simple   # Simple_chain trace + witness
tools/regen-fixtures.sh tree     # Tree_proof_return trace
tools/regen-fixtures.sh nrr      # No_recursion_return trace
```

Prerequisites and step-by-step setup are documented in the script's
header comment.

After a regen, review with:

```sh
git diff --stat packages/pickles/test/fixtures/
git diff packages/pickles/test/fixtures/
```

The diff should make intuitive sense given whatever OCaml-side change
motivated the regen. If it doesn't, something broke upstream — don't
commit.
