# Pickles OCaml-side fixtures

## What the automated tests need

**Nothing in this directory is tracked in git, and CI doesn't read any
of it.** The pickles test suite (`spago test -p pickles`) runs a full
prove flow for each test and asserts proofs validate via
`ProofFFI.verifyOpeningProof` (kimchi batch_verify). Compile →
solve → prove → verify, all in-process. No file I/O into this
directory.

## What lives here when it's populated

| Path | Contents | Consumer |
|---|---|---|
| `*.trace` | `[LABEL] VALUE` transcripts from the OCaml dumpers | `tools/*_trace_diff.sh` |
| `witness/ocaml_{step,wrap}_b{0,1}.txt` | 15-column kimchi witness matrices from `dump_simple_chain.exe` | `tools/witness_diff.sh` |

Both families are **developer convergence-debugging artifacts only**.
Regenerate via `tools/regen-fixtures.sh` when you need them:

```sh
tools/regen-fixtures.sh all      # everything
tools/regen-fixtures.sh trace    # just the .trace files
tools/regen-fixtures.sh witness  # just the witness matrices
tools/regen-fixtures.sh nrr      # No_recursion_return trace
tools/regen-fixtures.sh simple   # Simple_chain trace + witnesses
tools/regen-fixtures.sh tree     # Tree_proof_return trace
```

Prerequisites (nix, mina submodule, kimchi-stubs static lib) are
documented in the script header.

## Why nothing is tracked

The `.trace` transcripts change any time someone adds a trace point
on either side — they create noisy diffs for no test benefit. The
witness matrices are more stable, but CI doesn't need them either:
they only serve the manual `tools/witness_diff.sh` convergence tool
that runs locally during debugging. Committing ~16 MB of data that no
test reads is pure cost.
