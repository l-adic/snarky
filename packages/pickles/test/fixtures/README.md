# Pickles OCaml-side fixtures

## What the automated tests need

**Nothing committed here.** The pickles test suite (`spago test -p
pickles`) runs a full prove flow and asserts proofs validate via
`ProofFFI.verifyOpeningProof` — it does not read any file under this
directory. You can delete everything here and `spago test` will still
pass.

## What's in this directory

| Location | Contents | Consumer | Tracked in git? |
|---|---|---|---|
| `*.trace` | `[LABEL] VALUE` transcripts from the OCaml dumpers | `tools/*_trace_diff.sh` (manual convergence debugging) | **gitignored** — regenerate with `tools/regen-fixtures.sh trace` |
| `witness/ocaml_{step,wrap}_b{0,1}.txt` | 15-column kimchi witness matrices from `dump_simple_chain.exe` | `tools/witness_diff.sh` | yes |

The witness matrices are stable — they only change if Mina's circuit
structure or the kimchi witness format changes, which is rare. They're
committed so the convergence-debugging workflow works without a
full OCaml build. The `.trace` transcripts change every time someone
adds a trace point on either side; committing them creates noisy
diffs for no test benefit.

## Regenerating

All fixtures regenerate via `tools/regen-fixtures.sh`:

```sh
tools/regen-fixtures.sh all      # everything (default)
tools/regen-fixtures.sh trace    # just the .trace files (gitignored)
tools/regen-fixtures.sh witness  # just the witness matrices (committed)
tools/regen-fixtures.sh nrr      # No_recursion_return trace
tools/regen-fixtures.sh simple   # Simple_chain trace + witnesses
tools/regen-fixtures.sh tree     # Tree_proof_return trace
```

Prerequisites (nix, mina submodule, kimchi-stubs static lib) are
documented in the script header.

If a `git diff` on `witness/` shows unexpected deltas, something
changed in Mina's circuit layout — don't commit without understanding
why.
