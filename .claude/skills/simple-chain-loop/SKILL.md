---
name: simple-chain-loop
description: Iteratively build out the PureScript step prover for the Pickles `Simple_chain` test by diffing transcript logs against the OCaml fixture, fixing one divergence per iteration, until the traces match byte-for-byte or a fundamental obstruction is hit. The loop is the test infrastructure built in commits 0292b512..5389ac7b.
---

# Simple_chain trace-diff iteration loop

This is the operating procedure for closing the gap between OCaml's
`Simple_chain` step prover (the source of truth) and the PureScript
analog driven by `Test.Pickles.Prove.SimpleChain`. Each iteration is a
single tight cycle: **read the diff, fix the topmost divergence, run
the diff again, commit progress, schedule next.**

## Hard requirements (from the user)

1. **Generic circuits only.** No code in `packages/pickles/src/` may
   hard-code anything specific to `Simple_chain` — not the
   max-proofs-verified count, not the slot widths, not the public
   input shape, not the rule count. Every helper / function / type
   added to `src/` must be polymorphic over those parameters. The
   ONLY place concrete values are allowed is the test-side file
   `packages/pickles/test/Test/Pickles/Prove/SimpleChain.purs` (and
   `mina/.../dump_simple_chain/dump_simple_chain.ml` on the OCaml side).
2. **OCaml is the source of truth.** Use the ocamllsp MCP tools
   (`mcp__ocamllsp__hover`, `mcp__ocamllsp__diagnostics`,
   `mcp__ocamllsp__definition`, `mcp__ocamllsp__references`,
   `mcp__ocamllsp__edit_file`, `mcp__ocamllsp__rename_symbol`) as the
   primary way to inspect OCaml source — they're faster than merlin
   CLI (no nix-develop startup) and `hover` returns type + docstring.
   Fall back to `tools/merlin_type.sh` only when the MCP can't answer.
   Never guess. Cite OCaml file paths + line numbers in commit
   messages and in PureScript comments next to every translated piece.
3. **Use the OCaml-emitted transcript logs.** The fixture at
   `packages/pickles/test/fixtures/simple_chain_base_case.trace` is
   ground truth; the diff against
   `tools/simple_chain_trace_diff.sh` output drives every fix. Do
   not "fix" PureScript values to match guesses — fix them to match
   the fixture.

## Termination conditions

Stop the loop when EITHER:

- **Match.** `tools/simple_chain_trace_diff.sh` exits 0 (traces are
  byte-identical). Commit the final state and report success.
- **Fundamental obstruction.** Any of:
  - The same divergence persists across two consecutive iterations
    (you fixed something, but the diff didn't budge — a sign you're
    looking at the wrong source location).
  - A required OCaml internal is genuinely not exposed to the
    library boundary (e.g., a private functor field that needs a
    Pickles_intf.S addition you don't have authority to make).
  - A genericity violation can't be avoided (you'd have to import
    `simple_chain.ml`-specific code into `packages/pickles/src/`).
  - Build breaks somewhere in the workspace and stays broken across
    a fix attempt.

  When obstruction is hit: commit whatever progress exists, write a
  clear obstruction report (what, where, why, what you tried), and
  stop the loop.

## Per-iteration cycle

```
1. Read state
   - Run tools/simple_chain_trace_diff.sh
   - Capture: line counts, top of diff, exit code
   - Read the topmost divergence (missing or differing line)

2. Locate ground truth
   - From the diff, identify the label (e.g. "step.proof.public_input.5")
   - Find where OCaml emits this label:
       grep -rn '"step.proof.public_input"' mina/src/lib/crypto/pickles/
   - Read the OCaml source around the trace point.
   - For any unfamiliar identifier, **hover via the ocamllsp MCP**:
       mcp__ocamllsp__hover(
           filePath = "/home/martyall/code/l-adic/snarky/mina/src/lib/crypto/pickles/step.ml",
           line     = <line>,
           column   = <col>,
       )
     Returns the type signature + docstring. Workhorse query for the
     loop. Fall back to `tools/merlin_type.sh` only when hover doesn't
     resolve.
   - For "where is this symbol defined / used" questions, grep first
     (the MCP's `definition`/`references` tools are name-keyed and
     don't always resolve module-qualified identifiers — see the
     `ocaml-analysis-tools` skill for details).
   - For "does this file currently compile cleanly" checks, call
     `mcp__ocamllsp__diagnostics(filePath)` before proceeding.
   - Note: file path + line numbers + the type / shape of the value
     being traced. These go in the commit message and PS comment.

3. Find / build the PureScript equivalent
   - First check if there's an existing polymorphic helper in
     packages/pickles/src/Pickles/* that already computes the same
     value. Use grep / Pickles.* module structure.
   - If yes: call it from SimpleChain.purs (or wire it through the
     test-side advice helpers).
   - If no: add a NEW polymorphic helper in packages/pickles/src/.
     The helper must be parameterized so that Simple_chain at
     max_proofs_verified=1 is just one instantiation; the same
     helper must work for N2, N0, etc. Read the merlin types and
     the Pickles_intf.S signatures to ensure the parameterization
     matches OCaml's.

4. Add the trace point in PureScript
   - Use Pickles.Trace.field / .point / .fieldsArray / etc. with
     EXACTLY the same label string the OCaml side uses. Labels are
     semantic and dot-separated; never invent new labels at this
     stage — only mirror existing OCaml labels.

5. Build + run
   - `npx spago build -p pickles`
     If it fails: fix the build error first, do NOT proceed to the
     diff while the workspace is broken.
   - `tools/simple_chain_trace_diff.sh`
     Inspect the new diff state.

6. Decide
   - If diff line count strictly decreased OR a previously-divergent
     value now matches: commit the iteration with a clear message
     citing the OCaml source.
   - If diff is unchanged: revert this iteration's changes (or fix
     the missing wiring), do not commit a no-op.
   - If diff is now CLEAN: commit, mark loop complete, stop.
   - If diff got WORSE: revert, examine the iteration for an
     introduced bug, retry differently.

7. Schedule next
   - If still not done and no obstruction: ScheduleWakeup with the
     `<<autonomous-loop-dynamic>>` sentinel, ~60s, reason describing
     the next divergence to attack.
   - If obstruction or done: do not reschedule.
```

## Genericity discipline

Every PureScript change in `packages/pickles/src/` must be reviewable
through this lens:

> "If I changed `Simple_chain`'s `max_proofs_verified` from `N1` to
> `N2`, would this code still compile and behave correctly?"

If the answer is no, the code is too specific. Fix:

- Replace concrete `Vector 1 a` with `Vector n a` (using `Reflectable n Int`
  if you need the runtime value).
- Replace hard-coded `34` (= 1*32 + 1 + 1) with type-level arithmetic
  via `Add` / `Mul` constraints from `Prim.Int`.
- Replace specific module imports like `Test.Pickles.Prove.SimpleChain.<X>`
  with polymorphic helpers in `Pickles.<area>`.

Test instantiation is the test file's job, not the helper's.

## OCaml-side scratchpad (don't add to fixture without rerunning)

If during an iteration you discover that a divergence is most
diagnosable by adding more granular trace points on BOTH sides:

- **Add the OCaml trace point via `mcp__ocamllsp__edit_file`** (or
  directly via the `Edit` tool for small, targeted diffs). The MCP
  edit path accepts a list of `{startLine, endLine, newText}` edits
  applied atomically — convenient when a single logical change
  touches several locations in the same file.
- **Verify no build breakage** by calling
  `mcp__ocamllsp__diagnostics(filePath)` on the edited file. If
  there are any errors, fix them before proceeding — don't trust
  the downstream `dune build` to surface clean error messages for
  OCaml issues the LSP already knows about.
- Rebuild kimchi-stubs locally (`~/.cargo/bin/cargo build -p kimchi-stubs --release` from `mina/src/lib/crypto/proof-systems/`, copy to `/tmp/local_kimchi_stubs/lib/`). Pickles-library changes don't require this (only changes to the Rust stubs do), but if you DID touch kimchi-stubs, this step is mandatory.
- Re-run `tools/simple_chain_trace_diff.sh` so the OCaml side regenerates the trace file with the new point.
- Add the matching PureScript trace point via Pickles.Trace.
- The fixture file at `packages/pickles/test/fixtures/simple_chain_base_case.trace` is REGENERATED automatically by the diff script (it actually writes to `/tmp/simple_chain_ocaml.trace`); commit the fixture explicitly only when both sides converge.

## Common pitfalls

- **Do not run the diff with stale builds.** The diff script rebuilds
  PureScript via `spago test -p pickles` but the OCaml side needs the
  patched kimchi-stubs at `/tmp/local_kimchi_stubs/lib/libkimchi_stubs.a`
  to be up-to-date. If you change `mina/.../*.ml` files, also rebuild
  kimchi-stubs and re-stage the lib BEFORE running the diff.
- **Do not mistake spago's stale cache for a fix.** When you change
  PureScript files, run `npx spago build -p pickles` separately to
  surface compile errors before the test runner swallows them.
- **Do not commit a no-op iteration.** If the diff didn't change,
  there is no progress to commit.
- **Do not edit the OCaml fixture by hand.** It's regenerated by
  re-running `dump_simple_chain.exe`.
- **Never use `--no-verify` or `panic=abort` workarounds.** Fix root
  causes.
