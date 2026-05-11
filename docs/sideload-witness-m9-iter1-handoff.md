# Sideload main_step witness — M9 iter 1 findings

Self-contained handoff for resuming the sideload main_step witness
convergence loop.

## State after iter 1 (2026-05-06)

Loop tool: `tools/sideload_witness_diff.sh`. 4-counter run:

| Counter | Tag         | Result               |
|---------|-------------|----------------------|
| 0       | child_step  | byte-identical       |
| 1       | child_wrap  | byte-identical       |
| 2       | main_step   | **diverges at PI[32]** |
| 3       | main_wrap   | full cascade         |

Diff output: `/tmp/sl_witness_main_step.diff` (68759 lines diverging).

## First divergence

Row 32 col 0 is the `messages_for_next_step_proof` digest (the parent's
step PI layout: rows 0–31 = `unfinalized_proofs[0]` (32 fields), row 32
= digest, row 33 = `messages_for_next_wrap_proof[0]`). Rows 0–31 and
row 33 match — PS's `unfinalized_proofs[0]` for the side-loaded prev
is correct.

The cascade:

- Rows 110–130 diverge inside `exists_wrap_index` (parent's own wrap VK
  point-on-curve squares). The wrap VK commitments PS allocates as
  runtime advice differ from OCaml's.
- Rows 417+ diverge inside `prevs_verified/slot_0/scalar_challenge`
  (downstream of the differing VK).

Conclusion: PS feeds different wrap VK commitment values than OCaml
when proving the parent step. Wrap CS is byte-identical (per existing
`wrap_main_side_loaded_main_circuit` fixture, commit `036bc530`), so
the commitments derived from compiling that CS *should* match. They
don't.

## Why this is interesting (and probably tractable)

Both sides:

- Compile byte-identical wrap CS for the parent.
- Use the same patched kimchi crate (workspace path).
- Use the same chacha8 RNG seed (42).
- Run the same kimchi VK derivation algorithm.

But child b0 step+wrap converged byte-identical, so RNG state at the
end of child prove matches OCaml. So the divergence kicks in either:

1. During parent compile (after child compile+prove), where PS
   advances the RNG state differently from OCaml.
2. During parent step prove (when the wrap VK commitments are pushed
   into `exists_wrap_index` as advice), where PS extracts commitments
   from a different source than what the parent's compiled wrap VK
   contains.

## Hypotheses (in decreasing likelihood)

1. **PS extracts wrap VK commitments via a different code path for
   side-loaded specs.** `extractWrapVKCommsAdvice` is called for
   compiled External slots (`Pickles.Prove.Compile.purs:814`), but for
   the parent's OWN wrap VK exists in step circuit, the path is
   different. Check whether the SideLoadedMain spec routes the parent
   wrap VK through a different extraction than Simple_chain N1 would.

2. **Order of FFI calls differs between PS and OCaml.** OCaml's
   `compile_promise` does a specific sequence of kimchi-side-effects
   that PS's `compileMulti` mirrors approximately. If even ONE extra
   FFI call exists on the PS side after the child prove (e.g.
   `pallasSrsBPolyCommitmentPoint` for some advice), the chacha8 RNG
   advances differently, shifting the wrap VK derivation.

3. **PS's parent.vks.wrap.verifierIndex is stale or wrong.** Maybe
   `compileMulti` for the SideLoadedMain shape has a bug where the
   wrap VK exposed via `output.vks` is not the one actually used at
   prove time, or vice versa.

## How to make iter 2 productive

Add tracing to PS step prove to dump the wrap VK commitments fed into
`exists_wrap_index` (X+Y of all 7 sigma + 15 coeff + 6 idx
commitments). OCaml side already has this via `Pickles_trace`
(`step_main_outer.vk.sigma.{i}.x` etc.) — the trace label is at
`Pickles.Step.Main.purs:1039`.

If `PICKLES_TRACE_FILE` is set on both sides, comparing the
`step_main_outer.vk.*` lines should show the first commitment that
diverges. From there, walk backwards in the parent compile pipeline
to find where the VK is constructed.

Key files to inspect:

- `Pickles.Prove.Compile.purs` lines 814, 859, 1158 — VK extraction
  for non-self/external slots vs self.
- `Pickles.Step.Main.purs:799` — `exists_wrap_index` invocation.
- `Pickles.Prove.Step.purs` — step prove pipeline; where
  `wrapVkAdvice` is fed.

## Sanity check

Run the loop:
```
bash tools/sideload_witness_diff.sh
```
Expected: child_step, child_wrap match; main_step, main_wrap diverge.
First divergence is at `(col=0, row=32)`. If a different row diverges,
the cascade has shifted (different bug) — start from the new first
divergence.
