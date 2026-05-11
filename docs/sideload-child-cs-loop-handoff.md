# Side-loaded child CS byte-identity loop — handoff doc

Self-contained brief for a fresh Claude session. After `/clear`, point me
at this file: "read `docs/sideload-child-cs-loop-handoff.md` and proceed
with iteration 0."

## Goal

Achieve byte-for-byte equality between PureScript and OCaml constraint
systems for the **side-loaded child** circuit (the inner `No_recursion`
proof verified by the parent in `dump_side_loaded_main.ml:75-96`). This
is the only outstanding sub-circuit on the side-loaded path that does
not yet have a `pickles-circuit-diffs` byte-identity test.

Once this CS lands byte-identical, the same rule body gets transcribed
into the prove-time `Test.Pickles.Prove.SideLoadedMain.noRecursionInputRule`
(currently a 1-line placeholder missing `dummy_constraints()`),
unblocking the witness convergence loop M9 — diff PS dumps against the
committed `packages/pickles/test/fixtures/witness_sideload/ocaml_*.txt`
fixtures.

## Why this milestone is the right sequencing

CS byte-identity is the precondition for witness byte-identity.
Same-CS + same-RNG-seed (`KIMCHI_DETERMINISTIC_SEED=42`) is a
sufficient condition for byte-identical witnesses on this codebase —
proven by Simple_chain b0+b1, NRR step+wrap, and Tree_proof_return
NRR + b0..b4 step+wrap. Trying to converge witnesses while CS shape
diverges is wasted iteration: every CS-shape change cascades through
all 6495+ rows of the witness, and you can't tell witness bugs from
CS bugs.

## Concrete deliverable

A new test in `pickles-circuit-diffs` named
`step_main_side_loaded_child_circuit matches OCaml` that passes
alongside the existing 85.

## Where things stand (most recent commits)

- `e33104ab` — M7b: parent prove with InductivePrev + FOP `[0..16]`
  synthesis. All 85 circuit-diffs + 11 pickles tests pass.
- `d91393b8` — M7a: per-prove vkCarrier on StepInputs/BranchProver.
- `01e1850b` — M6: route runtime VK through StepAdvice.

The PS primitives are correct — proven by the 85 sub-circuit
byte-identity tests. Any divergence in the new test is a call-site
composition bug, not a primitive bug.

## Iteration loop

Each iteration has one objective: shrink the first divergence. Same
shape as the Simple_chain iter 1..7 loop in memory.

### Iteration 0 — bootstrap (one-shot setup)

**Step A — OCaml dumper:** append `step_main_side_loaded_child` to
`mina/src/lib/crypto/pickles/dump_circuit_impl.ml`. Template:
`step_main_no_recursion_return` at lines 3981-4057. Two diffs from
the template:
- `~public_input:(Input Field.typ)` instead of `Output`.
- Body: `dummy_constraints () ; Field.Assert.equal self Field.zero ;`
  — verbatim copy from `dump_side_loaded_main.ml:88-89`.

The `dummy_constraints` body is at `dump_side_loaded_main.ml:49-73`;
copy it into `dump_circuit_impl.ml` as a private helper near the
existing `step_main_*` definitions (or inline).

Register at the bottom near line 5060:
```ocaml
dump_step_main output_dir "step_main_side_loaded_child_circuit"
  step_main_side_loaded_child
```

**Step B — build + run OCaml dumper.** No nix needed — the binary
builds directly with the pre-built kimchi-stubs static lib:
```sh
cd /home/martyall/code/l-adic/snarky/mina
dune build src/lib/crypto/pickles/dump_circuit/dump_circuit.exe
KIMCHI_DETERMINISTIC_SEED=42 \
  ./_build/default/src/lib/crypto/pickles/dump_circuit/dump_circuit.exe \
  ../packages/pickles-circuit-diffs/circuits/ocaml/
```
Expected: four new files in `circuits/ocaml/`:
- `step_main_side_loaded_child_circuit.json`
- `step_main_side_loaded_child_circuit_cached_constants.json`
- `step_main_side_loaded_child_circuit_gate_labels.jsonl`
- `step_main_side_loaded_child_circuit_labels.jsonl`

**Step C — PS rule.** Add
`packages/pickles-circuit-diffs/src/Pickles/CircuitDiffs/PureScript/StepMainSideLoadedChild.purs`.
Template = `StepMainNoRecursionReturn.purs`. Differences:
- Switch to Input mode (input = `Field`, output = `Unit`).
- Inline a `dummyConstraints` block with 5 lines copying OCaml
  `dump_side_loaded_main.ml:49-73` 1:1, calling existing PS
  primitives:
  - `exists Field.typ ~compute:(fun () -> 3)` → `exists (pure (F (fromInt 3)))`.
  - `exists Step_main_inputs.Inner_curve.typ ~compute:(...)` →
    `exists (pure innerCurveGen)` where `innerCurveGen` is the Pallas
    generator's affine coordinates as a curve point in the step circuit.
  - `Scalar_challenge.to_field_checked' ~num_bits:16 (SC.create x)` →
    use whatever PS primitive is exported for that path (find via
    `grep "to_field_checked\|toField" packages/pickles/src/Pickles/`).
  - `Step_main_inputs.Ops.scale_fast g ~num_bits:5 (Shifted_value x)`
    ×2 → `scaleFast2 @5 g (toShifted x)` ×2 (or whatever the existing
    primitive's call shape is — check `packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/VarBaseMul.purs`).
  - `Step_verifier.Scalar_challenge.endo g ~num_bits:4 (SC.create x)`
    → use the EndoMul-gate-emitting primitive (see
    `packages/snarky-kimchi/src/Snarky/Constraint/Kimchi/EndoMul.purs`).

Wrap each segment in `label "..." $ do ...` matching OCaml's
`with_label "..." (fun () -> ...)` boundaries (visible in
`dump_side_loaded_main.ml`'s context).

**Step D — wire into circuit-diffs test.** Add a one-line `it ...`
under the "Step main" `describe` block in
`packages/pickles-circuit-diffs/test/Test/Pickles/CircuitDiffs/Main.purs`.

**Step E — first run, expect failure.**
```sh
PATH="/home/martyall/.nvm/versions/node/v23.11.1/bin:$PATH" \
  npx spago test -p pickles-circuit-diffs -- --example "side_loaded_child"
```

Iteration 0 done. The harness emits a JSON diff with the first
diverging gate index + side-by-side gate dump.

### Iteration N (N ≥ 1) — shrink the divergence

**Step 1 — localise.** Read the failure output. It tells you
`first divergence at gate G` plus the PS label and OCaml label for
that gate.

**Step 2 — rule out primitive bugs via the existing 85 tests.** If
the diverging label is inside one of these passing sub-circuits, the
primitive is correct; the bug is at the call site:

| Diverging label region | Pre-existing green test |
|---|---|
| `endo_mul` / EndoMul gate | `endo_mul_step_circuit matches OCaml` ✓ |
| `scale_fast2` / `var_base_mul` | `scale_fast2_128_step_circuit`, `var_base_mul_step_circuit` ✓ |
| `add_complete` | `add_complete_step_circuit` ✓ |
| `poseidon` / sponge | `poseidon_step_circuit` ✓ |
| `to_field_checked` / scalar challenge | `endo_scalar_step_circuit` ✓ |
| `pow2_pow` | `pow2_pow_step_circuit` ✓ |
| `bullet_reduce_*` / `ftcomm` / `group_map` / `b_correct` / `xhat` / `hash_messages_*` | All ✓ |
| `finalize_other_proof` (incl. SideLoadedMode) | `finalize_other_proof_step_circuit` ✓ |
| `step_verify`, `full_step_verify_one`, `wrap_verify`, `wrap_main`, etc. | All ✓ |

If the label is inside one of these green tests, **do not hypothesize
a bug in that primitive**. The bug is at the call site. Common call-
site bugs:
- Wrong `num_bits` type-app (e.g. `@5` instead of `@4`).
- Missing/extra `Shifted_value` wrapper.
- Missing/extra `Scalar_challenge.create` wrapper.
- Missing `seal`.
- Wrong order of two operations (PS's `traverse` is left-to-right;
  OCaml's `Vector.map` is right-to-left for record-field constructors —
  see the existing `Vector.reverse … Vector.reverse` patterns in FOP).
- Wrong `~compute` callback shape on `exists`.

**Step 3 — fix the call site.** Most likely target is
`StepMainSideLoadedChild.purs`. If the divergence is in the
surrounding `step_main` scaffolding, target `Pickles.Step.Main.purs`
— but that path already byte-matches via
`step_main_side_loaded_main_circuit ✓`, so unlikely.

**Step 4 — re-run.**
```sh
npx spago test -p pickles-circuit-diffs -- --example "side_loaded_child"
```
The first divergence index should advance further into the gate
stream. If it didn't advance, the fix was wrong; revert and
re-localise.

**Step 5 — small commits per substantive fix** so iteration count is
trackable. Commit message format: `sideload child CS iter N: <one-line fix description>`.

Repeat until 0 divergences.

### Once CS test passes — bridge to witness loop (M9)

1. Copy the same rule body (with `dummyConstraints` block) from
   `StepMainSideLoadedChild.purs` into
   `Test.Pickles.Prove.SideLoadedMain.noRecursionInputRule`.
2. Run pickles tests:
   ```
   npx spago test -p pickles -- --example "SideLoadedMain"
   ```
   Existing `Pickles.Prove.SideLoadedMain.parent prove with InductivePrev`
   should still pass (CS shape change is internal to the child).
3. Re-run with witness dump:
   ```
   KIMCHI_DETERMINISTIC_SEED=42 \
     KIMCHI_WITNESS_DUMP=/tmp/ps_sl_%c.witness \
     npx spago test -p pickles -- --example "SideLoadedMain"
   ```
4. Diff each counter:
   ```
   for pair in "child_step_b0:0" "child_wrap_b0:1" "main_step_b1:2" "main_wrap_b1:3"; do
     name="${pair%:*}"; idx="${pair#*:}"
     tools/witness_diff.sh \
       "packages/pickles/test/fixtures/witness_sideload/ocaml_${name}.txt" \
       "/tmp/ps_sl_${idx}.witness"
   done
   ```
5. M9 starts: same loop shape, but over witness rows instead of CS
   gates. Use `KIMCHI_STEP_LABELS_DUMP=/tmp/ps_step_labels_%c.txt` to
   get a row→label cross-reference.

## Key reminders

- **OCaml fidelity directive**: never invent, always translate.
  `dump_side_loaded_main.ml:49-73` `dummy_constraints` body is the
  source of truth; PS transcribes 1:1.
- **Use labels aggressively.** Every `do` block in the new PS rule
  should be wrapped in `label "name" $ do ...` for the same
  boundaries OCaml's `with_label`s create. The harness emits
  row→label JSONLs on both sides.
- **OCaml right-to-left evaluation order** is the most common source
  of subtle order divergences. PS's `traverse` and `Vector.map` are
  left-to-right; OCaml is right-to-left for record fields and `::`
  constructors. The existing FOP code uses `Vector.reverse` shims at
  exactly these boundaries.
- **Don't run `nix develop` for the OCaml dump.** The pre-built
  executable at
  `mina/_build/default/src/lib/crypto/pickles/dump_circuit/dump_circuit.exe`
  works directly. The kimchi-stubs static lib is staged at
  `/tmp/local_kimchi_stubs/lib/libkimchi_stubs.a` (set up earlier in
  the session for the witness diff work).
- **Don't propose changes to `MkUnitVkCarrier` / `RuleEntry` /
  `StepAdvice` / FOP architecture** — those are settled. Subsequent
  changes are localized to the new `StepMainSideLoadedChild.purs`
  rule and call-site fixes.
- **Skill reference**: `.claude/skills/kimchi-circuit-json-comparison/SKILL.md`
  has the row-label cross-reference recipe written out — re-read at
  start of session.

## Files to read at session start

1. This file.
2. `docs/sideload-witness-loop-handoff.md` — the predecessor handoff
   covering M5/M6 setup. Skim only.
3. `mina/src/lib/crypto/pickles/dump_side_loaded_main.ml` (lines
   49-110) — OCaml source of truth for child rule body and
   dummy_constraints.
4. `mina/src/lib/crypto/pickles/dump_circuit_impl.ml` (lines
   3981-4057) — `step_main_no_recursion_return` template for OCaml
   dumper entry.
5. `packages/pickles-circuit-diffs/src/Pickles/CircuitDiffs/PureScript/StepMainNoRecursionReturn.purs`
   — PS template for `StepMainSideLoadedChild.purs`.
6. `packages/pickles-circuit-diffs/test/Test/Pickles/CircuitDiffs/Main.purs`
   — registration site.
7. `.claude/skills/kimchi-circuit-json-comparison/SKILL.md` — debug
   recipes.
