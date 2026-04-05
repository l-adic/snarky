# Agentic Loop: wrap_main Circuit Diff Convergence

## Goal

Drive the wrap_main circuit to exact match with OCaml (0 diffs) by fixing one discrepancy at a time. The loop has two phases: Phase 1 fixes constraint (kind+coeff) differences, Phase 2 fixes wiring differences.

## Progress Metric & Commit Policy

**Commit if and only if** the first-difference index strictly increases (or the circuit reaches full match). "Abstract progress" does not count — only measurable advancement in the diff tools' output.

- **Phase 1 metric**: Gate row of first kind+coefficient difference (from `circuit-diff-summary.mjs`)
- **Phase 2 metric**: Gate row of first wire difference (from `circuit-wire-diff.mjs`)
- **Phase transition**: When `circuit-diff-summary.mjs` reports "All gates match exactly (kinds + coefficients)" but the test still reports "mismatch", switch to Phase 2.

## Regression Guard

These sub-circuit tests share library code with wrap_main and MUST continue to pass after any change:
- `finalize_other_proof_wrap_circuit` (FOP)
- `hash_messages_for_next_wrap_proof_circuit` (message hash)
- `ivp_wrap_circuit` / `wrap_verify_circuit` / `wrap_verify_n2_circuit` (IVP)
- `choose_key_n1_wrap_circuit`
- `one_hot_n1_wrap_circuit`, `pseudo_mask_n1_wrap_circuit`, `pseudo_choose_n1_wrap_circuit`

If a fix changes library code (anything outside `WrapMain.purs`), run all of these before committing. If a fix only changes `WrapMain.purs`, regression is unlikely but spot-check the FOP and IVP tests.

## Current State

- PS: 14,383 gates, OCaml: 14,514 gates (131 gap)
- First kind+coeff difference: **row 4787**, R1CS index 3887
- Context: PS `ivp_xhat > public-input-commit > add_fast`, OCaml `wrap_verify > ...`
- PS has Lagrange commitment coords as Const (cached constant assertions) where OCaml has them as Scale coefficients
- Gate types: Poseidon/Zero/CompleteAdd/EndoMul/EndoMulScalar/VarBaseMul all MATCH, only Generic differs (-131)
- Cached constants: PS 311, OCaml 287, shared 287, PS-only 24

### Recent fixes (row 487→4787):
1. **Pad prevChallenges** to N2 with constant dummy IPA challenges (matching wrap_hack.ml:82-87)
2. **Fix omega^-2** in FOP: `mul_` instead of `square_` (OCaml's plonk_checks uses `let square x = x * x`)
3. **Assert.any pattern**: `assertNonZero_(sum)` instead of `or_ + assert_` for FOP finalization check
4. **Swap message hash order**: proof 1 first (right-to-left Vector.map2 matching OCaml)
5. **Wire chooseKey output** into IVP columnComms (non-constant VK from Pseudo.mask + seal instead of Const)

## Key Files

### PureScript (modify)
- `packages/pickles-circuit-diffs/src/Pickles/CircuitDiffs/PureScript/WrapMain.purs` — top-level wiring
- `packages/pickles/src/Pickles/Wrap/FinalizeOtherProof.purs` — FOP library
- `packages/pickles/src/Pickles/Wrap/Verify.purs` — IVP wrapper
- `packages/pickles/src/Pickles/Wrap/MessageHash.purs` — message hash
- `packages/pickles/src/Pickles/Pseudo.purs` — pseudo-selection (toDomain, mask, choose)
- `packages/snarky/src/Snarky/Types/Shifted.purs` — splitField

### OCaml (read-only, use merlin/LSP — DO NOT reason about types manually)
- `mina/src/lib/crypto/pickles/wrap_main.ml` — reference implementation
- `mina/src/lib/crypto/pickles/wrap_verifier.ml` — FOP + IVP
- `mina/src/lib/crypto/pickles/pseudo/pseudo.ml` — pseudo-selection
- `mina/src/lib/crypto/pickles/util.ml` — seal definition (lines 68-76)
- `mina/src/lib/snarky/src/base/utils.ml` — Checked.mul/square (lines 80-110)

### Tools

All three circuit diff tools read the result JSON written by the test at `packages/pickles-circuit-diffs/circuits/results/wrap_main_circuit.json`. Run them on that file — never re-run the test just to get different analysis.

- **`tools/circuit-diff-summary.mjs <results-json>`** — Phase 1 primary tool. Reports first gate where kind or coefficients differ, gate type breakdown, cached constant analysis, and section-by-context breakdown. Use this to get `DIFF_ROW`.
  ```bash
  node tools/circuit-diff-summary.mjs packages/pickles-circuit-diffs/circuits/results/wrap_main_circuit.json
  ```

- **`tools/circuit-r1cs-diff.mjs <results-json> [context-lines]`** — Phase 1 deep dive. Unpacks Generic gates into individual R1CS in generation order (right half = first generated, left half = second). Finds the first R1CS divergence and decodes coefficient equations. Flags seal operations (constant in R1CS slot 5). The `context-lines` parameter controls how many surrounding R1CS to show (default 8).
  ```bash
  node tools/circuit-r1cs-diff.mjs packages/pickles-circuit-diffs/circuits/results/wrap_main_circuit.json 5
  ```

- **`tools/circuit-wire-diff.mjs <results-json> [context-lines]`** — Phase 2 primary tool. Finds first gate where wires differ. Shows which wire columns diverge and surrounding context. Warns if kind/coeff diffs still exist (wire debugging is premature). Reports total wire diff count.
  ```bash
  node tools/circuit-wire-diff.mjs packages/pickles-circuit-diffs/circuits/results/wrap_main_circuit.json 5
  ```

- **`tools/merlin_type.sh <file> <line> <col_start> <col_end>`** — OCaml type queries via merlin. **MUST use** for OCaml analysis. Requires nix shell.
  ```bash
  nix develop mina#default -c bash -c 'cd mina && tools/merlin_type.sh src/lib/crypto/pickles/wrap_verifier.ml 150 20 45'
  ```
- The `/ocaml-analysis-tools` skill invokes merlin properly within nix

### Test artifacts
- Result: `packages/pickles-circuit-diffs/circuits/results/wrap_main_circuit.json`
- OCaml fixture: `packages/pickles-circuit-diffs/circuits/ocaml/wrap_main_circuit.json`
- OCaml labels: `packages/pickles-circuit-diffs/circuits/ocaml/wrap_main_circuit_gate_labels.jsonl`

## CRITICAL: Seal Awareness

`seal` is the single most impactful operation for circuit equivalence. It converts a complex CVar expression into a single variable via `exists + assertEqual` (1 R1CS constraint + 1 cached constant).

### OCaml seal (mina/src/lib/crypto/pickles/util.ml:68-76)
```ocaml
let seal (x : Impl.Field.t) : Impl.Field.t =
  match Field.to_constant_and_terms x with
  | None, [ (x, i) ] when Field.Constant.(equal x one) -> Cvar.Var i  (* bare var: no-op *)
  | Some c, [] -> Field.constant c                                     (* constant: no-op *)
  | _ -> let y = exists ... in Field.Assert.equal x y ; y              (* complex: 1 R1CS *)
```

### PureScript seal (packages/snarky/src/Snarky/Circuit/DSL/Utils.purs:25-33)
```purescript
seal x = case constant, toUnfoldable terms of
  Nothing, Cons (Tuple v coeff) Nil | coeff == one -> pure $ Var v   -- bare var: no-op
  Just c, Nil -> pure $ const_ c                                     -- constant: no-op
  _, _ -> do y <- exists (readCVar x); assertEqual_ x y; pure y      -- complex: 1 R1CS
```

### Why seal matters everywhere

1. **Missing seal**: PS returns a complex CVar expression where OCaml seals it. Downstream `mul_` of the complex expression produces different R1CS coefficients than `mul_` of a sealed variable. The constraint is semantically equivalent but structurally different.

2. **Extra seal**: PS seals where OCaml doesn't. Produces extra R1CS constraints.

3. **Seal of const vs non-const**: `seal (const_ x)` is a no-op (returns `const_`). `seal (nonConstVar)` that happens to be a bare `Var` is also a no-op. But `seal (Scale c var)` or `seal (Add ...)` generates an R1CS. Whether an expression reaches seal as const, bare var, or complex depends on the entire computation chain.

4. **Implicit seals**: OCaml's `Field.Checked.mul` and `Field.Checked.square` are themselves seal-like: they `exists + assert_r1cs`. When both operands are non-constant, they generate R1CS. When one is constant, they return `Scale` (no R1CS). The const-vs-non-const distinction is the root cause of many gate count differences.

### Seal debugging protocol

At every divergence point, ask:
- Is PS producing a **constant** where OCaml has a **non-constant**? (Missing R1CS because `mul_` short-circuits to `Scale`)
- Is PS producing a **non-constant** where OCaml has a **constant**? (Extra R1CS)
- Is there an explicit `seal` call in one implementation but not the other?
- Does OCaml's `Util.Wrap.seal` appear in the context labels? (grep for `seal` in gate_labels.jsonl around the divergence row)
- Look at cached constants around the divergence: seal generates a constant value entry. The `circuit-r1cs-diff.mjs` tool flags when a divergent R1CS has a constant coefficient and searches cached constants for it.

## The Loop

### Step 0: Initialize
```bash
PREV_DIFF_ROW=<current first-diff row from circuit-diff-summary.mjs>
PHASE=1  # Start in Phase 1 (kind+coeffs)
```

### Step 1: Analyze the current first difference

```bash
# Use EXISTING result file — do NOT re-run tests yet
node tools/circuit-diff-summary.mjs packages/pickles-circuit-diffs/circuits/results/wrap_main_circuit.json
node tools/circuit-r1cs-diff.mjs packages/pickles-circuit-diffs/circuits/results/wrap_main_circuit.json 5
```

Extract:
- `DIFF_ROW`: gate row of first kind+coeff difference (Phase 1) or first wire difference (Phase 2)
- `PS_CTX` / `OC_CTX`: context labels at that row
- `DIFF_TYPE`: kind diff, coeff diff, or wire diff
- Examine 5-10 gates around the diff in both PS and OCaml

**Check for seal signatures**: If the R1CS diff shows a constant coefficient on one side (`c=<large number>`) and a multiplication on the other (`1*vo + -1*vl*vr`), this is almost certainly a seal mismatch. Note which side has the seal and which doesn't.

### Step 2: Identify responsible code on BOTH sides

**PureScript side**: Use PS context labels (e.g. `wrap-finalize-other-proof > step3_sgZeta > b-poly`) to find the code in WrapMain.purs or the sub-circuit. Read it.

**OCaml side**: Use OCaml context labels from `gate_labels.jsonl` to locate code in `wrap_main.ml` or `wrap_verifier.ml`.

**CRITICAL: Use merlin/LSP for OCaml analysis.** The code is functor-heavy and type inference is non-trivial.
```bash
# Example: query the type of an expression at wrap_verifier.ml line 150, cols 20-45
nix develop mina#default -c bash -c 'cd mina && tools/merlin_type.sh src/lib/crypto/pickles/wrap_verifier.ml 150 20 45'
```

Key merlin queries to make:
- Type of the domain generator expression (is it `Field.t` = in-circuit, or `Field.Constant.t` = pure?)
- Type of operands going into `mul`, `square`, `seal`
- Whether `Util.Wrap.seal` is called on the result

**Seal-specific checks**:
- Search for `seal` in the OCaml code within 20 lines of the divergence context
- Check if `Double.map ~f:Util.Wrap.seal` or similar patterns appear
- Check if the PureScript equivalent calls `seal` or `sealPoint` at the same point

### Step 3: Formulate a targeted fix

Based on the analysis, the fix will fall into one of these categories:

**A. Missing R1CS (PS has fewer gates)**: PS treats something as constant that OCaml treats as non-constant. Common cause: a value arrives as `const_` in PS but as an in-circuit variable in OCaml. Trace the value's origin — likely it needs to flow through `Pseudo.mask`/`toDomain` rather than being hardcoded.

**B. Extra R1CS (PS has more gates)**: PS generates a constraint where OCaml doesn't. Common cause: PS seals unnecessarily, or PS uses `mul_` where OCaml uses `Scale` (because OCaml's operand is const). Remove the extra seal or ensure the operand is const.

**C. Wrong coefficients**: The R1CS equation is structurally different. Compare the exact formula in OCaml (via merlin) with the PS expression tree. Pay attention to:
- Argument order in `mul_` (affects R1CS coefficient signs)
- Whether an intermediate result is sealed before being used in the next operation
- `sub_` vs negation + add

**D. Missing seal**: OCaml seals an intermediate result before passing it to the next operation. PS passes the raw expression. Add a `seal` call at the same point.

**E. Extra seal**: PS seals where OCaml doesn't. Remove the seal.

**Constraint**: Make the narrowest possible fix. Prefer changes to `WrapMain.purs` over library code. If library code must change, it MUST not break sub-circuit tests.

### Step 4: Type-check
```bash
npx purs compile -g corefn $(npx spago sources -p pickles-circuit-diffs 2>/dev/null | grep -v '/test/') \
  packages/pickles-circuit-diffs/test/**/*.purs --json-errors
```
Fix type errors before proceeding.

### Step 5: Run the wrap_main test
```bash
npx spago test -p pickles-circuit-diffs -- --example "wrap_main" 2>&1 | tee /tmp/wrap_main_test.txt
```
**IMPORTANT**: Save output to `/tmp/wrap_main_test.txt`. NEVER re-run the test to grep different things — analyze the saved file.

### Step 6: Measure progress

**Phase 1:**
```bash
node tools/circuit-diff-summary.mjs packages/pickles-circuit-diffs/circuits/results/wrap_main_circuit.json 2>&1 | tee /tmp/wrap_main_summary.txt
```
Extract `NEW_DIFF_ROW`. If the tool reports "All gates match exactly (kinds + coefficients)", check if test passed. If test still fails, transition to Phase 2.

**Phase 2:**
```bash
node tools/circuit-wire-diff.mjs packages/pickles-circuit-diffs/circuits/results/wrap_main_circuit.json 2>&1 | tee /tmp/wrap_main_wire_summary.txt
```
Extract `NEW_WIRE_DIFF_ROW`.

**Decision tree:**
- `NEW_DIFF_ROW > PREV_DIFF_ROW` → **Progress!** Go to Step 7.
- `NEW_DIFF_ROW == PREV_DIFF_ROW` → Fix didn't help. Revert (`git checkout -- <files>`), return to Step 2 with deeper analysis.
- `NEW_DIFF_ROW < PREV_DIFF_ROW` → **Regression.** Revert immediately, return to Step 2.
- Test passes (0 diffs) → **Done!** Go to Step 8.

### Step 7: Regression check + commit

If the fix touched library code (anything outside WrapMain.purs):
```bash
npx spago test -p pickles-circuit-diffs -- --example "finalize_other_proof_wrap" 2>&1 | tail -5
npx spago test -p pickles-circuit-diffs -- --example "wrap_verify" 2>&1 | tail -5
npx spago test -p pickles-circuit-diffs -- --example "hash_messages_for_next_wrap" 2>&1 | tail -5
npx spago test -p pickles-circuit-diffs -- --example "choose_key" 2>&1 | tail -5
```

- All pass → Commit: `wrap_main: fix <description> (first diff row N→M)`
  - Update `PREV_DIFF_ROW = NEW_DIFF_ROW`
  - Return to Step 1
- Any regress → The fix must be restructured to only change WrapMain.purs. Revert, re-analyze, try again.

### Step 8: Final verification
```bash
# Full suite — confirm no regressions anywhere
npx spago test -p pickles-circuit-diffs 2>&1 | tee /tmp/full_circuit_diffs.txt
```

## Phase 2: Wire Debugging

Phase 2 begins when `circuit-diff-summary.mjs` reports "All gates match exactly (kinds + coefficients)" but the test still reports "mismatch".

Use `tools/circuit-wire-diff.mjs` to find the first wire difference:
```bash
node tools/circuit-wire-diff.mjs packages/pickles-circuit-diffs/circuits/results/wrap_main_circuit.json 5
```

The tool shows which wire columns differ at each gate and surrounding context. Progress metric becomes the first wire-diff row (must strictly increase per commit, same as Phase 1).

Wire differences typically indicate:
- Variable allocation order differs (e.g., OCaml evaluates right-to-left, PS left-to-right)
- A `seal` at a different point creates a variable with a different index
- An `exists` call allocates in a different order

Fixes are usually:
- Reverse traversal order to match OCaml's right-to-left evaluation (see MEMORY.md "OCaml Right-to-Left Evaluation Order")
- Add/remove/move a seal to match variable allocation
- Reorder `exists` calls

## Debugging Reference

### The const/non-const distinction
```
mul_ (const_ c) x → Scale c x → 0 constraints
mul_ (Var i)    x → exists z; assert_r1cs i x z → 1 R1CS constraint
```
This is the #1 source of gate count differences. A value coming from `Pseudo.mask` or `Pseudo.toDomain` is non-constant (it's a circuit variable). The same value hardcoded as `const_` is constant. The standalone sub-circuit tests use constant values, so they pass. But wrap_main feeds non-constant values from pseudo-selection, so the sub-circuits generate more constraints.

### R1CS diff tool output
```
1*vo + -1*vl*vr        = multiplication (from mul_)
1*vo + -1*vl*vr co=-1  = square (from square_)
c=<large number>       = seal constant (the cached value of the sealed expression)
```

### Using merlin (MANDATORY for OCaml)
```bash
nix develop mina#default -c bash -c 'cd mina && tools/merlin_type.sh <file> <line> <col_start> <col_end>'
```
Always query types of:
- Domain generator expressions
- Operands to mul/square/seal
- Return types of `Pseudo.choose`/`Pseudo.mask`

### Important rules
1. **Never re-run expensive tests** to grep for different output. Save to `/tmp/` first.
2. **Never commit unless the first-diff row strictly increases.**
3. **Always use merlin for OCaml.** Do not manually trace types through functors.
4. **Prefer WrapMain.purs changes over library changes** to avoid regressions.
5. **Type-check before running tests** — `purs compile -g corefn` is fast; tests are slow.
6. **One fix at a time.** Don't batch speculative fixes.
7. **Pay attention to seal at every divergence.** Check both sides for explicit seal calls, implicit seals via `Checked.mul`, and const-vs-non-const status of operands.
