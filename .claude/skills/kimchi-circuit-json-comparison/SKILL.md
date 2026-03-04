---
name: kimchi-circuit-json-comparison
description: Add new Kimchi gate circuits to the JSON comparison tests that verify PureScript circuits produce identical constraint systems to OCaml. Use when adding a new gate circuit or debugging a circuit mismatch.
---

# Kimchi Circuit JSON Comparison

This skill guides adding new Kimchi gate circuits to the JSON comparison test suite, which verifies that PureScript circuits produce identical constraint systems to the OCaml reference implementation.

## Overview

The workflow is:
1. Write an OCaml dump function that isolates the circuit
2. Build and run it inside `nix develop` to produce a JSON fixture
3. Copy the fixture to `packages/snarky-kimchi/test/fixtures/`
4. Write a PureScript test that compiles the same circuit and compares
5. Iterate until the circuits match exactly

## Key Files

| File | Purpose |
|------|---------|
| `mina/src/lib/pickles/dump_circuit_impl.ml` | OCaml circuit definitions for JSON dump |
| `mina/src/lib/pickles/dump_circuit/dump_circuit.ml` | OCaml entry point wrapper |
| `packages/snarky-kimchi/test/fixtures/*.json` | OCaml-generated JSON fixtures |
| `packages/snarky-kimchi/test/Test/Snarky/Circuit/Kimchi/CircuitJson.purs` | PureScript comparison tests |
| `packages/snarky-kimchi/src/Snarky/Backend/Kimchi/CircuitJson.purs` | Parsing: `readCircuitJson`, `circuitToJson` |

## Circuit Status

| PureScript Circuit | Gate Type | Status |
|---|---|---|
| `AddComplete` → `addComplete` | `CompleteAdd` | exact match |
| `VarBaseMul` → `scaleFast1` | `VarBaseMul` | exact match |
| `VarBaseMul` → `scaleFast2'` (128-bit) | `VarBaseMul` | exact match |
| `EndoMul` → `endo` | `EndoMul` | exact match |
| `EndoScalar` → `toField` | `EndoMulScalar` | exact match |
| `Poseidon` → `poseidon` | `Poseidon` | exact match |
| `GroupMap` → `groupMapCircuit` | (generic gates only) | not yet compared |
| All 16 DSL operations | `Generic` | exact match |

## Step 1: Add the Circuit to the OCaml Dump Program

The dump program lives inside the pickles library so it can access internal modules like `Plonk_curve_ops`.

Edit `mina/src/lib/pickles/dump_circuit_impl.ml`. Each circuit is a function that takes typed inputs and calls the OCaml implementation directly:

```ocaml
(* Example: add_complete uses the real Plonk_curve_ops.Make_add.add_fast *)
module Add = Plonk_curve_ops.Make_add(Impl)

let add_complete_circuit (p1, p2) () =
  Add.add_fast ~check_finite:false p1 p2
```

Then register it in the `run` function with appropriate `input_typ` and `return_typ`:

```ocaml
let point_typ = Impl.Typ.(Impl.Field.typ * Impl.Field.typ) in
let two_point_typ = Impl.Typ.(point_typ * point_typ) in
dump "add_complete_circuit" add_complete_circuit
  ~input_typ:two_point_typ ~return_typ:point_typ
```

**Key details**:
- The dump helper must be eta-expanded to avoid OCaml's value restriction (it's polymorphic in `input_typ`/`return_typ`)
- Use `Impl.Field.typ` for field inputs, `Impl.Boolean.typ` for booleans, `Impl.Typ.unit` for unit returns
- `public_input_size` = number of input fields + number of output fields

## Step 2: Build and Run inside `nix develop`

The mina OCaml build requires `nix develop` (the pure nix shell), **not** `nix-shell` (which is an impure shell requiring separate opam setup).

```bash
cd mina

# Enter the pure dev shell (requires submodules)
nix develop "git+file://$(pwd)?submodules=1"

# Build and run the dump executable
dune exec src/lib/pickles/dump_circuit/dump_circuit.exe

# Exit nix shell
exit
```

This writes JSON files to `mina/src/lib/pickles/dump_circuit/`.

**Gotchas**:
- You must have git submodules initialized: `git submodule update --init --recursive`
- Do NOT run `dune clean` -- it wipes cached build artifacts and subsequent builds take a very long time
- Do NOT use `nix-shell` -- it provides a different (incomplete) OCaml environment
- If the build fails on unrelated modules (e.g. `dummy.ml`), check for uncommitted changes in the mina submodule with `git status` / `git diff`

## Step 3: Copy the Fixture

```bash
cp mina/src/lib/pickles/dump_circuit/<name>.json \
   packages/snarky-kimchi/test/fixtures/
```

## Step 4: Write the PureScript Comparison Test

Tests live in `packages/snarky-kimchi/test/Test/Snarky/Circuit/Kimchi/CircuitJson.purs`.

For each circuit shape, there's a compile helper:

```purescript
compileFF  -- field -> field
compileFB  -- field -> bool
compileFU  -- field -> unit
compileBB  -- bool -> bool
compileBU  -- bool -> unit
compilePP  -- (point, point) -> point  (Kimchi-specific)
```

To add a new gate test:

1. Write a circuit function matching the OCaml signature:
```purescript
addCompleteCircuit (Tuple p1 p2) =
  _.p <$> addComplete p1 p2
```

2. Add a compile helper if needed (for new input/output type shapes)

3. Start with `debugCompare` to see both circuits side-by-side:
```purescript
describe "Kimchi gate matches" do
  debugCompare "add_complete_circuit" (compilePP addCompleteCircuit)
```

4. Switch to `exactMatch` once the circuits match:
```purescript
  exactMatch "add_complete_circuit" (compilePP addCompleteCircuit)
```

### Running the Tests

```bash
npx spago test -p snarky-kimchi -- --example "CircuitJson"
```

## Step 5: Iterate on Differences

### Extra boolean check constraints

PureScript's `exists` automatically adds boolean check constraints when the return type is `BoolVar`. OCaml's `exists` with `Field.typ` does not. If a Kimchi gate already enforces the boolean property (like `CompleteAdd` does for `same_x` and `inf`), wrap the witness in `UnChecked` to skip the redundant check:

```purescript
-- Before: adds boolean check constraint
sameX <- exists $ lift2 eq (readCVar p1.x) (readCVar p2.x)

-- After: gate enforces boolean property, skip check
UnChecked sameX <- exists $ UnChecked <$>
  lift2 eq (readCVar p1.x) (readCVar p2.x)
```

### Missing seal calls

OCaml may seal (reduce to single variable) inputs before passing to a gate. Check if the OCaml function calls `seal` or similar operations on its inputs. Our `sealPoint` helper handles this for affine points.

### Different witness variable ordering

If the gate structure matches but wires differ, the issue may be in the order variables are introduced via `exists`.

### OCaml unspecified record field evaluation order

**This is a subtle pitfall.** When OCaml code uses a record `map` function like:

```ocaml
(* mina/src/lib/crypto/kimchi_pasta_snarky_backend/endoscale_scalar_round.ml *)
let map { n0; n8; a0; b0; ... } ~f =
  { n0 = f n0; n8 = f n8; a0 = f a0; b0 = f b0; ... }
```

...and `f` has side effects (like `reduce_to_v` which emits generic constraints and updates `cached_constants`), the **evaluation order of record fields is unspecified** by the OCaml language spec. The `ocamlopt` compiler used by mina typically evaluates them **right-to-left** (last field first).

This affects:
- **Constant deduplication**: Which of two identical constants (e.g. `a0=2` and `b0=2`) gets its own variable vs. reuses the cached one depends on which `reduce_to_v` call runs first.
- **Generic gate batching**: The order constants are reduced determines which constraint is queued vs. which triggers emission of a double-generic gate, affecting the left/right half ordering and all downstream wire references.

**How to diagnose**: If gates structurally match (same kinds, same count) but the two halves of a double-generic gate are swapped and wire references in subsequent gates differ, suspect RTL evaluation order. Compare which constants share variables in OCaml vs. PureScript.

**How to fix**: In the PureScript `reduce` function for the gate type (e.g. `Snarky.Constraint.Kimchi.EndoScalar.reduce`), reorder the `reduceToVariable` calls to match OCaml's effective (RTL) evaluation order. For `EndoScalar`, this meant processing `xs, b8, a8, b0, a0, n8, n0` instead of the source-order `n0, n8, a0, b0, a8, b8, xs`.

**Key file**: `mina/src/lib/crypto/kimchi_pasta_snarky_backend/plonk_constraint_system.ml` — the `add_constraint` function contains `reduce_to_v` and the `Endoscale_scalar_round.map ~f:reduce_to_v` call (line ~1989). Other gate types with record `map` functions (e.g. `Scale_round`, `Endoscale_round`) will have the same issue.

### Constant deduplication in `reduceToVariable`

OCaml's `reduce_to_v` (in `plonk_constraint_system.ml` line 1555) uses a `cached_constants` hashtable: when reducing a `Const c` to a variable, it checks the cache first and reuses an existing variable if the same constant was already reduced. PureScript's `reduceToVariable` must route the constant case through `addEqualsConstraint` (which checks `cachedConstants`) rather than directly emitting `addGenericPlonkConstraint`. Without this, identical constants like `a=2` and `b=2` produce duplicate constraints and extra gates.

### check_finite and addComplete' true

OCaml's `add_fast` defaults to `check_finite=true`, which sets `inf = Field.zero` (a constant CVar). PureScript's `addComplete` used `exists` for `inf`. Use `addComplete' true` when matching OCaml's default `add_fast`:

```purescript
-- Before: inf from exists (fresh variable)
{ p } <- addComplete g1 g2

-- After: inf = false_ (constant zero), matching OCaml's check_finite=true
{ p } <- addComplete' true g1 g2
```

This matters for permutation wiring: the constant-zero inf variable gets deduplicated via `cachedConstants`, sharing a permutation cycle with other zero constants (like `nPrev` in VarBaseMul or `nAcc` initial value in EndoMul).

### Direct CVar references vs fresh exists variables

OCaml's `endo` function uses `!acc` and `!n_acc` directly (not via `mk`/`exists`) for the round's input point and previous accumulator. These are the actual CVars from the previous round's output. PureScript must do the same — use `st.acc` and `st.nAcc` directly in the round record, NOT re-create them inside `exists`:

```purescript
-- Wrong: creates fresh variables, breaks permutation links
{ p, nAccPrev, ... } <- exists do
  { x: xp, y: yp } <- read @(AffinePoint _) st.acc
  nAccPrevVal <- readCVar st.nAcc
  pure { p: { x: xp, y: yp }, nAccPrev: nAccPrevVal, ... }

-- Correct: preserves variable identity for permutation wiring
{ r, s1, s3, s, nAccNext } <- exists do ...  -- only computed values
pure $ Tuple
  { p: st.acc, nAcc: st.nAcc, ... }  -- direct CVar references
  { nAcc: nAccNext, acc: s }
```

### Seal outside add_fast to match OCaml constraint ordering

OCaml's `endo` seals `Field.scale xt Endo.base` **before** calling `G.(+)` (which is `add_fast`). The seal constraint is queued in the generic gate batcher, and the `inf=0` constraint from `add_fast`'s reduction pairs with it into a double-generic gate. In PureScript, seal `scale_ eb g.x` before calling `addComplete'`:

```purescript
phix <- seal (scale_ eb g.x)
{ p } <- addComplete' true g (g { x = phix })
```

### Using `scale_` instead of `mul_` for constant endo

OCaml uses `Field.scale a endo` (constant CVar scaling, no constraint) while PureScript's `mul_` generates a Generic gate. When the endo parameter is known to be a constant (`Const e`), pattern match on the CVar constructor and use `scale_` instead:

```purescript
case endo of
  Const e -> pure $ scale_ e a `add_` b
  _ -> a `mul_` endo <#> add_ b
```

## JSON Format

The JSON is produced by Rust's `serde_json` on the `Circuit` struct. No OCaml-specific encoding:

```json
{
  "public_input_size": 6,
  "gates": [
    {
      "typ": "CompleteAdd",
      "wires": [{"row": 0, "col": 0}, ...],
      "coeffs": ["0100...00"]
    }
  ]
}
```

Gate type names are Rust `GateType` enum variants: `"Zero"`, `"Generic"`, `"Poseidon"`, `"CompleteAdd"`, `"VarBaseMul"`, `"EndoMul"`, `"EndoMulScalar"`.

Coefficient hex strings are little-endian field element serialization (arkworks `serialize_compressed` + hex encode).

## Debugging with Variable Metadata

When gate-level diffs are hard to trace back to source code, use the **variable metadata** technique to cross-reference gate wires with labeled code regions.

### How it works

1. **Label circuit steps** with `label` from `Snarky.Circuit.DSL`:
```purescript
zeta <- label "step2_zeta" $ toField @8 rawZeta endoVar
alpha <- label "step2_alpha" $ toField @8 rawAlpha endoVar
zkPoly <- label "step10_zkPoly" $ do
  ...
```

2. **Export `varMetadata`** from `CircuitBuilderState` — maps each `Variable` to its label stack (recorded when `fresh` creates the variable).

3. **Export `placeVariables`** from `Snarky.Backend.Kimchi` — maps each `Variable` to its `Array (Tuple row col)` gate cell positions.

4. **Cross-reference in a Node script**: for each gate row, look up which variables appear in its wires, then look up those variables' labels to identify which code step generated the constraint.

### Key exports needed

```purescript
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Kimchi (makePublicInputRows, placeVariables)
import Snarky.Constraint.Kimchi.Types (AuxState, KimchiRow, toKimchiRows)

fopState :: CircuitBuilderState (KimchiGate StepField) (AuxState StepField)
fopState = compilePure (Proxy @V151) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
  myCircuit Kimchi.initialState

-- Build variable → cell placement from constraint rows
piRows = (makePublicInputRows fopState.publicInputs :: Array (KimchiRow StepField))
rows = piRows <> concatMap toKimchiRows fopState.constraints
placement = placeVariables rows  -- Map Variable (Array (Tuple Int Int))

-- Combine with fopState.varMetadata :: Map Variable (Array String)
-- to get: for each variable, its labels AND its gate cell positions
```

### Analysis script pattern

```javascript
// Build reverse map: gate row -> Set of labels
const rowLabels = {};
for (const [varId, info] of Object.entries(metadata)) {
  for (const [row, col] of info.cells) {
    if (!rowLabels[row]) rowLabels[row] = new Set();
    for (const l of info.labels) rowLabels[row].add(l);
  }
}

// For each differing gate, show which code step generated it
for (const diffGate of diffs) {
  const labels = [...(rowLabels[diffGate.index] || [])];
  console.log(`Gate ${diffGate.index}: ${labels.join(', ')}`);
}

// Show runs of matching/differing gates with labels
// to identify which step introduced the divergence
```

### What this reveals

- **First diff location**: which labeled step generates the first diverging constraint
- **Offset detection**: if PS is N gates behind/ahead of OCaml, the labels show where extra/missing constraints are
- **Constant vs circuit variable**: if a step's variables don't appear in any gate row, the computation was folded into constants (no constraints generated)

## Common Circuit Translation Pitfalls

### `const_` suppresses constraints

`mul_ (const_ c) x` returns `Scale c x` with NO constraint. If OCaml computes the same value as a non-constant (e.g. via `mask` which produces `Scale(c, which_bit)`), then `mul (Scale(c, var)) x` generates an R1CS constraint. The fix: use `scale_ c var` to create a non-constant CVar, then `mul_`.

### `square_` vs `mul_ x x`

PureScript's `square_` generates a Square constraint (different coefficient layout). OCaml's `let square x = x * x` in `scalars_env` uses `Field.mul`, which generates an R1CS constraint. Use `mul_ x x` when matching OCaml code that defines `square` as `x * x`.

### In-circuit vs pure-constant omega powers

OCaml's `scalars_env` computes omega powers in-circuit because `domain#generator` returns a non-constant `Scale(gen_const, which_bit)`. So `one / gen` generates `inv_` + R1CS constraints, and `zeta - omega_var` produces 2-term linear combinations that need materializing constraints. PureScript must not pre-compute these as pure field constants — it must mirror the in-circuit computation to match gate counts.
