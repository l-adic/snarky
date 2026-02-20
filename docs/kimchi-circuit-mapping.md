# Kimchi Circuit Mapping: PureScript ↔ OCaml

## Custom Kimchi Gate Circuits

| PureScript Circuit | OCaml File | OCaml Function | Gate Type | Status |
|---|---|---|---|---|
| `Snarky.Circuit.Kimchi.AddComplete` → `addComplete` | `pickles/plonk_curve_ops.ml` | `Make_add.add_fast` | `CompleteAdd` | exact match |
| `Snarky.Circuit.Kimchi.VarBaseMul` → `scaleFast1` | `pickles/plonk_curve_ops.ml` | `Make.scale_fast` | `VarBaseMul` | not yet compared |
| `Snarky.Circuit.Kimchi.VarBaseMul` → `scaleFast2` | `pickles/plonk_curve_ops.ml` | `Make.scale_fast2` | `VarBaseMul` | not yet compared |
| `Snarky.Circuit.Kimchi.VarBaseMul` → `scaleFast2'` | `pickles/plonk_curve_ops.ml` | `Make.scale_fast2'` | `VarBaseMul` | not yet compared |
| `Snarky.Circuit.Kimchi.EndoMul` → `endo` | `pickles/scalar_challenge.ml` | `Make.endo` | `EndoMul` | not yet compared |
| `Snarky.Circuit.Kimchi.EndoMul` → `endoInv` | `pickles/scalar_challenge.ml` | `Make.endo_inv` | `EndoMul` | not yet compared |
| `Snarky.Circuit.Kimchi.EndoScalar` → `toField` | `pickles/scalar_challenge.ml` | `to_field_checked` | `EndoMulScalar` | not yet compared |
| `Snarky.Circuit.Kimchi.EndoScalar` → `toFieldPure` | `pickles/scalar_challenge.ml` | `to_field_constant` | (pure, no gate) | — |
| `Snarky.Circuit.Kimchi.Poseidon` → `poseidon` | `pickles/sponge_inputs.ml` | `Make.block_cipher` | `Poseidon` | not yet compared |
| `Snarky.Circuit.Kimchi.GroupMap` → `groupMapCircuit` | `snarky_group_map/checked_map.ml` | `Make.to_group` / `wrap` | (generic gates only) | not yet compared |
| `Snarky.Circuit.Kimchi.GroupMap` → `groupMap` | `snarky_group_map/snarky_group_map.ml` | `to_group` | (pure, no gate) | — |
| `Snarky.Circuit.Kimchi.GroupMap` → `potentialXs` | `snarky/group_map/bw19.ml` | `Make.potential_xs` | (pure computation) | — |

## DSL Operation Circuits (all exact matches)

| PureScript DSL Operation | OCaml Source | Gate Type |
|---|---|---|
| `mul_` | `snarky/src/base/snark0.ml` | `Generic` |
| `inv_` | `snarky/src/base/snark0.ml` | `Generic` |
| `div_` | `snarky/src/base/snark0.ml` | `Generic` |
| `if_` | `snarky/src/base/snark0.ml` | `Generic` |
| `equals_` | `snarky/src/base/snark0.ml` | `Generic` |
| `assertEqual_` | `snarky/src/base/snark0.ml` | `Generic` |
| `assertSquare_` | `snarky/src/base/snark0.ml` | `Generic` |
| `assertNonZero_` | `snarky/src/base/snark0.ml` | `Generic` |
| `assertNotEqual_` | `snarky/src/base/snark0.ml` | `Generic` |
| `unpack_` | `snarky/src/base/snark0.ml` | `Generic` |
| `and_` | `snarky/src/base/utils.ml` | `Generic` |
| `or_` | `snarky/src/base/utils.ml` | `Generic` |
| `xor_` | `snarky/src/base/utils.ml` | `Generic` |
| `all_` | `snarky/src/base/utils.ml` | `Generic` |
| `any_` | `snarky/src/base/utils.ml` | `Generic` |
| `assert_` | `snarky/src/base/utils.ml` | `Generic` |

## Circuit JSON Comparison Workflow

This section documents how to add a new Kimchi gate circuit to the JSON comparison tests, which verify that our PureScript circuits produce identical constraint systems to OCaml.

### Overview

The workflow is:
1. Write an OCaml dump function that isolates the circuit
2. Build and run it inside `nix develop` to produce a JSON fixture
3. Copy the fixture to `packages/snarky-kimchi/test/fixtures/`
4. Write a PureScript test that compiles the same circuit and compares
5. Iterate until the circuits match exactly

### Step 1: Add the circuit to the OCaml dump program

The dump program lives inside the pickles library so it can access internal modules like `Plonk_curve_ops`:

- **Circuit definitions**: `mina/src/lib/pickles/dump_circuit_impl.ml`
- **Entry point wrapper**: `mina/src/lib/pickles/dump_circuit/dump_circuit.ml`
- **Dune file**: `mina/src/lib/pickles/dump_circuit/dune` (depends only on `pickles`)
- **Exposed via**: `pickles.mli` and `pickles.ml` (re-exports `Dump_circuit_impl`)

To add a new circuit, edit `dump_circuit_impl.ml`. Each circuit is a function that takes typed inputs and calls the OCaml implementation directly:

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

### Step 2: Build and run inside `nix develop`

The mina OCaml build requires `nix develop` (the pure nix shell), not `nix-shell` (which is an impure shell requiring separate opam setup).

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
- Do NOT run `dune clean` — it wipes cached build artifacts and subsequent builds take a very long time
- Do NOT use `nix-shell` — it provides a different (incomplete) OCaml environment
- If the build fails on unrelated modules (e.g. `dummy.ml`), check for uncommitted changes in the mina submodule with `git status` / `git diff`

### Step 3: Copy the fixture

```bash
cp mina/src/lib/pickles/dump_circuit/<name>.json \
   packages/snarky-kimchi/test/fixtures/
```

### Step 4: Write the PureScript comparison test

Tests live in `packages/snarky-kimchi/test/Test/Snarky/Circuit/Kimchi/CircuitJson.purs`.

For each circuit shape, there's a compile helper. The existing ones cover DSL circuits:

```purescript
compileFF  -- field → field
compileFB  -- field → bool
compileFU  -- field → unit
compileBB  -- bool → bool
compileBU  -- bool → unit
compilePP  -- (point, point) → point  (Kimchi-specific)
```

To add a new gate test:

1. Write a circuit function matching the OCaml signature:
```purescript
addCompleteCircuit (Tuple p1 p2) =
  _.p <$> addComplete p1 p2
```

2. Add a compile helper if needed (for new input/output type shapes)

3. Add the test to the spec:
```purescript
describe "Kimchi gate matches" do
  exactMatch "add_complete_circuit" (compilePP addCompleteCircuit)
```

4. Start with `debugCompare` instead of `exactMatch` to see both circuits side-by-side, then switch to `exactMatch` once they match.

### Step 5: Iterate on differences

Common sources of mismatch:

**Extra boolean check constraints**: PureScript's `exists` automatically adds boolean check constraints when the return type is `BoolVar`. OCaml's `exists` with `Field.typ` does not. If a Kimchi gate already enforces the boolean property (like `CompleteAdd` does for `same_x` and `inf`), wrap the witness in `UnChecked` to skip the redundant check:

```purescript
-- Before: adds boolean check constraint
sameX <- exists $ lift2 eq (readCVar p1.x) (readCVar p2.x)

-- After: gate enforces boolean property, skip check
UnChecked sameX <- exists $ UnChecked <$>
  lift2 eq (readCVar p1.x) (readCVar p2.x)
```

**Missing seal calls**: OCaml may seal (reduce to single variable) inputs before passing to a gate. Check if the OCaml function calls `seal` or similar operations on its inputs.

**Different witness variable ordering**: If the gate structure matches but wires differ, the issue may be in the order variables are introduced via `exists`.

### JSON Format

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

## Notes

- All OCaml paths are relative to `mina/src/lib/`.
- GroupMap uses no dedicated Kimchi gate; it composes from basic DSL operations (`mul_`, `div_`, `if_`, `assertSquare_`, `any_`).
- All circuits listed above have been verified as exact gate-level matches against OCaml (JSON fixtures in `packages/snarky-kimchi/test/fixtures/`).
- The constraint reduction from basic constraints to Kimchi `Generic` gates is in `plonk_constraint_system.ml` (OCaml) and `Snarky.Constraint.Kimchi.GenericPlonk` (PureScript).
- PureScript parsing infrastructure: `Snarky.Backend.Kimchi.CircuitJson` (`readCircuitJson`, `circuitToJson`).
