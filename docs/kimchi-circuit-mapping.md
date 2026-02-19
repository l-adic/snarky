# Kimchi Circuit Mapping: PureScript ↔ OCaml

## Custom Kimchi Gate Circuits

| PureScript Circuit | OCaml File | OCaml Function | Gate Type |
|---|---|---|---|
| `Snarky.Circuit.Kimchi.AddComplete` → `addComplete` | `pickles/plonk_curve_ops.ml` | `Make_add.add_fast` | `CompleteAdd` |
| `Snarky.Circuit.Kimchi.VarBaseMul` → `scaleFast1` | `pickles/plonk_curve_ops.ml` | `Make.scale_fast` | `VarBaseMul` |
| `Snarky.Circuit.Kimchi.VarBaseMul` → `scaleFast2` | `pickles/plonk_curve_ops.ml` | `Make.scale_fast2` | `VarBaseMul` |
| `Snarky.Circuit.Kimchi.VarBaseMul` → `scaleFast2'` | `pickles/plonk_curve_ops.ml` | `Make.scale_fast2'` | `VarBaseMul` |
| `Snarky.Circuit.Kimchi.EndoMul` → `endo` | `pickles/scalar_challenge.ml` | `Make.endo` | `EndoMul` |
| `Snarky.Circuit.Kimchi.EndoMul` → `endoInv` | `pickles/scalar_challenge.ml` | `Make.endo_inv` | `EndoMul` |
| `Snarky.Circuit.Kimchi.EndoScalar` → `toField` | `pickles/scalar_challenge.ml` | `to_field_checked` | `EndoMulScalar` |
| `Snarky.Circuit.Kimchi.EndoScalar` → `toFieldPure` | `pickles/scalar_challenge.ml` | `to_field_constant` | (pure, no gate) |
| `Snarky.Circuit.Kimchi.Poseidon` → `poseidon` | `pickles/sponge_inputs.ml` | `Make.block_cipher` | `Poseidon` |
| `Snarky.Circuit.Kimchi.GroupMap` → `groupMapCircuit` | `snarky_group_map/checked_map.ml` | `Make.to_group` / `wrap` | (generic gates only) |
| `Snarky.Circuit.Kimchi.GroupMap` → `groupMap` | `snarky_group_map/snarky_group_map.ml` | `to_group` | (pure, no gate) |
| `Snarky.Circuit.Kimchi.GroupMap` → `potentialXs` | `snarky/group_map/bw19.ml` | `Make.potential_xs` | (pure computation) |

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

## Notes

- All OCaml paths are relative to `mina/src/lib/`.
- GroupMap uses no dedicated Kimchi gate; it composes from basic DSL operations (`mul_`, `div_`, `if_`, `assertSquare_`, `any_`).
- DSL operation circuits have been verified as exact gate-level matches against OCaml (JSON fixtures in `packages/snarky-kimchi/test/fixtures/`).
- The constraint reduction from basic constraints to Kimchi `Generic` gates is in `plonk_constraint_system.ml` (OCaml) and `Snarky.Constraint.Kimchi.GenericPlonk` (PureScript).
