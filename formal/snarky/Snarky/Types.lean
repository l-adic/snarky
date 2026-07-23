import Snarky.Monad
import Snarky.Vec
import Snarky.Constraint.Basic

/-!
# Circuit types

Port of the typed layer of the DSL: `CircuitType` (PS `class CircuitType f a var` from
`Snarky.Circuit.Types`) and `CheckedType` (PS `class CheckedType f c var`,
packages/snarky/src/Snarky/Circuit/DSL/Monad.purs lines 488–531), together with the
`FVar`/`BoolVar` instances. The user-facing combinators built on these classes
(`witness`, `readVar`, `mul`, `assertEq`) live in `Snarky.DSL`; the backend constraint
interface lives in `Snarky.Constraint.Basic`.

Improvement over PS: the field-vector size is type-level (`Vector F size` instead of
`Array f` plus a runtime `sizeInFields` contract), so the length obligations disappear.

Out of scope for this port (deliberately): the generic-deriving machinery
(`GCheckedType`/`RCheckedType`) — Lean would grow `deriving` handlers or macros instead.
-/

namespace Snarky

/-! ## The type classes -/

/-- A bidirectional encoding of a value type `val` as `size` field elements, together with
its variable-bundle counterpart `var` (PS `CircuitType f a var`). -/
class CircuitType (F : Type u) (val : Type u) (var : outParam (Type u)) where
  /-- The number of field elements a `val` encodes to (PS `sizeInFields`, made type-level). -/
  size : Nat
  /-- Encode a value as its `size` field elements (PS `valueToFields`). -/
  valueToFields : val → Vector F size
  /-- Decode a value from its `size` field elements (PS `fieldsToValue`). -/
  fieldsToValue : Vector F size → val
  /-- Flatten a variable bundle into its `size` underlying `CVar`s (PS `varToFields`). -/
  varToFields : var → Vector (CVar F) size
  /-- Rebuild a variable bundle from `size` underlying `CVar`s (PS `fieldsToVar`). -/
  fieldsToVar : Vector (CVar F) size → var

/-- Variable bundles whose well-formedness is enforced by constraints: `check` is emitted
by `witness` under *both* interpreters, exactly like PS `CheckedType`'s `check`. -/
class CheckedType (F c : Type u) (var : Type u) where
  /-- The circuit that constrains the bundle to well-formed values (PS `check`). -/
  check : var → CircuitM F c PUnit

/-! ## Field and boolean variables -/

/-- A single field element as a circuit value (PS `FVar f` is a wrapped `CVar`). -/
abbrev FVar (F : Type u) := CVar F

instance : CircuitType F F (FVar F) where
  size := 1
  valueToFields x := #v[x]
  fieldsToValue v := v[0]
  varToFields x := #v[x]
  fieldsToVar v := v[0]

/-- A field element carries no well-formedness constraint (PS `CheckedType` instance for
`FVar`: `check = const (pure unit)`). -/
instance : CheckedType F c (FVar F) where
  check _ := .pure PUnit.unit

/-- A boolean as a circuit variable: a `CVar` constrained to `{0, 1}` (PS `BoolVar f`). -/
structure BoolVar (F : Type u) where
  /-- The underlying field expression, constrained to `{0, 1}` by `CheckedType.check`. -/
  toCVar : CVar F

instance [Zero F] [One F] [DecidableEq F] : CircuitType F Bool (BoolVar F) where
  size := 1
  valueToFields b := #v[if b then 1 else 0]
  fieldsToValue v := decide (v[0] ≠ 0)
  varToFields b := #v[b.toCVar]
  fieldsToVar v := ⟨v[0]⟩

/-- A freshly witnessed boolean must be constrained to `{0, 1}` (PS `CheckedType`
instance for `BoolVar`: `check = boolean`). -/
instance [BasicSystem F c] : CheckedType F c (BoolVar F) where
  check b := addConstraint (BasicSystem.boolean b.toCVar)

end Snarky
