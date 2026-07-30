import Snarky.Monad
import Snarky.Circuit.Types
import Snarky.Constraint.Basic

/-!
# CheckedType — transitional home

`CheckedType` (PS `class CheckedType f c var`, defined in
packages/snarky/src/Snarky/Circuit/DSL/Monad.purs) and its `FVar`/`BoolVar` instances.

TRANSITIONAL: this module exists only until walk step 5 of
`formal/docs/snarky-ps-alignment.md`, when `Snarky/Circuit/DSL/Monad.lean` — the class's
PS home — absorbs it and this file is deleted. The rest of the old `Snarky.Types` content
lives in `Snarky.Circuit.Types`.
-/

namespace Snarky

/-- Variable bundles whose well-formedness is enforced by constraints: `check` is emitted
by `witness` under *both* interpreters, exactly like PS `CheckedType`'s `check`. -/
class CheckedType (F c : Type u) (var : Type u) where
  /-- The circuit that constrains the bundle to well-formed values (PS `check`). -/
  check : var → CircuitM F c PUnit

/-- A field element carries no well-formedness constraint (PS `CheckedType` instance for
`FVar`: `check = const (pure unit)`). -/
instance : CheckedType F c (FVar F) where
  check _ := .pure PUnit.unit

/-- A freshly witnessed boolean must be constrained to `{0, 1}` (PS `CheckedType`
instance for `BoolVar`: `check = boolean`). -/
instance [BasicSystem F c] : CheckedType F c (BoolVar F) where
  check b := addConstraint (BasicSystem.boolean b.toCVar)

end Snarky
