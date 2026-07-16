import Snarky.CVar

/-!
# The basic constraint interface

Port of `Snarky.Constraint.Basic` (packages/snarky/src/Snarky/Constraint/Basic.purs): the
two constraint constructors every backend supplies, and all the DSL's core combinators
need — rank-1 products and booleanity. Backends instantiate the class at their concrete
constraint type (`Snarky.Constraint.R1CS` for the plain R1CS model,
`Snarky.Kimchi.GateConstraint` for the Kimchi Generic-gate bridge).
-/

namespace Snarky

/-- The basic constraint constructors every backend supplies (PS
`class BasicSystem f c`): rank-1 products and booleanity. -/
class BasicSystem (F c : Type u) where
  /-- The constraint `a * b = prod`. -/
  r1cs : (a b prod : CVar F) → c
  /-- The constraint `x * x = x`, pinning `x` to `{0, 1}`. -/
  boolean : (x : CVar F) → c

end Snarky
