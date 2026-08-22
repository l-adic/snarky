import Pasta.Basic

/-!
# The curve dictionary

The EC gadget laws (`AddComplete`, `VarBaseMul`, `EndoMul`) are generic over a curve
dictionary — the curve, its short shape, and the group facts the gate-semantics
theorems consume — resolved by the field: the deployed Pasta curves are its two
instances, Pallas at `Fp` and Vesta at `Fq`.
-/

namespace Snarky.Kimchi

/-- The curve dictionary the EC gadget laws close over (the PS ambient
`WeierstrassCurve` class): the curve, its Pasta short shape, and the group facts the
gate-semantics theorems consume. The laws stay generic over it; the deployed Pasta
instances concretize it by field. -/
class HasCurve (F : Type) [Field F] [DecidableEq F] where
  /-- The curve the base point and accumulators live on. -/
  W : WeierstrassCurve.Affine F
  /-- The Pasta short-Weierstrass shape. -/
  short : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0
  /-- The group order is prime. -/
  prime : Nat.Prime W.order
  /-- The group order is not `2` — with `prime`, the group has no 2-torsion. -/
  odd : W.order ≠ 2
  /-- The field does not have characteristic `2`. -/
  two_ne : (2 : F) ≠ 0

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Pasta in
/-- The dictionary at deployed Pallas: the certified order facts from `Pasta`. -/
instance HasCurve.pallas : HasCurve Fp where
  W := Pallas.curve.toAffine
  short := ⟨rfl, rfl, rfl, rfl⟩
  prime := Fact.out
  odd := by rw [pallas_card]; decide
  two_ne := by decide

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Pasta in
/-- The dictionary at deployed Vesta — the other half of the 2-cycle. -/
instance HasCurve.vesta : HasCurve Fq where
  W := Vesta.curve.toAffine
  short := ⟨rfl, rfl, rfl, rfl⟩
  prime := Fact.out
  odd := by rw [vesta_card]; decide
  two_ne := by decide

end Snarky.Kimchi
