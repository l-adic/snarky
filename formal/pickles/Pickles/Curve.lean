import Snarky.Kimchi.Circuit.VarBaseMul
import Bulletproof.Wire
import Pasta.Basic

/-!
# The gadget layer's curve dictionary of a commitment curve

The gadget theorems (`Snarky.Kimchi.*`) are stated over `HasCurve F`, a Mathlib affine curve
with the four facts the gate semantics consume; the wire verifier is stated over
`CommitmentCurve`, CompElliptic's `SWCurve` with its scalar order. The two describe one curve:
`C.E.toAffine` is the affine form and `SWPoint.equivPoint` the group isomorphism. This module
is the map from the second to the first, so an assembly stated over a `CommitmentCurve` derives
its gadget dictionary instead of asking for the coupling as fields.

## Main definitions

* `HasCurve.ofCommitmentCurve` — the dictionary of a commitment curve, at the bounds `2 < base`
  and `2 < scalar` that rule out characteristic `2` and a 2-torsion group.

## Main results

* `CommitmentCurve.order_eq` — the affine group's order is the scalar cardinality.
* `CommitmentCurve.affine_card_nsmul` — the scalar order kills the affine group.
-/

namespace Pickles

open CompElliptic.CurveForms.ShortWeierstrass Bulletproof.Ipa Snarky.Kimchi

/-- The affine group's order is the wire's scalar cardinality. -/
theorem _root_.Bulletproof.Ipa.CommitmentCurve.order_eq (C : CommitmentCurve) :
    C.E.toAffine.order = C.scalar :=
  (SWPoint.card_eq_point C.E).symm.trans C.card

/-- The scalar order kills the affine group (Lagrange). -/
theorem _root_.Bulletproof.Ipa.CommitmentCurve.affine_card_nsmul (C : CommitmentCurve)
    (X : C.E.toAffine.Point) : C.scalar • X = 0 := by
  rw [← C.order_eq]; exact card_nsmul_eq_zero'

/-- The gadget layer's curve dictionary of a commitment curve: the affine form of `C.E`, short
by `C.a_zero`, of prime order by `C.card`, and off characteristic `2` and 2-torsion by the two
bounds. -/
noncomputable def _root_.Snarky.Kimchi.HasCurve.ofCommitmentCurve (C : CommitmentCurve)
    (hbase : 2 < C.base) (hscalar : 2 < C.scalar) : HasCurve C.BaseField where
  W := C.E.toAffine
  short := ⟨rfl, rfl, rfl, C.a_zero⟩
  prime := C.order_eq ▸ Fact.out
  odd := by rw [C.order_eq]; omega
  two_ne := by
    haveI : NeZero C.base := ⟨by omega⟩
    intro h
    have h2 : ((2 : ℕ) : ZMod C.base) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h2
    exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)

end Pickles
