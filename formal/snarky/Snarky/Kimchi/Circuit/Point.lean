import Snarky.Kimchi.Circuit.AddComplete
import Snarky.DSL.Boolean

/-!
# Point-level gadgets and readings

Small point-level pieces the group-side gadgets compose, beside `OnCurveAt`: a point read
off cells is nonzero, the conditional select of a point (PS `if_` at `AffinePoint`, in
OCaml's reverse array order), and `addFast` at `checkFinite` read as the group sum.
-/

namespace Snarky.Kimchi

open Snarky Std.Do WeierstrassCurve.Affine

variable {F c : Type}

/-- A point read off cells is affine, so nonzero. -/
theorem OnCurveAt.ne_zero [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    {V : Valuation F} {p : AffinePoint (FVar F)} {P : W.Point} (h : OnCurveAt W V p P) :
    P ≠ 0 := by
  obtain ⟨hns, rfl⟩ := h
  exact Point.some_ne_zero hns

/-- Select a point by a bit (PS `if_` at `AffinePoint`, OCaml's reverse array order): `y`
then `x`. -/
def selectPoint [Field F] [DecidableEq F] [BasicSystem F c] (b : BoolVar F)
    (t e : AffinePoint (FVar F)) : CircuitM F c (AffinePoint (FVar F)) := do
  let y ← selectField b t.y e.y
  let x ← selectField b t.x e.x
  pure ⟨x, y⟩

/-- Points select coordinatewise, `y` before `x`. -/
instance instIfThenElseAffinePoint [Field F] [DecidableEq F] [BasicSystem F c] :
    IfThenElse F c (AffinePoint (FVar F)) :=
  ⟨selectPoint⟩

/-- Selection at a point is `selectPoint` — the instance's defining equation. -/
@[simp] theorem select_affinePoint [Field F] [DecidableEq F] [BasicSystem F c] (b : BoolVar F)
    (t e : AffinePoint (FVar F)) : select (c := c) b t e = selectPoint b t e := rfl

/-- Under any valuation satisfying the emitted constraints, the selected point reads as the
selected reading. -/
theorem selectPoint_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (b : BoolVar F) (t e : AffinePoint (FVar F)) :
    ⦃⌜True⌝⦄ selectPoint (c := Builder V c) b t e
    ⦃⇓ r _ => ⌜∀ bb : Bool, (↑b : CVar F).val V = bit bb →
      ∀ {W : WeierstrassCurve.Affine F} (T E : W.Point), OnCurveAt W V t T → OnCurveAt W V e E →
        OnCurveAt W V r (if bb then T else E)⌝⦄ := by
  simp only [selectPoint]
  mvcgen
  rename_i _ y _ hy x _ hx
  intro bb hb W T E hT hE
  have hx' := hx bb hb
  have hy' := hy bb hb
  cases bb
  · simp only [Bool.false_eq_true, ite_false] at hx' hy' ⊢
    obtain ⟨hns, rfl⟩ := hE
    exact ⟨by rw [hx', hy']; exact hns,
      Kimchi.Gate.AddComplete.some_congr W hns _ hx'.symm hy'.symm⟩
  · simp only [ite_true] at hx' hy' ⊢
    obtain ⟨hns, rfl⟩ := hT
    exact ⟨by rw [hx', hy']; exact hns,
      Kimchi.Gate.AddComplete.some_congr W hns _ hx'.symm hy'.symm⟩

/-- `addFast` at `checkFinite`: the infinity flag is pinned, so under any valuation
satisfying the emitted row the result reads as the group sum — given the group has no
2-torsion (`hnt`), which the row's doubling case asks of the first summand. -/
theorem addFast_checkFinite_spec {V : Valuation F} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    (htwo : (2 : F) ≠ 0) (hnt : ∀ P : W.Point, P ≠ 0 → P + P ≠ 0)
    (p1 p2 : AffinePoint (FVar F)) :
    ⦃⌜True⌝⦄ addFast (c := Builder V (KimchiConstraint F)) .checkFinite p1 p2
    ⦃⇓ r _ => ⌜∀ P Q : W.Point, OnCurveAt W V p1 P → OnCurveAt W V p2 Q →
      OnCurveAt W V r.p (P + Q)⌝⦄ := by
  refine builder_spec_imp _ _ _ (addFast_spec .checkFinite W ha htwo p1 p2)
    fun r ⟨hflag, hsum⟩ P Q hP hQ => ?_
  rcases hsum P Q hP hQ (hnt P (OnCurveAt.ne_zero hP)) with ⟨h1, -⟩ | ⟨-, hs⟩
  · exact absurd (h1.symm.trans (hflag rfl)) one_ne_zero
  · exact hs

end Snarky.Kimchi
