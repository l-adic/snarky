import Snarky.Circuit.DSL.Field
import Snarky.Circuit.DSL.Assert
import Snarky.Kimchi.Constraint.AddComplete
import Pasta.Basic

-- `mvcgen` is experimental; this option is its acknowledged-use switch (see the
-- `Backend/WP` module docstring for the adoption rationale).
set_option mvcgen.warning false

/-!
# The curve-tagged point

Port of PS `WeierstrassAffinePoint`
(packages/snarky-curves/src/Snarky/Data/EllipticCurve.purs): an affine point whose TYPE
names its curve, and whose `CheckedType.check` fires the on-curve constraint — OCaml
`assert_on_curve`: `x² ` by the dedicated square row, `x³` by one `r1cs` row,
`y² = x³ + a·x + b` by one more square row. The plain `AffinePoint` stays checks-free
(the `genericCheck` convention, `Circuit/AddComplete`); a statement carries THIS type
where its wire refinement is a genuine curve point, so the whole-circuit seam forces
the public reading on-curve.

Name map: PS's phantom tag `g` with its `WeierstrassCurve f g` params class becomes the
two coefficient indices `a b : F` — the same information, value-indexed. The law pair
lands the equation in CompElliptic's `OnCurve` vocabulary, which is what a boundary
statement consumes (`SWPoint` construction at the read coordinates).
-/

namespace Snarky.Kimchi

open Snarky
open CompElliptic.CurveForms.ShortWeierstrass

variable {F c : Type}

/-- An affine point tagged with its curve's coefficients (PS
`WeierstrassAffinePoint g f`). The tag is phantom on the data — the constraint arrives
through `CheckedType`, not the carrier. -/
structure CurvePoint (a b : F) (α : Type) where
  /-- The untagged coordinates. -/
  point : AffinePoint α

/-- The on-curve check circuit (OCaml `assert_on_curve`, snarky_curve.ml): the
constraint shape is Square, then `r1cs`, then Square — deployed rows, not a generic
polynomial identity. -/
def CurvePoint.check [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c]
    {a b : F} (p : CurvePoint a b (FVar F)) : CircuitM F c PUnit := do
  let x2 ← square p.point.x
  let x3 ← mul x2 p.point.x
  assertSquare p.point.y (CVar.add_ (CVar.add_ x3 (CVar.scale_ a p.point.x)) (.const b))

/-- The tag is phantom: a tagged point is its point. -/
@[simps apply symm_apply] def CurvePoint.equivPoint {a b : F} {α : Type} :
    CurvePoint a b α ≃ AffinePoint α where
  toFun p := p.point
  invFun p := ⟨p⟩
  left_inv _ := rfl
  right_inv _ := rfl

attribute [circuitVal] CurvePoint.equivPoint_apply CurvePoint.equivPoint_symm_apply

/-- The tagged point encodes exactly as its coordinates, `[x, y]`. -/
instance instCurvePointCircuitType {a b : F} :
    CircuitType F (CurvePoint a b F) (CurvePoint a b (FVar F)) :=
  CircuitType.ofEquiv (inferInstance : CircuitType F (AffinePoint F) (AffinePoint (FVar F)))
    CurvePoint.equivPoint CurvePoint.equivPoint

/-- A tagged point pays its on-curve constraint (PS `WeierstrassAffinePoint`'s
`CheckedType`). -/
instance instCurvePointCheckedType {a b : F}
    [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c] :
    CheckedType F c (CurvePoint a b (FVar F)) where
  check := CurvePoint.check

open Std.Do in
/-- The check's rows force the reading on-curve: any satisfying valuation reads the
coordinates onto `y² = x³ + a·x + b`. -/
theorem CurvePoint.check_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] {a b : F}
    (p : CurvePoint a b (FVar F)) (Q : PostCond PUnit (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (_ : PUnit) => OnCurve a b (p.point.x.val V, p.point.y.val V)) Q⦄
    (CurvePoint.check (c := c) p)
    ⦃Q⦄ := by
  simp only [CurvePoint.check]
  mvcgen
  rename_i s hpre
  intro x2 _ hx2
  mvcgen
  intro x3 _ hx3
  mvcgen
  intro u _ hsq
  refine hpre u _ ?_
  rw [CVar.val_add_, CVar.val_add_, CVar.val_scale_, hx3, hx2] at hsq
  show p.point.y.val s.V ^ 2
      = p.point.x.val s.V ^ 3 + a * p.point.x.val s.V + b
  have hb : (CVar.const b).val s.V = b := rfl
  rw [hb] at hsq
  linear_combination hsq

open Std.Do in
/-- The check's honest run succeeds on a reading satisfying the on-curve equation,
only extending the table (the `x³` row witnesses its product). -/
theorem CurvePoint.check_complete_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [Checker F c] [LawfulChecker F c] {a b : F}
    (p : CurvePoint a b (FVar F))
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => (p.point.x.eval env).isOk ∧ (p.point.y.eval env).isOk ∧
        ∀ xv yv, p.point.x.eval env = .ok xv → p.point.y.eval env = .ok yv →
          OnCurve a b (xv, yv))
        (fun _ _ _ => True) Q⦄
    (CurvePoint.check (c := Prover c) p)
    ⦃Q⦄ := by
  intro st hpre
  obtain ⟨⟨hokx, hoky, hoc⟩, hk⟩ := hpre
  obtain ⟨xv, hx⟩ := CVar.evalOk hokx
  obtain ⟨yv, hy⟩ := CVar.evalOk hoky
  have hcurve : yv ^ 2 = xv ^ 3 + a * xv + b := hoc xv yv hx hy
  simp only [CurvePoint.check, WPMonad.wp_bind, PredTrans.apply_Bind_bind]
  refine square_complete_spec p.point.x _ st ⟨isOk_of_eq hx, fun x2 st₁ hx2 hle₁ => ?_⟩
  have hx2v := hx2 xv hx
  have hx₁ := CVar.eval_le hle₁ hx
  refine mul_complete_spec x2 p.point.x _ st₁
    ⟨⟨isOk_of_eq hx2v, isOk_of_eq hx₁⟩, fun x3 st₂ hx3 hle₂ => ?_⟩
  have hx3v := hx3 (xv * xv) xv hx2v hx₁
  have hx₂ := CVar.eval_le hle₂ hx₁
  have hy₂ := CVar.eval_le hle₂ (CVar.eval_le hle₁ hy)
  have hrhs : (CVar.add_ (CVar.add_ x3 (CVar.scale_ a p.point.x))
      (.const b)).eval st₂.env = .ok (xv * xv * xv + a * xv + b) :=
    CVar.eval_add_ (CVar.eval_add_ hx3v (CVar.eval_scale_ hx₂ a)) rfl
  refine assertSquare_complete_spec p.point.y _ _ st₂
    ⟨⟨isOk_of_eq hy₂, isOk_of_eq hrhs, fun av bv ha hb => ?_⟩,
      fun _ st₃ _ hle₃ => hk PUnit.unit st₃ trivial (hle₁.trans (hle₂.trans hle₃))⟩
  rw [hy₂] at ha
  rw [hrhs] at hb
  injection ha with ha
  injection hb with hb
  subst ha
  subst hb
  linear_combination hcurve

end Snarky.Kimchi
