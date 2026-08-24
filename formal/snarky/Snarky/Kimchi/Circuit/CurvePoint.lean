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
open Snarky Snarky.Kimchi CompElliptic.Fields.Pasta

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

open CompElliptic.Curves.Pasta in
/-- A point tagged with Vesta's coefficients — what an `Fq`-circuit's public points are. -/
abbrev VestaPoint := CurvePoint (a := Vesta.curve.A) (b := Vesta.curve.B)

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
@[spec] theorem CurvePoint.check_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] {a b : F}
    (p : CurvePoint a b (FVar F)) :
    ⦃⌜True⌝⦄
    (CurvePoint.check (c := Builder V c) p)
    ⦃⇓ _ _ => ⌜OnCurve a b (p.point.x.val V, p.point.y.val V)⌝⦄ := by
  simp only [CurvePoint.check]
  mvcgen
  rename_i x2 _ hx2 x3 _ hx3 _ _
  intro hsq
  rw [CVar.val_add_, CVar.val_add_, CVar.val_scale_, hx3, hx2] at hsq
  show p.point.y.val V ^ 2
      = p.point.x.val V ^ 3 + a * p.point.x.val V + b
  have hb : (CVar.const b).val V = b := rfl
  rw [hb] at hsq
  linear_combination hsq

/-- The contract a curve point's check grants: its coordinates are on the curve. -/
instance instSoundCheckedTypeCurvePoint {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] {a b : F} :
    SoundCheckedType F c V (CurvePoint a b (FVar F)) where
  post p := OnCurve a b (p.point.x.val V, p.point.y.val V)
  check_sound p := CurvePoint.check_spec (V := V) p

@[circuitVal, simp] theorem SoundCheckedType.post_curvePoint {V : Valuation F} [Field F]
    [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] {a b : F}
    (p : CurvePoint a b (FVar F)) :
    SoundCheckedType.post (F := F) (c := c) (V := V) p
      = OnCurve a b (p.point.x.val V, p.point.y.val V) := rfl

/-- The state after the check's honest run: `square`'s, then `mul`'s (the assertion
allocates nothing). -/
def CurvePoint.checkRun [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] {a b : F}
    (st : ProverState F) (p : CurvePoint a b (FVar F)) : ProverState F :=
  let sq := squareRun st p.point.x
  (mulRun sq.1 sq.2 p.point.x).1

/-- The check's run grows the table. -/
theorem CurvePoint.checkRun_le [Field F] [DecidableEq F] {a b : F} (st : ProverState F)
    {p : CurvePoint a b (FVar F)} (hx : p.point.x.Scoped st) :
    st.env.Le (CurvePoint.checkRun st p).env :=
  (squareRun_grants (st := st) hx).le.trans
    (mulRun_grants (squareRun_grants hx).fvar_scoped (hx.of_le (squareRun_grants hx).le)).le

/-- The check's honest run on a reading satisfying the on-curve equation lands at
`checkRun`. -/
theorem CurvePoint.check_run [Field F] [DecidableEq F] [BasicSystem F c] [Checker F c]
    [LawfulChecker F c] {a b : F} {p : CurvePoint a b (FVar F)} (st : ProverState F)
    (hx : p.point.x.Scoped st) (hy : p.point.y.Scoped st)
    (hoc : OnCurve a b (p.point.x.val st.env.toValuation, p.point.y.val st.env.toValuation)) :
    prove (Checker.holds (F := F) (c := c)) (CurvePoint.check (c := c) p) st.nv st.env
      = .ok ((CurvePoint.checkRun st p).out ()) := by
  have hsq := squareRun_grants (st := st) hx
  have hm := mulRun_grants hsq.fvar_scoped (hx.of_le hsq.le)
  have hle := hsq.le.trans hm.le
  have hx3 : (mulRun (squareRun st p.point.x).1 (squareRun st p.point.x).2 p.point.x).2.val
      (mulRun (squareRun st p.point.x).1 (squareRun st p.point.x).2 p.point.x).1.env.toValuation
      = p.point.x.val st.env.toValuation * p.point.x.val st.env.toValuation
        * p.point.x.val st.env.toValuation := by
    rw [hm.fvar_val, hsq.fvar_val, CVar.val_of_le hsq.le hx]
  simp only [CurvePoint.check, CurvePoint.checkRun, prove_bind, square_run st hx, Except.bind,
    mul_run _ hsq.fvar_scoped (hx.of_le hsq.le)]
  refine assertSquare_run _ (hy.of_le hle)
    (CVar.Scoped.add_ (CVar.Scoped.add_ hm.fvar_scoped (CVar.Scoped.scale_ _ (hx.of_le hle)))
      (CVar.scoped_const _ _)) ?_
  simp only [CVar.val_add_, CVar.val_scale_, CVar.val, hx3, CVar.val_of_le hle hx,
    CVar.val_of_le hle hy]
  have h : p.point.y.val st.env.toValuation ^ 2
      = p.point.x.val st.env.toValuation ^ 3 + a * p.point.x.val st.env.toValuation + b := hoc
  linear_combination h

end Snarky.Kimchi
