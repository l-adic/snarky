import Snarky.Kimchi.Circuit.AddComplete
import Snarky.DSL.Field
import Snarky.DSL.Assert

/-!
# The curve-tagged point

Port of PS `WeierstrassAffinePoint`
(packages/snarky-curves/src/Snarky/Data/EllipticCurve.purs): an affine point whose TYPE
names its curve. The plain `AffinePoint` stays checks-free (the `genericCheck`
convention, `Circuit/AddComplete`); a statement carries THIS type where its wire
refinement is a genuine curve point, so the whole-circuit seam can force the public
reading on-curve.

Name map: PS's phantom tag `g` with its `WeierstrassCurve f g` params class becomes the
two coefficient indices `a b : F` — the same information, value-indexed.

The on-curve check (OCaml `assert_on_curve`) is here too: it is what makes the tag real,
and it is the one checked type whose rows constrain the decoded value.
-/

namespace Snarky.Kimchi

open Snarky

variable {F : Type}

/-- An affine point tagged with its curve's coefficients (PS
`WeierstrassAffinePoint g f`). The tag is phantom on the data — the constraint arrives
through `CheckedType`, not the carrier. -/
structure CurvePoint (a b : F) (α : Type) where
  /-- The untagged coordinates. -/
  point : AffinePoint α

/-- The tag is phantom: a tagged point is its point. -/
@[simps apply symm_apply] def CurvePoint.equivPoint {a b : F} {α : Type} :
    CurvePoint a b α ≃ AffinePoint α where
  toFun p := p.point
  invFun p := ⟨p⟩
  left_inv _ := rfl
  right_inv _ := rfl

open CompElliptic.Curves.Pasta in
/-- A point tagged with Vesta's coefficients — what an `Fq`-circuit's public points are. -/
abbrev VestaPoint := CurvePoint (a := Vesta.curve.A) (b := Vesta.curve.B)

/-- The tagged point encodes exactly as its coordinates, `[x, y]`. -/
instance instCurvePointCircuitType {a b : F} :
    CircuitType F (CurvePoint a b F) (CurvePoint a b (FVar F)) :=
  CircuitType.ofEquiv CurvePoint.equivPoint CurvePoint.equivPoint

/-- A tagged point is in scope when its coordinates are. -/
@[simp] theorem scoped_curvePoint {a b : F} {st : ProverState F}
    {p : CurvePoint a b (FVar F)} :
    CircuitType.Scoped (val := CurvePoint a b F) st p ↔
      p.point.x.Scoped st ∧ p.point.y.Scoped st :=
  (CircuitType.scoped_ofEquiv _ _).trans scoped_affinePoint

/-- A tagged point reads coordinatewise — the tag is phantom on the reading. -/
@[simp] theorem reads_curvePoint [Add F] [Mul F] [Zero F] {a b : F} {V : Valuation F}
    {p : CurvePoint a b (FVar F)} {P : CurvePoint a b F} :
    CircuitType.Reads V p P ↔
      p.point.x.val V = P.point.x ∧ p.point.y.val V = P.point.y :=
  (CircuitType.reads_ofEquiv _ _).trans reads_affinePoint


/-! ## The on-curve check -/

section Check

variable {c : Type} [Field F] [DecidableEq F] [BasicSystem F c] {a b : F}

/-- The on-curve check circuit (OCaml `assert_on_curve`, snarky_curve.ml): the constraint
shape is Square, then `r1cs`, then Square — deployed rows, not a generic polynomial
identity. It ALLOCATES: `x²` and `x³` are witnessed, since `CVar` is affine. -/
def CurvePoint.check (p : CurvePoint a b (FVar F)) : CircuitM F c PUnit := do
  let x2 ← square p.point.x
  let x3 ← mul x2 p.point.x
  assertSquare p.point.y ((x3.add_ (CVar.scale_ a p.point.x)).add_ (.const b))

open Std.Do in
/-- The check's rows force the reading on-curve. -/
@[spec] theorem CurvePoint.check_spec {V : Valuation F} [ConstraintHolds F c]
    [LawfulBasicSystem F c] (p : CurvePoint a b (FVar F)) :
    ⦃⌜True⌝⦄
    CurvePoint.check (c := Builder V c) p
    ⦃⇓ _ _ => ⌜CompElliptic.CurveForms.ShortWeierstrass.OnCurve a b
        (p.point.x.val V, p.point.y.val V)⌝⦄ := by
  simp only [CurvePoint.check]
  mvcgen
  rename_i hx2 _ _ hx3 _ _
  intro hsq
  show p.point.y.val V ^ 2 = p.point.x.val V ^ 3 + a * p.point.x.val V + b
  rw [CVar.val_add_, CVar.val_add_, CVar.val_scale_, hx3, hx2] at hsq
  have hb : (CVar.const b).val V = b := rfl
  rw [hb] at hsq
  linear_combination hsq

/-- An on-curve reading pays the check: the run succeeds and its rows are satisfied at
every extension of where it lands. `OnCurve` is the hypothesis because the value type is
an unrefined coordinate pair — the check enforces exactly this. -/
theorem CurvePoint.check_complete [ConstraintHolds F c] [LawfulBasicSystem F c]
    (p : CurvePoint a b (FVar F)) (P : CurvePoint a b F)
    (hoc : CompElliptic.CurveForms.ShortWeierstrass.OnCurve a b (P.point.x, P.point.y)) :
    Complete (F := F) (c := c)
      (fun st => CircuitType.ReadsAs (val := CurvePoint a b F) st p P)
      (CurvePoint.check (c := c) p) (fun _ _ => True) := by
  intro st hp
  rw [CircuitType.ReadsAs, CircuitType.scoped_ofEquiv, CircuitType.reads_ofEquiv,
    scoped_affinePoint, reads_affinePoint] at hp
  obtain ⟨⟨hsx, hsy⟩, hvx, hvy⟩ := hp
  have hx : CircuitType.ReadsAs (val := F) st p.point.x P.point.x :=
    ⟨CircuitType.scoped_fvar.mpr hsx, CircuitType.reads_fvar.mpr hvx⟩
  have hy : CircuitType.ReadsAs (val := F) st p.point.y P.point.y :=
    ⟨CircuitType.scoped_fvar.mpr hsy, CircuitType.reads_fvar.mpr hvy⟩
  obtain ⟨x2, st₁, hrun₁, hsat₁, h2⟩ := square_complete (c := c) p.point.x P.point.x st hx
  obtain ⟨x3, st₂, hrun₂, hsat₂, h3⟩ :=
    mul_complete (c := c) x2 p.point.x (P.point.x * P.point.x) P.point.x st₁
      ⟨h2, hx.mono hrun₁.nv_le hrun₁.le⟩
  have hrhs : CircuitType.ReadsAs (val := F) st₂
      ((x3.add_ (CVar.scale_ a p.point.x)).add_ (.const b))
      (P.point.x * P.point.x * P.point.x + a * P.point.x + b) := by
    have hx₂ := hx.mono (Nat.le_trans hrun₁.nv_le hrun₂.nv_le) (hrun₁.le.trans hrun₂.le)
    refine ⟨CircuitType.scoped_fvar.mpr
      (((CircuitType.scoped_fvar.mp h3.1).add_
        (CVar.Scoped.scale_ (CircuitType.scoped_fvar.mp hx₂.1))).add_ (CVar.scoped_const _ _)),
      CircuitType.reads_fvar.mpr ?_⟩
    rw [CVar.val_add_, CVar.val_add_, CVar.val_scale_,
      CircuitType.reads_fvar.mp h3.2, CircuitType.reads_fvar.mp hx₂.2]
    rfl
  obtain ⟨_, st₃, hrun₃, hsat₃, -⟩ :=
    assertSquare_complete (c := c) p.point.y
      ((x3.add_ (CVar.scale_ a p.point.x)).add_ (.const b))
      P.point.y (P.point.x * P.point.x * P.point.x + a * P.point.x + b)
      (by
        have hoc' : P.point.y ^ 2 = P.point.x ^ 3 + a * P.point.x + b := hoc
        linear_combination hoc')
      st₂ ⟨hy.mono (Nat.le_trans hrun₁.nv_le hrun₂.nv_le) (hrun₁.le.trans hrun₂.le), hrhs⟩
  exact ⟨PUnit.unit, st₃, hrun₁.bind (hrun₂.bind hrun₃), fun hnv hle =>
    Sat.bind hrun₁
      (hsat₁ (Nat.le_trans hrun₂.nv_le (Nat.le_trans hrun₃.nv_le hnv))
        (hrun₂.le.trans (hrun₃.le.trans hle)))
      (Sat.bind hrun₂ (hsat₂ (Nat.le_trans hrun₃.nv_le hnv) (hrun₃.le.trans hle))
        (hsat₃ hnv hle)), trivial⟩

/-- The tagged point's well-formedness: the on-curve rows. This is the one checked type
whose rows constrain the decoded value, so its admissible values are exactly the curve's
points — `valid_curvePoint`. -/
instance instCurvePointCheckedType :
    CheckedType F c (CurvePoint a b F) (CurvePoint a b (FVar F)) where
  check := CurvePoint.check
  post V p := CompElliptic.CurveForms.ShortWeierstrass.OnCurve a b
    (p.point.x.val V, p.point.y.val V)
  check_sound V p nv h :=
    (builder_spec_iff (CurvePoint.check (c := Builder V c) p) _).mp (CurvePoint.check_spec p) nv h
  check_complete p P hv :=
    CurvePoint.check_complete p P
      (hv (fun _ => 0) ⟨⟨.const P.point.x, .const P.point.y⟩⟩ rfl)

/-- A tagged point is admissible exactly when it is on the curve — the one place where a
checked type's rows pin the value, and the reason the whole-circuit completeness law is
stated over the curve's points rather than over all coordinate pairs. -/
@[simp] theorem valid_curvePoint {P : CurvePoint a b F} :
    CheckedType.Valid (F := F) (c := c) (var := CurvePoint a b (FVar F)) P ↔
      CompElliptic.CurveForms.ShortWeierstrass.OnCurve a b (P.point.x, P.point.y) := by
  constructor
  · exact fun h => h (fun _ => 0) ⟨⟨.const P.point.x, .const P.point.y⟩⟩ rfl
  · intro h V w hw
    rw [CircuitType.reads_ofEquiv, reads_affinePoint] at hw
    show CompElliptic.CurveForms.ShortWeierstrass.OnCurve a b
      (w.point.x.val V, w.point.y.val V)
    rw [show w.point.x.val V = P.point.x from hw.1, show w.point.y.val V = P.point.y from hw.2]
    exact h

end Check

end Snarky.Kimchi
