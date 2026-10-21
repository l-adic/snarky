import Snarky.Kimchi.Circuit.AddComplete

/-!
# Points allocated on a curve

A point bundle whose allocation checks that it lies on the short-Weierstrass curve
`y² = x³ + a·x + b`: `x² ← square x`, `x³ ← x² · x`, then one square row `y · y = x³ + a·x + b`,
the order and expression shape the deployed allocation emits.

## Main definitions

* `CheckedPoint`: a point, tagged with the curve's `a` and `b`;
* the `CircuitType` and `CheckedType` instances: the point's two cells, and the on-curve check.
-/

namespace Snarky.Kimchi

open Snarky

/-- A point tagged with the curve `y² = x³ + a·x + b` its allocation checks it lies on. -/
structure CheckedPoint {F : Type} (a b : F) (α : Type) where
  /-- The point. -/
  pt : AffinePoint α

variable {F c : Type}

/-- An `CheckedPoint` point is its point. -/
def CheckedPoint.equivPoint (a b : F) (α : Type) : CheckedPoint a b α ≃ AffinePoint α :=
  ⟨CheckedPoint.pt, CheckedPoint.mk, fun _ => rfl, fun _ => rfl⟩

instance instCircuitTypeCheckedPoint (a b : F) :
    CircuitType F (CheckedPoint a b F) (CheckedPoint a b (FVar F)) :=
  CircuitType.ofEquiv (CheckedPoint.equivPoint a b F) (CheckedPoint.equivPoint a b (FVar F))

/-- The curve equation's right-hand side at `x`, as the check builds it from `x³`. -/
def CheckedPoint.rhs [Field F] [DecidableEq F] (a b : F) (x x3 : FVar F) : FVar F :=
  CVar.add_ (CVar.add_ x3 (CVar.scale_ a x)) (.const b)

/-- The on-curve check: `x² ← square x`, `x³ ← x² · x`, then `y · y = x³ + a·x + b`. -/
def CheckedPoint.check [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (a b : F)
    (p : AffinePoint (FVar F)) :
    CircuitM F c PUnit := do
  let x2 ← square p.x
  let x3 ← mul x2 p.x
  assertSquare p.y (CheckedPoint.rhs a b p.x x3)

open Std.WP in
/-- Under any valuation satisfying the emitted constraints, the point reads on the curve
`y² = x³ + a·x + b`. -/
theorem CheckedPoint.check_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] {V : Valuation F} (a b : F) (p : AffinePoint (FVar F)) :
    ⦃fun _ => True⦄ CheckedPoint.check (c := Builder V c) a b p
    ⦃fun _ _ => p.y.val V * p.y.val V = p.x.val V ^ 3 + a * p.x.val V + b⦄ := by
  simp only [CheckedPoint.check]
  vcgen
  rename_i h2 _ h3 _ _ hsq
  rw [hsq]
  simp only [CheckedPoint.rhs, CVar.val_add_, CVar.val_scale_, h3, h2]
  simp [CVar.val]
  ring

open Std.WP in
/-- The check's law at the prover's reading: from a point reading an on-curve value, the run
succeeds. -/
theorem CheckedPoint.check_prover_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : F) (p : AffinePoint (FVar F))
    (pv : AffinePoint F) (hcurve : pv.y * pv.y = pv.x ^ 3 + a * pv.x + b) :
    ⦃Prover.Reads p pv⦄ CheckedPoint.check (c := Prover c) a b p ⦃fun _ ↦ ⊤⦄ := by
  have hsq := Prover.square_spec (c := c) p.x pv.x
  have hmul := fun x2 : FVar F ↦ Prover.mul_spec (c := c) x2 p.x (pv.x * pv.x) pv.x
  have hrhs := fun x3 : FVar F ↦
    Prover.assertSquare_spec (c := c) p.y (CheckedPoint.rhs a b p.x x3) pv.y
  have hpow : pv.x ^ 3 = pv.x * pv.x * pv.x := by ring
  simp only [CheckedPoint.check]
  vcgen [hsq, hmul, hrhs]
  all_goals prover_assert with
    (intros; simp_all (maxDischargeDepth := 3) [Prover.reads_affinePoint_apply,
      Prover.Reads.fvar_apply, CheckedPoint.rhs,
      CVar.val_add_, CVar.val_scale_, CVar.Scoped.add_, CVar.Scoped.scale_, CVar.scoped_const,
      CVar.val])

instance instCheckedTypeCheckedPoint [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : F) :
    CheckedType F c (CheckedPoint a b F) (CheckedPoint a b (FVar F)) where
  check p := CheckedPoint.check a b p.pt
  post V p := p.pt.y.val V * p.pt.y.val V = p.pt.x.val V ^ 3 + a * p.pt.x.val V + b
  check_sound V p nv hsat := (builder_spec_iff _ _).mp (CheckedPoint.check_spec a b p.pt) nv hsat

open Std.WP in
/-- The on-curve check keeps the point's reading: its contract at the prover's reading. -/
instance instCheckSpecCheckedPoint [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : F) :
    Prover.CheckSpec F c (CheckedPoint a b F) (CheckedPoint a b (FVar F)) where
  check v x hv := by
    have hcurve : x.pt.y * x.pt.y = x.pt.x ^ 3 + a * x.pt.x + b :=
      hv (fun _ => 0) (CircuitType.constVar x) (CircuitType.reads_constVar _ x)
    have h := CheckedPoint.check_prover_spec (c := c) a b v.pt x.pt hcurve
    show ⦃Prover.Reads v.pt x.pt⦄ CheckedPoint.check (c := Prover c) a b v.pt
      ⦃fun _ ↦ Prover.Reads v.pt x.pt⦄
    vcgen [h]
    all_goals prover_assert

end Snarky.Kimchi
