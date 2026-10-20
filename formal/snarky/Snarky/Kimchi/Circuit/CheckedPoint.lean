import Snarky.Kimchi.Circuit.AddComplete

set_option mvcgen.warning false

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

open Std.Do Snarky

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

/-- Under any valuation satisfying the emitted constraints, the point reads on the curve
`y² = x³ + a·x + b`. -/
theorem CheckedPoint.check_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] {V : Valuation F} (a b : F) (p : AffinePoint (FVar F)) :
    ⦃⌜True⌝⦄ CheckedPoint.check (c := Builder V c) a b p
    ⦃⇓ _ _ => ⌜p.y.val V * p.y.val V = p.x.val V ^ 3 + a * p.x.val V + b⌝⦄ := by
  simp only [CheckedPoint.check]
  mvcgen
  rename_i _ _ h2 _ _ h3 _ _
  intro hsq
  rw [hsq]
  simp only [CheckedPoint.rhs, CVar.val_add_, CVar.val_scale_, h3, h2]
  simp [CVar.val]
  ring

/-- The check's law at the prover's reading: from a point reading as an on-curve value, the
run succeeds and the state only grows. -/
theorem CheckedPoint.check_prover_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : F) (p : AffinePoint (FVar F))
    (pv : AffinePoint F) (hcurve : pv.y * pv.y = pv.x ^ 3 + a * pv.x + b)
    (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ CircuitType.ReadsAs (val := AffinePoint F) st₀ p pv⌝⦄
    CheckedPoint.check (c := Prover c) a b p
    ⦃⇓ _ s' => ⌜st₀ ≤ s'⌝⦄ := by
  simp only [CheckedPoint.check]
  mvcgen
  all_goals grind [Prover.Reg.iff, CircuitType.ReadsAs, scoped_affinePoint, reads_affinePoint,
    CheckedPoint.rhs, CVar.Scoped.add_, CVar.Scoped.scale_, CVar.scoped_const, CVar.val_add_,
    CVar.val_scale_, CVar.val, CVar.Scoped.of_le, ProverState.read_of_le, pow_succ, pow_zero]

instance instCheckedTypeCheckedPoint [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : F) :
    CheckedType F c (CheckedPoint a b F) (CheckedPoint a b (FVar F)) where
  check p := CheckedPoint.check a b p.pt
  post V p := p.pt.y.val V * p.pt.y.val V = p.pt.x.val V ^ 3 + a * p.pt.x.val V + b
  check_sound V p nv hsat := (builder_spec_iff _ _).mp (CheckedPoint.check_spec a b p.pt) nv hsat

/-- The on-curve check's law, at the prover's reading. -/
instance instWPCheckedTypeCheckedPoint [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : F) :
    WPCheckedType F c (CheckedPoint a b F) (CheckedPoint a b (FVar F)) :=
  ⟨fun v x s hr hv => by
    have hcurve : x.pt.y * x.pt.y = x.pt.x ^ 3 + a * x.pt.x + b := by
      have h := hv (fun _ => 0) (CircuitType.constVar x) (CircuitType.reads_constVar _ x)
      exact h
    have hpt : CircuitType.ReadsAs (val := AffinePoint F) s v.pt x.pt :=
      ⟨(CircuitType.scoped_ofEquiv (CheckedPoint.equivPoint a b F)
          (CheckedPoint.equivPoint a b (FVar F))).mp hr.1,
        (CircuitType.reads_ofEquiv (CheckedPoint.equivPoint a b F)
          (CheckedPoint.equivPoint a b (FVar F))).mp hr.2⟩
    exact CheckedPoint.check_prover_spec a b v.pt x.pt hcurve s s ⟨rfl, hpt⟩⟩

end Snarky.Kimchi
