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
def CheckedPoint.check [Field F] [DecidableEq F] [BasicSystem F c] (a b : F)
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

/-- The check's completeness law: from a point reading as an on-curve value, the run
succeeds and its rows hold at every extension of the final table. -/
theorem CheckedPoint.check_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : F) (p : AffinePoint (FVar F))
    (pv : AffinePoint F) (hcurve : pv.y * pv.y = pv.x ^ 3 + a * pv.x + b) :
    Complete (fun st => CircuitType.ReadsAs (val := AffinePoint F) st p pv)
      (CheckedPoint.check (c := c) a b p) (fun _ _ => True) := by
  have hxpt : ∀ st : ProverState F, CircuitType.ReadsAs (val := AffinePoint F) st p pv →
      CircuitType.ReadsAs (val := F) st p.x pv.x := fun _ h =>
    ⟨CircuitType.scoped_fvar.mpr (scoped_affinePoint.mp h.1).1,
      CircuitType.reads_fvar.mpr (reads_affinePoint.mp h.2).1⟩
  have hypt : ∀ st : ProverState F, CircuitType.ReadsAs (val := AffinePoint F) st p pv →
      CircuitType.ReadsAs (val := F) st p.y pv.y := fun _ h =>
    ⟨CircuitType.scoped_fvar.mpr (scoped_affinePoint.mp h.1).2,
      CircuitType.reads_fvar.mpr (reads_affinePoint.mp h.2).2⟩
  simp only [CheckedPoint.check]
  refine Complete.bind (mid := fun x2 st => CircuitType.ReadsAs (val := F) st x2
      (pv.x * pv.x) ∧ CircuitType.ReadsAs (val := AffinePoint F) st p pv)
    (Complete.imp (fun st h => ⟨hxpt st h, h⟩) (fun _ _ h => h)
      (Complete.frame CircuitType.monotone_readsAs (square_complete p.x pv.x)))
    fun x2 => ?_
  refine Complete.bind (mid := fun x3 st => CircuitType.ReadsAs (val := F) st x3
      (pv.x * pv.x * pv.x) ∧ CircuitType.ReadsAs (val := AffinePoint F) st p pv)
    (Complete.imp (fun st h => ⟨⟨h.1, hxpt st h.2⟩, h.2⟩) (fun _ _ h => h)
      (Complete.frame CircuitType.monotone_readsAs (mul_complete x2 p.x _ _)))
    fun x3 => ?_
  refine Complete.imp (fun st h => ⟨hypt st h.2, ?_⟩) (fun _ _ h => h)
    (assertSquare_complete p.y (CheckedPoint.rhs a b p.x x3) pv.y
      (pv.x * pv.x * pv.x + a * pv.x + b) (by rw [hcurve]; ring))
  obtain ⟨⟨h3s, h3r⟩, hp⟩ := h
  have hx := hxpt st hp
  refine ⟨CircuitType.scoped_fvar.mpr ?_, CircuitType.reads_fvar.mpr ?_⟩
  · exact CVar.Scoped.add_ (CVar.Scoped.add_ (CircuitType.scoped_fvar.mp h3s)
      (CVar.Scoped.scale_ (CircuitType.scoped_fvar.mp hx.1))) (CVar.scoped_const _ _)
  · simp only [CheckedPoint.rhs, CVar.val_add_, CVar.val_scale_, CircuitType.reads_fvar.mp h3r,
      CircuitType.reads_fvar.mp hx.2]
    simp [CVar.val]

instance instCheckedTypeCheckedPoint [Field F] [DecidableEq F] [BasicSystem F c] (a b : F) :
    CheckedType F c (CheckedPoint a b F) (CheckedPoint a b (FVar F)) where
  check p := CheckedPoint.check a b p.pt
  post V p := p.pt.y.val V * p.pt.y.val V = p.pt.x.val V ^ 3 + a * p.pt.x.val V + b
  check_sound V p nv hsat := (builder_spec_iff _ _).mp (CheckedPoint.check_spec a b p.pt) nv hsat
  check_complete := by
    intro _ _ v x hv
    have hcurve : x.pt.y * x.pt.y = x.pt.x ^ 3 + a * x.pt.x + b := by
      have h := hv (fun _ => 0) (CircuitType.constVar x) (CircuitType.reads_constVar _ x)
      simpa [CircuitType.constVar, CircuitType.ofEquiv, CheckedPoint.equivPoint, CVar.val] using h
    exact Complete.imp (fun _ h =>
        ⟨(CircuitType.scoped_ofEquiv (CheckedPoint.equivPoint a b F)
          (CheckedPoint.equivPoint a b (FVar F))).mp h.1,
          (CircuitType.reads_ofEquiv (CheckedPoint.equivPoint a b F)
            (CheckedPoint.equivPoint a b (FVar F))).mp h.2⟩)
      (fun _ _ h => h) (CheckedPoint.check_complete a b v.pt x.pt hcurve)

end Snarky.Kimchi
