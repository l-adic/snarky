import Snarky.Pilot.Vocab
import Snarky.Kimchi.Circuit.CurvePoint

/-!
# Pilot: `CurvePoint.check`

A three-leaf composite: `square`, `mul`, `assertSquare`. The run is the existing
`CurvePoint.checkRun`; the law is one rewrite per leaf, scope by `recall`.
-/

namespace Snarky.Pilot

open Snarky Snarky.Kimchi CompElliptic.CurveForms.ShortWeierstrass

variable {F c : Type}

/-- The check's run on an on-curve reading: accepted, landing at `checkRun`, the table
grown. -/
theorem check_facts [Field F] [DecidableEq F] [BasicSystem F c] [Checker F c]
    [LawfulChecker F c] {a b : F} {p : CurvePoint a b (FVar F)} (st : ProverState F)
    (hx : p.point.x.Scoped st) (hy : p.point.y.Scoped st)
    (hoc : OnCurve a b (p.point.x.val st.env.toValuation, p.point.y.val st.env.toValuation)) :
    prove (Checker.holds (F := F) (c := c)) (CurvePoint.check (c := c) p) st.nv st.env
        = .ok ((CurvePoint.checkRun st p).out ()) ∧
      st.env.Le (CurvePoint.checkRun st p).env := by
  generalize hG : CurvePoint.checkRun st p = G
  unfold CurvePoint.checkRun at hG
  extract_lets +lift sq at hG
  have h₁ : squareRun st p.point.x = sq := rfl
  clear_value sq
  subst hG
  have g₁ := squareRun_grants' (st := st) hx rfl
  rw [h₁] at g₁
  have g₂ := mulRun_grants' (st := sq.1) g₁.fvar_scoped (by recall) g₁.fvar_val
    (CVar.val_at rfl g₁.le hx)
  refine ⟨?_, g₁.le.trans g₂.le⟩
  simp only [CurvePoint.check, prove_bind]
  rw [square_run st hx, h₁]
  simp only [Except.bind]
  rw [mul_run (c := c) (y := p.point.x) sq.1 g₁.fvar_scoped (by recall)]
  simp only [Except.bind]
  generalize hm : mulRun sq.1 sq.2 p.point.x = m at g₂ ⊢
  have t1 : p.point.y.Scoped m.1 := by recall
  have t2a : (CVar.add_ (CVar.add_ m.2 (CVar.scale_ a p.point.x)) (CVar.const b)).Scoped m.1 := by
    solve_by_elim (config := { maxDepth := 40 })
      [CVar.scoped_const, CVar.Scoped.add_, CVar.Scoped.scale_, Grants.fvar_scoped, Grants.le,
       Assignments.Le.trans, CVar.Scoped.at]
  have t2b : (CVar.add_ (CVar.add_ m.2 (CVar.scale_ a p.point.x)) (CVar.const b)).Scoped m.1 := by
    solve_by_elim (config := { maxDepth := 40 })
      [CVar.scoped_const, CVar.Scoped.add_, CVar.Scoped.sub_, CVar.Scoped.scale_, not_scoped,
       ProverState.mem_extendMany_head, Grants.fvar_scoped,
       ProverState.le_extendMany, Grants.le, Assignments.Le.trans, Assignments.Le.refl,
       CVar.Scoped.at]
  have t2c : (CVar.add_ (CVar.add_ m.2 (CVar.scale_ a p.point.x)) (CVar.const b)).Scoped m.1 := by
    solve_by_elim (config := { maxDepth := 40 })
      [CVar.scoped_const, CVar.Scoped.add_, CVar.Scoped.scale_,
       ProverState.mem_extendMany_head, Grants.fvar_scoped, Grants.fvar_val,
       ProverState.le_extendMany, Grants.le, Assignments.Le.trans, Assignments.Le.refl,
       CVar.Scoped.at, CVar.val_at]
  exact assertSquare_run m.1 (hy.at (g₁.le.trans g₂.le))
    (CVar.Scoped.add_ (CVar.Scoped.add_ g₂.fvar_scoped (CVar.Scoped.scale_ _
      (hx.at (g₁.le.trans g₂.le)))) (CVar.scoped_const _ _)) (by
    simp only [CVar.val_add_, CVar.val_scale_, CVar.val, g₂.fvar_val,
      CVar.val_at (rfl : p.point.x.val _ = _) (g₁.le.trans g₂.le) hx,
      CVar.val_at (rfl : p.point.y.val _ = _) (g₁.le.trans g₂.le) hy]
    exact hoc)

end Snarky.Pilot
