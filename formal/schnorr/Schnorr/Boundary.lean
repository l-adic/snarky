import Schnorr.Laws
import Snarky.Kimchi.Backend.Compile

/-!
# The CS-satisfaction boundary — the fragment seam

The endpoint laws packaged through the whole-circuit pipeline
(`formal/docs/circuit-verifier-faithfulness.md`, layer 3): the statement is the
public input through its `CircuitType` encoding, and its `CheckedType` pays the two
on-curve checks at the seam.

- `verifyCircuit_compile_sound` — a valuation satisfying `compile verifyCircuit`'s
  constraints, reading any five cells at `inputVar`, certifies genuine nonzero wire
  points at the read coordinates, a nonzero response decode, and — off the ladder's
  forbidden band — `verify` at the statement's canonical decode. On-curve-ness is
  forced by the input check's rows, not hypothesized.
- `verifyCircuit_solve_complete` — on a statement `verify` accepts, honestly
  encoded, `solve` at the kimchi checker succeeds (the input check's honest run
  through `CurvePoint.check_complete_spec`) and its table reads the statement.
-/

namespace Schnorr

open Snarky Snarky.Kimchi CompElliptic.Fields.Pasta
open Std.Do

open Kimchi.Gate.VarBaseMul (forbiddenValues) in
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass in
/-- The seam program — the statement's check, then the verifier — under one Sound
triple: the check's rows force both point readings on-curve; the body carries the
endpoint's certificate. -/
private theorem checkedBody_spec (stv : Statement.Raw (FVar Fq))
    (Q : PostCond PUnit (.arg (BuilderState Fq) .pure)) :
    ⦃Sound (fun V (_ : PUnit) =>
        OnCurve Vesta.curve.A Vesta.curve.B (stv.pk.x.val V, stv.pk.y.val V) ∧
        OnCurve Vesta.curve.A Vesta.curve.B (stv.u.x.val V, stv.u.y.val V) ∧
        (∀ (pkP uP : SWPoint Vesta.curve) (zt : Type1 Fq), pkP ≠ 0 → uP ≠ 0 →
          readVal (val := Statement.Raw Fq) V stv
            = (⟨⟨pkP.x, pkP.y⟩, ⟨uP.x, uP.y⟩, zt⟩ : Statement.Raw Fq) →
          zt.fromShifted ≠ (0 : Fp) ∧
          (zt.fromShiftedZ ∉ forbiddenValues PALLAS_BASE_CARD →
            verify ⟨pkP, uP, zt.fromShifted⟩ = true))) Q⦄
    (do CheckedType.check (c := KimchiConstraint Fq) stv
        verifyCircuit (c := KimchiConstraint Fq) stv)
    ⦃Q⦄ := by
  have hpk := CurvePoint.check_spec (F := Fq) (c := KimchiConstraint Fq)
    (⟨stv.pk⟩ : CurvePoint Vesta.curve.A Vesta.curve.B (FVar Fq))
  have hu := CurvePoint.check_spec (F := Fq) (c := KimchiConstraint Fq)
    (⟨stv.u⟩ : CurvePoint Vesta.curve.A Vesta.curve.B (FVar Fq))
  have hbody := verifyCircuit_spec stv
  simp only [show CheckedType.check (c := KimchiConstraint Fq) stv
      = Statement.Raw.check stv from rfl, Statement.Raw.check]
  mvcgen [hpk, hu, hbody]
  rename_i s hpre
  intro _ _ hpkC
  mvcgen [hu, hbody]
  intro _ _ huC
  mvcgen [hbody]
  intro r nv hmain
  exact hpre r nv hpkC huC hmain

open Kimchi.Gate.VarBaseMul (forbiddenValues) in
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass in
/-- **The satisfaction boundary.** A valuation satisfying every compiled constraint
(each the verified gate's own predicate at the payload's operands), reading ANY five
cells at the input bundle, certifies: the point readings are genuine nonzero wire
points — the input check's rows force them on-curve, and the `(0, 0)` sentinel is
off-curve — the response decode is nonzero, and, off the ladder's forbidden band,
`verify` accepts at the statement's canonical decode. No curve-membership hypothesis
survives. -/
theorem verifyCircuit_compile_sound
    (px py ux uy : Fq) (zt : Type1 Fq)
    (hband : zt.fromShiftedZ ∉ forbiddenValues PALLAS_BASE_CARD)
    (V : Valuation Fq)
    (hsat : ∀ con ∈ (compile (a := Statement.Raw Fq) (b := PUnit)
        (verifyCircuit (c := KimchiConstraint Fq))).constraints,
      ConstraintHolds.Holds V con)
    (hin : readVal V (inputVar (F := Fq) (a := Statement.Raw Fq))
      = (⟨⟨px, py⟩, ⟨ux, uy⟩, zt⟩ : Statement.Raw Fq)) :
    ∃ (pkP uP : SWPoint Vesta.curve),
      pkP.x = px ∧ pkP.y = py ∧ uP.x = ux ∧ uP.y = uy ∧ pkP ≠ 0 ∧ uP ≠ 0 ∧
      zt.fromShifted ≠ (0 : Fp) ∧
      verify ⟨pkP, uP, zt.fromShifted⟩ = true := by
  have hplain := (sound_spec_iff _ _).mp
    (checkedBody_spec (inputVar (F := Fq) (a := Statement.Raw Fq)))
  obtain ⟨hpkC, huC, hmain⟩ := hplain V 5
    (fun con hcon => hsat con (mem_compile_of_mem_body hcon))
  rw [readVal_statementRaw] at hin
  -- the reading pins the cells to the given coordinates, projectionwise
  have hpx : (inputVar (F := Fq) (a := Statement.Raw Fq)).pk.x.val V = px :=
    congrArg (fun s => s.pk.x) hin
  have hpy : (inputVar (F := Fq) (a := Statement.Raw Fq)).pk.y.val V = py :=
    congrArg (fun s => s.pk.y) hin
  have hux : (inputVar (F := Fq) (a := Statement.Raw Fq)).u.x.val V = ux :=
    congrArg (fun s => s.u.x) hin
  have huy : (inputVar (F := Fq) (a := Statement.Raw Fq)).u.y.val V = uy :=
    congrArg (fun s => s.u.y) hin
  have hpkC' : OnCurve Vesta.curve.A Vesta.curve.B (px, py) := by
    rw [← hpx, ← hpy]; exact hpkC
  have huC' : OnCurve Vesta.curve.A Vesta.curve.B (ux, uy) := by
    rw [← hux, ← huy]; exact huC
  -- an on-curve pair is a nonzero wire point: the sentinel (0, 0) is off-curve
  have hne : ∀ (x y : Fq) (h : OnCurve Vesta.curve.A Vesta.curve.B (x, y)),
      (⟨x, y, Or.inl h⟩ : SWPoint Vesta.curve) ≠ 0 := by
    intro x y h h0
    have hx : x = 0 := (congrArg SWPoint.x h0).trans rfl
    have hy : y = 0 := (congrArg SWPoint.y h0).trans rfl
    subst hx
    subst hy
    exact absurd h (by decide)
  obtain ⟨hnz, himp⟩ := hmain ⟨px, py, Or.inl hpkC'⟩ ⟨ux, uy, Or.inl huC'⟩ zt
    (hne _ _ hpkC') (hne _ _ huC') (by rw [readVal_statementRaw]; exact hin)
  exact ⟨⟨px, py, Or.inl hpkC'⟩, ⟨ux, uy, Or.inl huC'⟩, rfl, rfl, rfl, rfl,
    hne _ _ hpkC', hne _ _ huC', hnz, himp hband⟩

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass in
/-- The statement check's honest prover run: it succeeds on any table reading the
statement as on-curve coordinate pairs — the two `CurvePoint` completeness laws in
sequence. Generic in the statement bundle so consumers instantiate without deep
unfolding. -/
private theorem check_complete (stv : Statement.Raw (FVar Fq))
    (pkx pky uxv uyv : Fq) (zv : Type1 Fq)
    (hpkOC : OnCurve Vesta.curve.A Vesta.curve.B (pkx, pky))
    (huOC : OnCurve Vesta.curve.A Vesta.curve.B (uxv, uyv))
    (Q : PostCond PUnit (.arg (ProverState Fq) (.except EvalError .pure))) :
    ⦃Complete (fun env => Reads env stv
        (⟨⟨pkx, pky⟩, ⟨uxv, uyv⟩, zv⟩ : Statement.Raw Fq))
      (fun _ _ _ => True) Q⦄
    (CheckedType.check (F := Fq) (c := KimchiProverC Fq) stv)
    ⦃Q⦄ := by
  intro st hpre
  obtain ⟨hrd, hk⟩ := hpre
  rw [reads_statementRaw_iff] at hrd
  obtain ⟨hpkx, hpky, hux, huy, -⟩ := hrd
  simp only [show CheckedType.check (F := Fq) (c := KimchiProverC Fq) stv
      = Statement.Raw.check stv from rfl,
    Statement.Raw.check, WPMonad.wp_bind, PredTrans.apply_Bind_bind]
  refine CurvePoint.check_complete_spec _ _ st
    ⟨⟨isOk_of_eq hpkx, isOk_of_eq hpky, fun xv yv hx hy => ?_⟩,
      fun _ st₁ _ hle₁ => ?_⟩
  · rw [hpkx] at hx
    rw [hpky] at hy
    injection hx with hx
    injection hy with hy
    subst hx
    subst hy
    exact hpkOC
  have hux₁ := CVar.eval_le hle₁ hux
  have huy₁ := CVar.eval_le hle₁ huy
  refine CurvePoint.check_complete_spec _ _ st₁
    ⟨⟨isOk_of_eq hux₁, isOk_of_eq huy₁, fun xv yv hx hy => ?_⟩,
      fun _ st₂ _ hle₂ => ?_⟩
  · rw [hux₁] at hx
    rw [huy₁] at hy
    injection hx with hx
    injection hy with hy
    subst hx
    subst hy
    exact huOC
  exact hk ⟨⟩ st₂ trivial (hle₁.trans hle₂)

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass in
/-- **The constructive boundary.** On a statement `verify` accepts — honestly
encoded, nondegenerate, in the ladder regime — the whole-circuit `solve` at the
kimchi checker succeeds, and the returned table reads the statement at the input
bundle. The input check's honest run succeeds because the wire points are on-curve. -/
private theorem verifyCircuit_solve_complete
    (stP : Statement) (zt : Type1 Fq)
    (hpk0 : stP.pk ≠ 0) (hu0 : stP.u ≠ 0) (hz0 : stP.z ≠ 0)
    (hreg : HasCurve.vesta.LadderRegime 255 (zt.fromShiftedZ))
    (henc : zt.fromShifted = stP.z)
    (hacc : verify stP = true) :
    ∃ env : Assignments Fq,
      solve (b := PUnit) (Checker.holds (F := Fq) (c := KimchiConstraint Fq))
          (verifyCircuit (c := KimchiConstraint Fq))
          (⟨⟨stP.pk.x, stP.pk.y⟩, ⟨stP.u.x, stP.u.y⟩, zt⟩ : Statement.Raw Fq)
        = .ok (PUnit.unit, env) ∧
      Reads env (inputVar (F := Fq) (a := Statement.Raw Fq))
        (⟨⟨stP.pk.x, stP.pk.y⟩, ⟨stP.u.x, stP.u.y⟩, zt⟩ : Statement.Raw Fq) := by
  obtain ⟨env₀, hseed, hlook, hfresh⟩ := solve_seed (F := Fq)
    (a := Statement.Raw Fq)
    (⟨⟨stP.pk.x, stP.pk.y⟩, ⟨stP.u.x, stP.u.y⟩, zt⟩ : Statement.Raw Fq)
  have h0 : env₀ 0 = some stP.pk.x := hlook 0 (by decide)
  have h1 : env₀ 1 = some stP.pk.y := hlook 1 (by decide)
  have h2 : env₀ 2 = some stP.u.x := hlook 2 (by decide)
  have h3 : env₀ 3 = some stP.u.y := hlook 3 (by decide)
  have h4 : env₀ 4 = some zt.val := hlook 4 (by decide)
  have hreads : Reads env₀ (inputVar (F := Fq) (a := Statement.Raw Fq))
      (⟨⟨stP.pk.x, stP.pk.y⟩, ⟨stP.u.x, stP.u.y⟩, zt⟩ : Statement.Raw Fq) := by
    rw [reads_statementRaw_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show (CVar.var 0).eval env₀ = .ok stP.pk.x
      simp [CVar.eval, h0]
    · show (CVar.var 1).eval env₀ = .ok stP.pk.y
      simp [CVar.eval, h1]
    · show (CVar.var 2).eval env₀ = .ok stP.u.x
      simp [CVar.eval, h2]
    · show (CVar.var 3).eval env₀ = .ok stP.u.y
      simp [CVar.eval, h3]
    · show (CVar.var 4).eval env₀ = .ok zt.val
      simp [CVar.eval, h4]
  -- the input check's honest run: both wire points are on-curve
  obtain ⟨q, hq, -, hleC⟩ := (complete_spec_iff
      (CheckedType.check (F := Fq) (c := KimchiProverC Fq)
        (inputVar (F := Fq) (a := Statement.Raw Fq))) _ _).mp
    (check_complete (inputVar (F := Fq) (a := Statement.Raw Fq))
      stP.pk.x stP.pk.y stP.u.x stP.u.y zt
      (SWPoint.onCurve_of_ne_zero hpk0) (SWPoint.onCurve_of_ne_zero hu0))
    ⟨5, env₀, hfresh⟩ hreads
  have hfresh₁ : q.assignments.FreshFrom q.nextVar := prove_freshFrom hfresh hq
  obtain ⟨out, hrun, hle⟩ := verifyCircuit_complete_spec
    (inputVar (F := Fq) (a := Statement.Raw Fq)) stP zt
    hpk0 hu0 hz0 hreg henc hacc ⟨q.nextVar, q.assignments, hfresh₁⟩
    (Reads.le hleC hreads)
  exact ⟨out.assignments, solve_punit_ok hseed hq hrun,
    Reads.le (hleC.trans hle) hreads⟩

open Kimchi.Gate.VarBaseMul (forbiddenValues) in
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass in
/-- The constructive boundary at the canonical encode: for an accepted, nondegenerate
statement whose response's encode sits off the forbidden band, `solve` succeeds at
`Type1.toShifted` — the encoding hypotheses discharged by `toShifted_ladderRegime`. -/
theorem complete
    (stP : Statement) (hpk0 : stP.pk ≠ 0) (hu0 : stP.u ≠ 0) (hz0 : stP.z ≠ 0)
    (hband : (Type1.toShifted stP.z).fromShiftedZ
      ∉ forbiddenValues PALLAS_BASE_CARD)
    (hacc : verify stP = true) :
    ∃ env : Assignments Fq,
      solve (b := PUnit) (Checker.holds (F := Fq) (c := KimchiConstraint Fq))
          (verifyCircuit (c := KimchiConstraint Fq))
          (⟨⟨stP.pk.x, stP.pk.y⟩, ⟨stP.u.x, stP.u.y⟩,
            Type1.toShifted stP.z⟩ : Statement.Raw Fq)
        = .ok (PUnit.unit, env) ∧
      Reads env (inputVar (F := Fq) (a := Statement.Raw Fq))
        (⟨⟨stP.pk.x, stP.pk.y⟩, ⟨stP.u.x, stP.u.y⟩,
          Type1.toShifted stP.z⟩ : Statement.Raw Fq) := by
  obtain ⟨henc, hreg⟩ := toShifted_ladderRegime stP.z hband
  exact verifyCircuit_solve_complete stP _ hpk0 hu0 hz0 hreg henc hacc

end Schnorr
