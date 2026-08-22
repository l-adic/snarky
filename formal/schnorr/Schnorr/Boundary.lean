import Schnorr.Laws
import Snarky.Kimchi.Backend.Compile

/-!
# The CS-satisfaction boundary — the fragment seam

The endpoint laws packaged through the whole-circuit pipeline
(`formal/docs/circuit-verifier-faithfulness.md`, layer 3): the statement is the
public input through its `CircuitType` encoding, and its `CheckedType` pays the two
on-curve checks at the seam.

- `verifyCircuit_compile_sound` — a valuation satisfying `compile verifyCircuit`'s
  constraints reads, at `inputVar`, a raw statement `verifyRaw` accepts (off the
  ladder's forbidden band). The guard's facts — both points on-curve, the response
  decode nonzero — are forced by the input check's rows, not hypothesized.
- `complete` — on a raw statement `verifyRaw` accepts, `solve` at the kimchi checker
  succeeds (the guard supplies what the input check's honest run needs) and its table
  reads it.
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
        OnCurve Vesta.curve.A Vesta.curve.B (stv.pk.point.x.val V, stv.pk.point.y.val V) ∧
        OnCurve Vesta.curve.A Vesta.curve.B (stv.u.point.x.val V, stv.u.point.y.val V) ∧
        (∀ (pkP uP : SWPoint Vesta.curve) (zt : Type1 Fq), pkP ≠ 0 → uP ≠ 0 →
          readVal (val := Statement.Raw Fq) V stv
            = (⟨⟨⟨pkP.x, pkP.y⟩⟩, ⟨⟨uP.x, uP.y⟩⟩, zt⟩ : Statement.Raw Fq) →
          zt.fromShifted ≠ (0 : Fp) ∧
          (zt.fromShiftedZ ∉ forbiddenValues PALLAS_BASE_CARD →
            verify ⟨pkP, uP, zt.fromShifted⟩ = true))) Q⦄
    (do CheckedType.check (c := KimchiConstraint Fq) stv
        verifyCircuit (c := KimchiConstraint Fq) stv)
    ⦃Q⦄ := by
  have hbody := verifyCircuit_spec stv
  have hprog : CheckedType.check (c := KimchiConstraint Fq) stv
      = (do CurvePoint.check (c := KimchiConstraint Fq) stv.pk
            CurvePoint.check (c := KimchiConstraint Fq) stv.u
            pure PUnit.unit) := rfl
  simp only [hprog]
  mvcgen [hbody]
  rename_i s hpre
  intro _ _ hpkC
  mvcgen [hbody]
  intro _ _ huC
  mvcgen [hbody]
  intro r nv hmain
  exact hpre r nv hpkC huC hmain

open Kimchi.Gate.VarBaseMul (forbiddenValues) in
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass in
/-- **The satisfaction boundary.** A valuation satisfying every compiled constraint
(each the verified gate's own predicate at the payload's operands) reads, at the input
bundle, a raw statement the wire verifier accepts — off the ladder's forbidden band.
`verifyRaw`'s guard is exactly what the input check's rows force: both points on-curve,
the response decode nonzero. No curve-membership hypothesis survives. -/
theorem verifyCircuit_compile_sound (V : Valuation Fq)
    (hsat : ∀ con ∈ (compile (a := Statement.Raw Fq) (b := PUnit)
        (verifyCircuit (c := KimchiConstraint Fq))).constraints,
      ConstraintHolds.Holds V con)
    (hband : (readVal (val := Statement.Raw Fq) V
        (inputVar (F := Fq) (a := Statement.Raw Fq))).z.fromShiftedZ
      ∉ forbiddenValues PALLAS_BASE_CARD) :
    verifyRaw (readVal (val := Statement.Raw Fq) V
      (inputVar (F := Fq) (a := Statement.Raw Fq))) = true := by
  have hplain := (sound_spec_iff _ _).mp
    (checkedBody_spec (inputVar (F := Fq) (a := Statement.Raw Fq)))
  obtain ⟨hpkC, huC, hmain⟩ := hplain V 5
    (fun con hcon => hsat con (mem_compile_of_mem_body hcon))
  -- the reading is the input cells' values, projectionwise
  have hin : readVal (val := Statement.Raw Fq) V (inputVar (F := Fq) (a := Statement.Raw Fq))
      = (⟨⟨⟨(inputVar (F := Fq) (a := Statement.Raw Fq)).pk.point.x.val V,
            (inputVar (F := Fq) (a := Statement.Raw Fq)).pk.point.y.val V⟩⟩,
         ⟨⟨(inputVar (F := Fq) (a := Statement.Raw Fq)).u.point.x.val V,
            (inputVar (F := Fq) (a := Statement.Raw Fq)).u.point.y.val V⟩⟩,
         ⟨(inputVar (F := Fq) (a := Statement.Raw Fq)).z.val.val V⟩⟩ : Statement.Raw Fq) := by
    simp only [circuitVal]
  rw [hin] at hband ⊢
  obtain ⟨hnz, himp⟩ :=
    hmain _ _ _ (SWPoint.mk_ne_zero hpkC) (SWPoint.mk_ne_zero huC) hin
  exact (verifyRaw_iff _).mpr ⟨hpkC, huC, hnz, himp hband⟩

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
        (⟨⟨⟨pkx, pky⟩⟩, ⟨⟨uxv, uyv⟩⟩, zv⟩ : Statement.Raw Fq))
      (fun _ _ _ => True) Q⦄
    (CheckedType.check (F := Fq) (c := KimchiProverC Fq) stv)
    ⦃Q⦄ := by
  intro st hpre
  obtain ⟨hrd, hk⟩ := hpre
  simp only [reads_ofEquiv_iff, reads_prod_iff, reads_fvar_iff, circuitVal] at hrd
  obtain ⟨⟨hpkx, hpky⟩, ⟨hux, huy⟩, -⟩ := hrd
  have hprog : CheckedType.check (F := Fq) (c := KimchiProverC Fq) stv
      = (do CurvePoint.check (c := KimchiProverC Fq) stv.pk
            CurvePoint.check (c := KimchiProverC Fq) stv.u
            pure PUnit.unit) := rfl
  simp only [hprog, WPMonad.wp_bind, PredTrans.apply_Bind_bind]
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
  simp only [wp, PredTrans.apply, prove]
  intro hf
  exact hk PUnit.unit ⟨st₂.nv, st₂.env, hf⟩ trivial (hle₁.trans hle₂)

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
          (⟨⟨⟨stP.pk.x, stP.pk.y⟩⟩, ⟨⟨stP.u.x, stP.u.y⟩⟩, zt⟩ : Statement.Raw Fq)
        = .ok (PUnit.unit, env) ∧
      Reads env (inputVar (F := Fq) (a := Statement.Raw Fq))
        (⟨⟨⟨stP.pk.x, stP.pk.y⟩⟩, ⟨⟨stP.u.x, stP.u.y⟩⟩, zt⟩ : Statement.Raw Fq) := by
  obtain ⟨env₀, hseed, hlook, hfresh⟩ := solve_seed (F := Fq)
    (a := Statement.Raw Fq)
    (⟨⟨⟨stP.pk.x, stP.pk.y⟩⟩, ⟨⟨stP.u.x, stP.u.y⟩⟩, zt⟩ : Statement.Raw Fq)
  have h0 : env₀ 0 = some stP.pk.x := hlook 0 (by decide)
  have h1 : env₀ 1 = some stP.pk.y := hlook 1 (by decide)
  have h2 : env₀ 2 = some stP.u.x := hlook 2 (by decide)
  have h3 : env₀ 3 = some stP.u.y := hlook 3 (by decide)
  have h4 : env₀ 4 = some zt.val := hlook 4 (by decide)
  have hreads : Reads env₀ (inputVar (F := Fq) (a := Statement.Raw Fq))
      (⟨⟨⟨stP.pk.x, stP.pk.y⟩⟩, ⟨⟨stP.u.x, stP.u.y⟩⟩, zt⟩ : Statement.Raw Fq) := by
    simp only [reads_ofEquiv_iff, reads_prod_iff, reads_fvar_iff, circuitVal]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
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
/-- **The constructive boundary.** On a raw statement the wire verifier accepts — its
response decode off the ladder's forbidden band — the whole-circuit `solve` at the
kimchi checker succeeds and the returned table reads it at the input bundle: the
guard's on-curve facts are what the input check's honest run needs, its nonzero
response what the exclusion row needs. -/
theorem complete (raw : Statement.Raw Fq)
    (hband : raw.z.fromShiftedZ ∉ forbiddenValues PALLAS_BASE_CARD)
    (hacc : verifyRaw raw = true) :
    ∃ env : Assignments Fq,
      solve (b := PUnit) (Checker.holds (F := Fq) (c := KimchiConstraint Fq))
          (verifyCircuit (c := KimchiConstraint Fq)) raw = .ok (PUnit.unit, env) ∧
      Reads env (inputVar (F := Fq) (a := Statement.Raw Fq)) raw := by
  obtain ⟨hpk, hu, hz, hv⟩ := (verifyRaw_iff raw).mp hacc
  exact verifyCircuit_solve_complete
    ⟨⟨_, _, Or.inl hpk⟩, ⟨_, _, Or.inl hu⟩, raw.z.fromShifted⟩ raw.z
    (SWPoint.mk_ne_zero hpk) (SWPoint.mk_ne_zero hu) hz (vesta_ladderRegime raw.z hband)
    rfl hv

end Schnorr
