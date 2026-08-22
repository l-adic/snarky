import Schnorr.Laws
import Snarky.Kimchi.Backend.Compile

/-!
# The CS-satisfaction boundary — the fragment seam

The endpoint laws packaged through the whole-circuit pipeline
(`formal/docs/circuit-verifier-faithfulness.md`, layer 3): the statement is the
public input through its `CircuitType` encoding, and its `CheckedType` pays the two
on-curve checks at the seam.

- `verifyCircuit_compile_sound` — a valuation satisfying `compile verifyCircuit`'s
  constraints reads, at `inputVar`, a statement `verify` accepts (off the ladder's
  forbidden band). What `verify`'s guard demands — both points on-curve, the response
  decode nonzero — is forced by the input check's rows, not hypothesized.
- `complete` — on a statement `verify` accepts, `solve` at the kimchi checker succeeds
  (the guard supplies what the input check's honest run needs) and its table reads it.
-/

namespace Schnorr

open Snarky Snarky.Kimchi CompElliptic.Fields.Pasta
open Std.Do

open Kimchi.Gate.VarBaseMul (forbiddenValues) in
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass in
/-- The seam program — the statement's check, then the verifier — under one Sound
triple: the check's rows force both point readings on-curve, which is what the body's
certificate needs to land at `verify`. -/
private theorem checkedBody_spec (V : Valuation Fq) (stv : Statement (FVar Fq)) :
    ⦃⌜True⌝⦄
    (do CheckedType.check (c := Builder V (KimchiConstraint Fq)) stv
        verifyCircuit (c := Builder V (KimchiConstraint Fq)) stv)
    ⦃⇓ _ _ => ⌜(readVal (val := Statement Fq) V stv).z.fromShiftedZ
          ∉ forbiddenValues PALLAS_BASE_CARD →
        verify (readVal (val := Statement Fq) V stv) = true⌝⦄ := by
  mvcgen
  rename_i _ _ hchk _ _
  intro hmain hband
  -- the reading is the cells, projectionwise
  have hin : readVal (val := Statement Fq) V stv
      = (⟨⟨⟨stv.pk.point.x.val V, stv.pk.point.y.val V⟩⟩,
          ⟨⟨stv.u.point.x.val V, stv.u.point.y.val V⟩⟩,
          ⟨stv.z.val.val V⟩⟩ : Statement Fq) := by
    simp only [circuitVal]
  rw [hin] at hband ⊢
  exact (hmain _ hin hchk.1 hchk.2.1).2 hband

open Kimchi.Gate.VarBaseMul (forbiddenValues) in
/-- **The satisfaction boundary.** A valuation satisfying every compiled constraint
(each the verified gate's own predicate at the payload's operands) reads, at the input
bundle, a statement the wire verifier accepts — off the ladder's forbidden band. What
`verify`'s guard demands is exactly what the input check's rows force: both points
on-curve, the response decode nonzero. No curve-membership hypothesis survives. -/
theorem verifyCircuit_compile_sound (V : Valuation Fq)
    (hsat : ∀ con ∈ (compile (a := Statement Fq) (b := PUnit)
        (verifyCircuit (c := KimchiConstraint Fq))).constraints,
      ConstraintHolds.Holds V con)
    (hband : (readVal (val := Statement Fq) V
        (inputVar (F := Fq) (a := Statement Fq))).z.fromShiftedZ
      ∉ forbiddenValues PALLAS_BASE_CARD) :
    verify (readVal (val := Statement Fq) V (inputVar (F := Fq) (a := Statement Fq))) = true :=
  (builder_spec_iff _ _).mp (checkedBody_spec V (inputVar (F := Fq) (a := Statement Fq))) 5
    (fun con hcon => hsat con (mem_compile_of_mem_body hcon)) hband

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass in
/-- The statement check's honest prover run: it succeeds on any table reading the
statement as on-curve coordinate pairs — the two `CurvePoint` completeness laws in
sequence. Generic in the statement bundle so consumers instantiate without deep
unfolding. -/
private theorem check_complete (stv : Statement (FVar Fq)) (raw : Statement Fq)
    (hpkOC : OnCurve Vesta.curve.A Vesta.curve.B (raw.pk.point.x, raw.pk.point.y))
    (huOC : OnCurve Vesta.curve.A Vesta.curve.B (raw.u.point.x, raw.u.point.y))
    (Q : PostCond PUnit (.arg (ProverState Fq) (.except EvalError .pure))) :
    ⦃Complete (fun env => Reads env stv raw) (fun _ _ _ => True) Q⦄
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

open Kimchi.Gate.VarBaseMul (forbiddenValues) in
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass in
/-- **The constructive boundary.** On a statement the wire verifier accepts — its
response decode off the ladder's forbidden band — the whole-circuit `solve` at the
kimchi checker succeeds and the returned table reads it at the input bundle: the
guard's on-curve facts are what the input check's honest run needs
(`CurvePoint.check_complete_spec`), its nonzero response what the exclusion row needs. -/
theorem complete (raw : Statement Fq)
    (hband : raw.z.fromShiftedZ ∉ forbiddenValues PALLAS_BASE_CARD)
    (hacc : verify raw = true) :
    ∃ env : Assignments Fq,
      solve (b := PUnit) (Checker.holds (F := Fq) (c := KimchiConstraint Fq))
          (verifyCircuit (c := KimchiConstraint Fq)) raw = .ok (PUnit.unit, env) ∧
      Reads env (inputVar (F := Fq) (a := Statement Fq)) raw := by
  obtain ⟨hpkC, huC, -, -⟩ := (verify_iff raw).mp hacc
  obtain ⟨env₀, hseed, hlook, hfresh⟩ := solve_seed (F := Fq) (a := Statement Fq) raw
  have h0 : env₀ 0 = some raw.pk.point.x := hlook 0 (by decide)
  have h1 : env₀ 1 = some raw.pk.point.y := hlook 1 (by decide)
  have h2 : env₀ 2 = some raw.u.point.x := hlook 2 (by decide)
  have h3 : env₀ 3 = some raw.u.point.y := hlook 3 (by decide)
  have h4 : env₀ 4 = some raw.z.val := hlook 4 (by decide)
  have hreads : Reads env₀ (inputVar (F := Fq) (a := Statement Fq)) raw := by
    simp only [reads_ofEquiv_iff, reads_prod_iff, reads_fvar_iff, circuitVal]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · show (CVar.var 0).eval env₀ = .ok raw.pk.point.x
      simp [CVar.eval, h0]
    · show (CVar.var 1).eval env₀ = .ok raw.pk.point.y
      simp [CVar.eval, h1]
    · show (CVar.var 2).eval env₀ = .ok raw.u.point.x
      simp [CVar.eval, h2]
    · show (CVar.var 3).eval env₀ = .ok raw.u.point.y
      simp [CVar.eval, h3]
    · show (CVar.var 4).eval env₀ = .ok raw.z.val
      simp [CVar.eval, h4]
  -- the input check's honest run: both wire points are on-curve
  obtain ⟨q, hq, -, hleC⟩ := (complete_spec_iff
      (CheckedType.check (F := Fq) (c := KimchiProverC Fq)
        (inputVar (F := Fq) (a := Statement Fq))) _ _).mp
    (check_complete (inputVar (F := Fq) (a := Statement Fq)) raw hpkC huC)
    ⟨5, env₀, hfresh⟩ hreads
  have hfresh₁ : q.assignments.FreshFrom q.nextVar := prove_freshFrom hfresh hq
  obtain ⟨out, hrun, hle⟩ := verifyCircuit_complete_spec
    (inputVar (F := Fq) (a := Statement Fq)) raw (vesta_ladderRegime raw.z hband) hacc
    ⟨q.nextVar, q.assignments, hfresh₁⟩ (Reads.le hleC hreads)
  exact ⟨out.assignments, solve_punit_ok hseed hq hrun,
    Reads.le (hleC.trans hle) hreads⟩

end Schnorr
