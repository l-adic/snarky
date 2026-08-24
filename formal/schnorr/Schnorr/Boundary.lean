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
  (the guard supplies what the input check's honest run needs) and its table has the
  input bundle in scope, reading it.
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
/-- The statement check's honest run: on a table reading both points on-curve, the two
`CurvePoint` checks in sequence land at their runs. Generic in the statement bundle so
consumers instantiate without deep unfolding. -/
private theorem check_run (stv : Statement (FVar Fq)) (st : ProverState Fq)
    (hsc : CircuitType.Scoped (Statement Fq) st stv)
    (hpkOC : OnCurve Vesta.curve.A Vesta.curve.B
      (stv.pk.point.x.val st.env.toValuation, stv.pk.point.y.val st.env.toValuation))
    (huOC : OnCurve Vesta.curve.A Vesta.curve.B
      (stv.u.point.x.val st.env.toValuation, stv.u.point.y.val st.env.toValuation)) :
    prove (Checker.holds (F := Fq) (c := KimchiConstraint Fq))
        (CheckedType.check (c := KimchiConstraint Fq) stv) st.nv st.env
      = .ok ((CurvePoint.checkRun (CurvePoint.checkRun st stv.pk) stv.u).out ()) := by
  simp only [scoped_ofEquiv_iff, scoped_prod_iff, scoped_fvar_iff, circuitVal] at hsc
  obtain ⟨⟨hpkx, hpky⟩, ⟨hux, huy⟩, -⟩ := hsc
  have hprog : CheckedType.check (F := Fq) (c := KimchiConstraint Fq) stv
      = (do CurvePoint.check (c := KimchiConstraint Fq) stv.pk
            CurvePoint.check (c := KimchiConstraint Fq) stv.u
            pure PUnit.unit) := rfl
  have hle₁ := CurvePoint.checkRun_le st hpkx
  rw [hprog, prove_bind, CurvePoint.check_run st hpkx hpky hpkOC]
  simp only [Except.bind]
  rw [prove_bind, CurvePoint.check_run _ (hux.of_le hle₁) (huy.of_le hle₁)
    (by rw [CVar.val_of_le hle₁ hux, CVar.val_of_le hle₁ huy]; exact huOC)]
  simp only [Except.bind, prove_pure]

open Kimchi.Gate.VarBaseMul (forbiddenValues) in
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass in
/-- **The constructive boundary.** On a statement the wire verifier accepts — its
response decode off the ladder's forbidden band — the whole-circuit `solve` at the
kimchi checker succeeds, and the returned table has the input bundle in scope, reading
it: the guard's on-curve facts are what the input check's honest run needs
(`CurvePoint.check_run`), its nonzero response what the exclusion row needs. -/
theorem complete (raw : Statement Fq)
    (hband : raw.z.fromShiftedZ ∉ forbiddenValues PALLAS_BASE_CARD)
    (hacc : verify raw = true) :
    ∃ st : ProverState Fq,
      solve (b := PUnit) (Checker.holds (F := Fq) (c := KimchiConstraint Fq))
          (verifyCircuit (c := KimchiConstraint Fq)) raw = .ok (PUnit.unit, st.env) ∧
      CircuitType.Scoped (Statement Fq) st (inputVar (F := Fq) (a := Statement Fq)) ∧
      readVal (val := Statement Fq) st.env.toValuation (inputVar (F := Fq) (a := Statement Fq))
        = raw := by
  obtain ⟨hpkC, huC, -, -⟩ := (verify_iff raw).mp hacc
  obtain ⟨env₀, hseed, hlook, hfresh⟩ := solve_seed (F := Fq) (a := Statement Fq) raw
  have h0 : env₀ 0 = some raw.pk.point.x := hlook 0 (by decide)
  have h1 : env₀ 1 = some raw.pk.point.y := hlook 1 (by decide)
  have h2 : env₀ 2 = some raw.u.point.x := hlook 2 (by decide)
  have h3 : env₀ 3 = some raw.u.point.y := hlook 3 (by decide)
  have h4 : env₀ 4 = some raw.z.val := hlook 4 (by decide)
  let st₀ : ProverState Fq := ⟨5, env₀, hfresh⟩
  have hval : ∀ (k : Variable) (x : Fq), env₀ k = some x →
      (CVar.var k).val st₀.env.toValuation = x := by
    intro k x hk
    simp [CVar.val, Assignments.toValuation, hk]
  -- the seeded table has the input bundle in scope, reading the statement
  have hsc : CircuitType.Scoped (Statement Fq) st₀ (inputVar (F := Fq) (a := Statement Fq)) := by
    simp only [scoped_ofEquiv_iff, scoped_prod_iff, scoped_fvar_iff, circuitVal]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · show (CVar.var 0).Scoped st₀
      exact ProverState.mem_of_assigned h0
    · show (CVar.var 1).Scoped st₀
      exact ProverState.mem_of_assigned h1
    · show (CVar.var 2).Scoped st₀
      exact ProverState.mem_of_assigned h2
    · show (CVar.var 3).Scoped st₀
      exact ProverState.mem_of_assigned h3
    · show (CVar.var 4).Scoped st₀
      exact ProverState.mem_of_assigned h4
  have hread : readVal (val := Statement Fq) st₀.env.toValuation
      (inputVar (F := Fq) (a := Statement Fq)) = raw := by
    simp only [circuitVal]
    show (⟨⟨⟨(CVar.var 0).val st₀.env.toValuation, (CVar.var 1).val st₀.env.toValuation⟩⟩,
        ⟨⟨(CVar.var 2).val st₀.env.toValuation, (CVar.var 3).val st₀.env.toValuation⟩⟩,
        ⟨(CVar.var 4).val st₀.env.toValuation⟩⟩ : Statement Fq) = raw
    rw [hval 0 _ h0, hval 1 _ h1, hval 2 _ h2, hval 3 _ h3, hval 4 _ h4]
  -- the input check's honest run: both wire points are on-curve
  have hpkOC : OnCurve Vesta.curve.A Vesta.curve.B
      ((inputVar (F := Fq) (a := Statement Fq)).pk.point.x.val st₀.env.toValuation,
        (inputVar (F := Fq) (a := Statement Fq)).pk.point.y.val st₀.env.toValuation) := by
    show OnCurve _ _ ((CVar.var 0).val st₀.env.toValuation, (CVar.var 1).val st₀.env.toValuation)
    rw [hval 0 _ h0, hval 1 _ h1]
    exact hpkC
  have huOC : OnCurve Vesta.curve.A Vesta.curve.B
      ((inputVar (F := Fq) (a := Statement Fq)).u.point.x.val st₀.env.toValuation,
        (inputVar (F := Fq) (a := Statement Fq)).u.point.y.val st₀.env.toValuation) := by
    show OnCurve _ _ ((CVar.var 2).val st₀.env.toValuation, (CVar.var 3).val st₀.env.toValuation)
    rw [hval 2 _ h2, hval 3 _ h3]
    exact huC
  have hcheck := check_run (inputVar (F := Fq) (a := Statement Fq)) st₀ hsc hpkOC huOC
  have hsc' := hsc
  simp only [scoped_ofEquiv_iff, scoped_prod_iff, scoped_fvar_iff, circuitVal] at hsc'
  obtain ⟨⟨hpkx₀, -⟩, ⟨hux₀, -⟩, -⟩ := hsc'
  have hle₁ := CurvePoint.checkRun_le st₀ hpkx₀
  have hle₀₂ : st₀.env.Le (CurvePoint.checkRun (CurvePoint.checkRun st₀
      (inputVar (F := Fq) (a := Statement Fq)).pk) (inputVar (F := Fq) (a := Statement Fq)).u).env :=
    hle₁.trans (CurvePoint.checkRun_le _ (hux₀.of_le hle₁))
  -- the body's honest run at the checked table
  have hmain := verifyCircuit_run (inputVar (F := Fq) (a := Statement Fq)) raw
    (vesta_ladderRegime raw.z hband) hacc _ (hsc.of_le hle₀₂)
    (by rw [readVal_of_le hle₀₂ hsc]; exact hread)
  have hleV := verifyRun_le (inputVar (F := Fq) (a := Statement Fq)) raw
    (vesta_ladderRegime raw.z hband) hacc _ (hsc.of_le hle₀₂)
    (by rw [readVal_of_le hle₀₂ hsc]; exact hread)
  refine ⟨_, solve_punit_ok hseed hcheck hmain, hsc.of_le (hle₀₂.trans hleV), ?_⟩
  rw [readVal_of_le (hle₀₂.trans hleV) hsc]
  exact hread

end Schnorr
