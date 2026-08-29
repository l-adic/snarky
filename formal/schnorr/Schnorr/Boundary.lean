import Schnorr.Laws
import Snarky.Compile

/-!
# The satisfaction boundary — the compile seam

The endpoint pair packaged through the whole-circuit pipeline. `Laws` states soundness and
completeness of `verifyCircuit` as a program: a weakest-precondition triple and a `Complete`
judgment. Here they are cashed at the compiled constraint system and the solver, which is
the form a deployed verifier and a deployed prover actually meet.

Both directions speak about the same two objects — `compile verifyCircuit`'s row list, and
the public input bundle `inputVar` at slots `0 … 4` — so they compose: the table
`verifyCircuit_solve_complete` produces satisfies exactly the hypothesis
`verifyCircuit_compile_sound` assumes.

The statement's on-curve facts are hypotheses of the sound direction and conclusions of the
wire verifier in the complete direction. They are not forced by `verifyCircuit`'s own rows —
they are the statement `CheckedType`'s contribution, paid at the seam by `compileBody`
before the body runs, which is why the sound direction takes them as given.

This is the boundary at the constraint layer. Dispatching those constraints to kimchi gate
rows (`kimchiCompile`, `kimchiGateData`) is a further layer and is not stated here.
-/

namespace Schnorr

open Snarky Snarky.Kimchi CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta
open CompElliptic.CurveForms.ShortWeierstrass
open Kimchi.Gate.VarBaseMul (forbiddenValues)

/-- **The sound boundary.** Any valuation that satisfies every row the compiled verifier
emits, and reads a statement at the public input bundle, certifies the wire verifier at that
statement: the response decodes nonzero, and outside the ladder's forbidden band `verify`
accepts. The two on-curve hypotheses are what the statement's own check contributes at the
seam — `verifyCircuit`'s rows do not force them. -/
theorem verifyCircuit_compile_sound (V : Valuation Fq) (raw : Statement Fq)
    (hsat : ∀ con ∈ (compile (a := Statement Fq) (b := PUnit)
        (verifyCircuit (c := KimchiConstraint Fq))).constraints,
      ConstraintHolds.Holds V con)
    (hin : CircuitType.Reads V (inputVar (F := Fq) (a := Statement Fq)) raw)
    (hpk : OnCurve Vesta.curve.A Vesta.curve.B (raw.pk.point.x, raw.pk.point.y))
    (hu : OnCurve Vesta.curve.A Vesta.curve.B (raw.u.point.x, raw.u.point.y)) :
    raw.z.toScalar ≠ (0 : Fp) ∧
      (raw.z.toScalarZ ∉ forbiddenValues PALLAS_BASE_CARD → verify raw = true) :=
  (builder_spec_iff (verifyCircuit (c := Builder V (KimchiConstraint Fq))
      (inputVar (F := Fq) (a := Statement Fq))) _).mp
    (verifyCircuit_spec (inputVar (F := Fq) (a := Statement Fq)))
    (bodyStart (F := Fq) (c := KimchiConstraint Fq) (a := Statement Fq)
      (avar := Statement (FVar Fq)))
    (fun con hcon => hsat con (mem_compile_of_mem_body hcon)) raw hin hpk hu

/-- **The constructive boundary.** On a statement the wire verifier accepts, outside the
ladder's forbidden band, the whole-circuit solve succeeds; the table it returns satisfies
every row the compiled verifier emits and still reads the statement at the public input
bundle. Acceptance is the only hypothesis on the statement: the on-curve facts the seam's
input check needs come out of `verify_iff`. -/
theorem verifyCircuit_solve_complete (raw : Statement Fq)
    (hv : verify raw = true)
    (hband : raw.z.toScalarZ ∉ forbiddenValues PALLAS_BASE_CARD) :
    ∃ env : Assignments Fq,
      solve (a := Statement Fq) (b := PUnit)
          (verifyCircuit (c := KimchiConstraint Fq)) raw = .ok (PUnit.unit, env) ∧
      (∀ con ∈ (compile (a := Statement Fq) (b := PUnit)
          (verifyCircuit (c := KimchiConstraint Fq))).constraints,
        ConstraintHolds.Holds env.get con) ∧
      CircuitType.Reads env.get (inputVar (F := Fq) (a := Statement Fq)) raw := by
  obtain ⟨hpk, hu, -, -⟩ := (verify_iff raw).mp hv
  -- the empty output bundle: nothing in scope, and the empty encoding is well formed
  have hpost : ∀ (out : PUnit) (st' : ProverState Fq), True →
      CircuitType.Scoped (val := PUnit) st' out ∧
        CircuitType.WellFormed (val := PUnit) st'.env.get out := by
    rintro ⟨⟩ st' _
    exact ⟨by simp [CircuitType.Scoped], ⟨PUnit.unit, rfl⟩⟩
  obtain ⟨out, env, hsolve, hsat, hin, -, -⟩ :=
    solve_complete (a := Statement Fq) (b := PUnit) (c := KimchiConstraint Fq)
      (main := fun stv => verifyCircuit (c := KimchiConstraint Fq) stv) raw
      (by simp [hpk, hu])
      (Complete.imp (fun _ h => h) hpost
        (verifyCircuit_complete (inputVar (F := Fq) (a := Statement Fq)) raw hv hband))
  exact ⟨env, by rwa [show out = PUnit.unit from rfl] at hsolve, hsat, hin⟩

end Schnorr
