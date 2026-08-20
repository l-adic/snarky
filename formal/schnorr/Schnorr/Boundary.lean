import Schnorr.Laws
import Snarky.Kimchi.Backend.Compile

/-!
# The CS-satisfaction boundary — the fragment seam

The endpoint laws packaged through the whole-circuit pipeline, the way the
verifier-faithfulness architecture's fragments are
(`formal/docs/circuit-verifier-faithfulness.md`, layer 3): the statement is the
circuit's public input through its `CircuitType` encoding, and the boundary speaks
about compiled constraint systems and solver runs, not triples.

- `verifyCircuit_compile_sound` — any valuation satisfying every constraint
  `compile verifyCircuit` emits, with the statement's encoding at the input slots,
  certifies the relaxed wire verifier (the sound endpoint, cashed out of the
  weakest-precondition reading by `sound_spec_iff`).
- `verifyCircuit_solve_complete` — on a statement the wire verifier accepts,
  honestly encoded, the whole-circuit `solve` at the kimchi checker succeeds and
  its table reads the statement at the input bundle (the complete endpoint through
  `complete_spec_iff`, wrapped by `solve_seed`/`solve_punit_ok`).
-/

namespace Schnorr

open Snarky Snarky.Kimchi CompElliptic.Fields.Pasta
open Std.Do

open Kimchi.Gate.VarBaseMul (forbiddenValues) in
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass in
/-- **The satisfaction boundary.** Any valuation that satisfies every constraint the
compiled verifier emits, and holds a statement's encoding at the five public-input
slots, certifies `verifyRelaxed` at that statement — with the response recovered up
to its reconstruction class, as the sound endpoint states. The constraint reading is
the kimchi semantic one: each emitted constraint is the verified gate's own
predicate at the payload's operand values. -/
theorem verifyCircuit_compile_sound
    (pkP uP : SWPoint Vesta.curve) (zv : Fq) (hpk0 : pkP ≠ 0) (hu0 : uP ≠ 0)
    (V : Valuation Fq)
    (hsat : ∀ con ∈ (compile (a := Statement.Raw Fq) (b := PUnit)
        (verifyCircuit (c := KimchiConstraint Fq))).constraints,
      ConstraintHolds.Holds V con)
    (hin : readVal V (inputVar (F := Fq) (a := Statement.Raw Fq))
      = (⟨⟨pkP.x, pkP.y⟩, ⟨uP.x, uP.y⟩, zv⟩ : Statement.Raw Fq)) :
    ∃ s : ℤ, 2 ^ 255 < s ∧ s < 3 * 2 ^ 255 ∧
      (s : Fq) = Type1.fromShifted 255 ⟨zv⟩ ∧
      (s ∉ forbiddenValues PALLAS_BASE_CARD →
        verifyRelaxed ⟨pkP, uP, (s : Fp)⟩) := by
  have hlist : (compile (a := Statement.Raw Fq) (b := PUnit)
      (verifyCircuit (c := KimchiConstraint Fq))).constraints
      = (build (verifyCircuit (c := KimchiConstraint Fq)
          (inputVar (F := Fq) (a := Statement.Raw Fq))) 5).constraints := by
    rw [compile_punit_constraints]
    rfl
  have hplain := (sound_spec_iff (verifyCircuit (c := KimchiConstraint Fq)
      (inputVar (F := Fq) (a := Statement.Raw Fq))) _).mp
    (verifyCircuit_spec (inputVar (F := Fq) (a := Statement.Raw Fq)))
  exact hplain V 5 (fun con hcon => hsat con (by rw [hlist]; exact hcon))
    pkP uP zv hpk0 hu0 hin

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass in
/-- **The constructive boundary.** On a statement the wire verifier accepts —
honestly encoded, nondegenerate, in the ladder regime — the whole-circuit `solve` at
the kimchi checker succeeds, and the returned table reads the statement at the
public-input bundle. The run is the complete endpoint's, entered through the seeded
input slots; the wrapper contributes nothing at output `PUnit`. -/
theorem verifyCircuit_solve_complete
    (stP : Statement) (zv : Fq)
    (hpk0 : stP.pk ≠ 0) (hu0 : stP.u ≠ 0) (hz0 : stP.z ≠ 0)
    (hfit : ToNat.toNat zv < 2 ^ 255)
    (hfaith : ((ToNat.toNat zv : ℕ) : Fq) = zv)
    (hreg : HasCurve.vesta.LadderRegime 255
      (Type1.fromShifted 255 ⟨(ToNat.toNat zv : ℤ)⟩))
    (henc : ((Type1.fromShifted 255 ⟨(ToNat.toNat zv : ℤ)⟩ : ℤ) : Fp) = stP.z)
    (hacc : verify stP = true) :
    ∃ env : Assignments Fq,
      solve (b := PUnit) (Checker.holds (F := Fq) (c := KimchiConstraint Fq))
          (verifyCircuit (c := KimchiConstraint Fq))
          (⟨⟨stP.pk.x, stP.pk.y⟩, ⟨stP.u.x, stP.u.y⟩, zv⟩ : Statement.Raw Fq)
        = .ok (PUnit.unit, env) ∧
      Reads env (inputVar (F := Fq) (a := Statement.Raw Fq))
        (⟨⟨stP.pk.x, stP.pk.y⟩, ⟨stP.u.x, stP.u.y⟩, zv⟩ : Statement.Raw Fq) := by
  obtain ⟨env₀, hseed, hlook, hfresh⟩ := solve_seed (F := Fq)
    (a := Statement.Raw Fq)
    (⟨⟨stP.pk.x, stP.pk.y⟩, ⟨stP.u.x, stP.u.y⟩, zv⟩ : Statement.Raw Fq)
  have h0 : env₀ 0 = some stP.pk.x := hlook 0 (by decide)
  have h1 : env₀ 1 = some stP.pk.y := hlook 1 (by decide)
  have h2 : env₀ 2 = some stP.u.x := hlook 2 (by decide)
  have h3 : env₀ 3 = some stP.u.y := hlook 3 (by decide)
  have h4 : env₀ 4 = some zv := hlook 4 (by decide)
  have hreads : Reads env₀ (inputVar (F := Fq) (a := Statement.Raw Fq))
      (⟨⟨stP.pk.x, stP.pk.y⟩, ⟨stP.u.x, stP.u.y⟩, zv⟩ : Statement.Raw Fq) := by
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
    · show (CVar.var 4).eval env₀ = .ok zv
      simp [CVar.eval, h4]
  have hcheck : prove (Checker.holds (F := Fq) (c := KimchiConstraint Fq))
      (CheckedType.check (c := KimchiConstraint Fq)
        (inputVar (F := Fq) (a := Statement.Raw Fq))) 5 env₀
      = .ok ⟨PUnit.unit, 5, env₀⟩ := rfl
  obtain ⟨out, hrun, hle⟩ := verifyCircuit_complete_spec
    (inputVar (F := Fq) (a := Statement.Raw Fq)) stP zv
    hpk0 hu0 hz0 hfit hfaith hreg henc hacc ⟨5, env₀, hfresh⟩ hreads
  exact ⟨out.assignments, solve_punit_ok hseed hcheck hrun, Reads.le hle hreads⟩

end Schnorr
