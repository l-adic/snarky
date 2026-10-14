import Pickles.Application.MatrixRun

/-!
# Application correctness stated over supplied keys

`KimchiFailure` names acceptance under a corresponding key when no satisfying index witness
exists at the accepted public input. Bounding the probability of producing this event is a
separate cryptographic claim; no perfect-soundness hypothesis is assumed here.

`ApplicationCertified.step_valuation_or_failure` and
`ApplicationCertified.wrap_valuation_or_failure` give either a valuation satisfying the
canonical circuit constraints and reading the accepted public statement, or `KimchiFailure`.
The certificate relates the supplied keys to the checked Lean indices, and compiler lifting
handles the satisfying-witness case. No imported index or witness is an argument of either
theorem.
-/

namespace Pickles

open Snarky Bulletproof Kimchi.Verifier CompElliptic.Fields.Pasta

namespace Application

/-- Some accepted proof fails Kimchi soundness at this fixed SRS. Application-level composition
can hide which index, key, proof and public input failed; the general results retain them. -/
def SomeKimchiFailure {curve : Ipa.KimchiCurve} (σ : SRS curve.Point) : Prop :=
  ∃ (n nc : Nat) (idx : Kimchi.Index curve.ScalarField n) (key : KimchiVK curve nc)
    (p : KimchiProof curve nc σ.k) (pub : Vector curve.ScalarField idx.publicCount),
    KimchiFailure σ idx key p pub

variable {D : Shape}

/-- Acceptance under a certified Step key supplies a valuation satisfying the branch's
canonical constraints and reading its accepted public statement, or witnesses Kimchi failure. -/
theorem ApplicationCertified.step_valuation_or_failure {C : Circuits D}
    (cert : ApplicationCertified C) (b : D.Branch)
    (p : KimchiProof IpaVesta.curve C.wiring.backend.stepChunks StepIPARounds)
    (pub : StepPublic D)
    (haccept : kimchiVerify IpaVesta.curve C.setup.stepSrs C.wiring.backend.stepKeys[b]
      p (CircuitType.valueToFields pub).toArray = true) :
    (∃ V : Valuation Fp,
      (∀ con ∈ (stepCompilation C b).constraints, ConstraintHolds.Holds V con) ∧
      CircuitType.Reads V (stepCompilation C b).result.1.2.out pub) ∨
      KimchiFailure C.setup.stepSrs (cert.step b).index C.wiring.backend.stepKeys[b] p
        ((CircuitType.valueToFields pub).cast (cert.indices.stepPublicCount b).symm) := by
  obtain ⟨table, holds⟩ | failure := satisfiesVec_or_failure (cert.stepKey b) p
    (CircuitType.valueToFields pub) (cert.indices.stepPublicCount b) haccept
  · obtain ⟨r, hreads, -⟩ := cert.lift_step b ⟨pub, table, holds⟩
    refine Or.inl ⟨r.V, ?_, ?_⟩
    · simpa only [C.stepBuilt_eq b r.advice] using r.holds
    · simpa only [StepRun.cells_eq] using hreads
  · exact Or.inr failure

/-- Acceptance under a certified Wrap key supplies a valuation satisfying the canonical
Wrap constraints and reading its accepted public statement, or witnesses Kimchi failure. -/
theorem ApplicationCertified.wrap_valuation_or_failure {C : Circuits D}
    (cert : ApplicationCertified C)
    (p : KimchiProof IpaPallas.curve 1 WrapIPARounds) (pub : WrapPublic)
    (haccept : kimchiVerify IpaPallas.curve C.setup.wrapSrs C.wiring.backend.wrapKey
      p (CircuitType.valueToFields pub).toArray = true) :
    (∃ V : Valuation Fq,
      (∀ con ∈ (wrapCompilation C).constraints, ConstraintHolds.Holds V con) ∧
      CircuitType.Reads V wrapStatement pub) ∨
      KimchiFailure C.setup.wrapSrs cert.wrap.index C.wiring.backend.wrapKey p
        ((CircuitType.valueToFields pub).cast cert.indices.wrapPublicCount.symm) := by
  obtain ⟨table, holds⟩ | failure := satisfiesVec_or_failure cert.wrapKey p
    (CircuitType.valueToFields pub) cert.indices.wrapPublicCount haccept
  · obtain ⟨r, hreads, -⟩ := cert.lift_wrap ⟨pub, table, holds⟩
    refine Or.inl ⟨r.V, ?_, hreads⟩
    simpa only [C.wrapBuilt_eq r.advice] using r.holds
  · exact Or.inr failure

end Application

end Pickles
