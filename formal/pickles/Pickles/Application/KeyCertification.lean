import Pickles.Application.Imported
import Pickles.KeyDerivation

/-!
# Application keys certified against their indices

Check every branch's step key and the shared wrap key against their indices and shared SRSs.
The correspondence includes every polynomial commitment, the domain metadata and the shape's
accumulator counts. Imported producers need their own certificate. The manifest driver checks
producers before certifying their dependents.

`KeyedCertificate` retains both matrix lifting and key correspondence for the same indices.
`certifyKeys?` adds the latter to a certificate of index equality, with failures located at a
branch or the wrap circuit. No cached proof or witness is consumed.
-/

namespace Pickles.Application

open Bulletproof CompElliptic.Fields.Pasta

variable {D : Shape} {L : Layout D}

/-- Each application key commits to the corresponding certified index under the shared SRS. -/
structure ApplicationKeys (C : Circuits D L) (I : ApplicationIndices D) : Prop where
  /-- Every branch's step key, at its declared predecessor count. -/
  step : ∀ b, KeyCorresponds C.setup.stepSrs.σ (I.step b)
    C.wiring.backend.stepKeys[b] (D.slots b)
  /-- The shared wrap key, at the fixed padded accumulator count. -/
  wrap : KeyCorresponds C.setup.wrapSrs.σ I.wrap
    C.wiring.backend.wrapKey MaxProofsVerified

/-- The circuit whose key disagrees with its index. -/
inductive ApplicationKeyFailure (D : Shape) where
  /-- A branch's step key disagrees. -/
  | step (b : D.Branch) (failure : KeyFailure)
  /-- The shared wrap key disagrees. -/
  | wrap (failure : KeyFailure)

/-- An index certificate with the supplied keys' polynomial correspondence retained. -/
structure KeyedCertificate (C : Circuits D L) where
  /-- The certified imported indices, with their universal matrix lifting theorem. -/
  certified : CertifiedIndices C
  /-- The supplied keys commit to those same indices. -/
  keys : ApplicationKeys C certified.indices

/-- Derive all application key commitments and retain their correspondence to the indices. -/
def certifyKeys? {C : Circuits D L} (certified : CertifiedIndices C) :
    Except (ApplicationKeyFailure D) (KeyedCertificate C) := do
  let steps ← finSequence fun b =>
    (checkKey? pastaShapeVesta C.setup.stepSrs.σ (certified.indices.step b)
      C.wiring.backend.stepKeys[b] (D.slots b)).mapError (.step b)
  let wrap ← (checkKey? pastaShapePallas C.setup.wrapSrs.σ certified.indices.wrap
    C.wiring.backend.wrapKey MaxProofsVerified).mapError .wrap
  return ⟨certified, ⟨fun b => (steps b).down, wrap.down⟩⟩

/-- Key certification keeps the given index certificate. -/
theorem certifyKeys?_certified {C : Circuits D L} {certified : CertifiedIndices C}
    {result : KeyedCertificate C} (h : certifyKeys? certified = .ok result) :
    result.certified = certified := by
  simp only [certifyKeys?, bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      rfl

end Pickles.Application
