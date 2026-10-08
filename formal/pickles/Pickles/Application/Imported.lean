import Pickles.Application.Certification
import Pickles.Application.Compare

/-!
# Imported indices certified

Native correctness transports along index equality: indices equal to Pickles-correct indices
are Pickles-correct (`importedApplication_picklesCorrect`). `certifyIndices?` applies it to
indices built from an independent source: against a checked application, the first
disagreement with the application's checked indices, or the indices certified, their
Pickles-correctness from the comparator's success turned into the equality the transport
takes. A consumer reads `CertifiedIndices.correct`; the comparator's verdict stays inside.

## Main definitions

- `CertifiedIndices`: an application's certified indices, with their Pickles-correctness.
- `certifyIndices?`: the indices certified, or the first disagreement with the checked
  indices.

## Main results

- `importedApplication_picklesCorrect`: native correctness transports along index equality.
- `certifyIndices?_indices`: the certified indices are the given ones.
- `certifyIndices?_isOk_iff`: certification succeeds exactly on the checked indices.
-/

namespace Pickles.Application

variable {D : Shape} {L : Layout D}

/-- **Transport along index equality.** Indices equal to Pickles-correct indices are
Pickles-correct. -/
theorem importedApplication_picklesCorrect (C : Circuits D L)
    (native imported : ApplicationIndices D) (hNative : PicklesCorrect C native)
    (hMatch : imported = native) : PicklesCorrect C imported :=
  hMatch ▸ hNative

/-- An application's certified indices: indices with their Pickles-correctness. Obtained from
`certifyIndices?`, which compares given indices with the application's checked indices. -/
structure CertifiedIndices (C : Circuits D L) where
  /-- The indices. -/
  indices : ApplicationIndices D
  /-- The indices are Pickles-correct. -/
  correct : PicklesCorrect C indices

/-- Indices against a checked application: the first disagreement with its checked indices,
or the indices certified, the comparator's success as the equality the transport takes. -/
def certifyIndices? {C : Circuits D L} (checked : CheckedApplication C)
    (imported : ApplicationIndices D) : Except (IndicesDiff D) (CertifiedIndices C) :=
  match h : compareIndices? imported checked.indices with
  | some d => .error d
  | none => .ok ⟨imported, importedApplication_picklesCorrect C _ imported
      (checkedApplication_picklesCorrect C checked) (compareIndices?_eq_none_iff.mp h)⟩

/-- The certified indices are the given ones. -/
theorem certifyIndices?_indices {C : Circuits D L} {checked : CheckedApplication C}
    {imported : ApplicationIndices D} {cert : CertifiedIndices C}
    (h : certifyIndices? checked imported = .ok cert) : cert.indices = imported := by
  unfold certifyIndices? at h
  split at h
  · cases h
  · cases h
    rfl

/-- Certification succeeds exactly on the checked indices. -/
theorem certifyIndices?_isOk_iff {C : Circuits D L} {checked : CheckedApplication C}
    {imported : ApplicationIndices D} :
    (certifyIndices? checked imported).isOk = true ↔ imported = checked.indices := by
  unfold certifyIndices?
  split
  · rename_i d h
    refine iff_of_false (by simp [Except.isOk, Except.toBool]) fun e => ?_
    rw [compareIndices?_eq_none_iff.mpr e] at h
    cases h
  · rename_i h
    exact iff_of_true (by simp [Except.isOk, Except.toBool]) (compareIndices?_eq_none_iff.mp h)

end Pickles.Application
