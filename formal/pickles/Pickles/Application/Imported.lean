import Pickles.Application.Certification
import Pickles.Application.Compare

/-!
# Imported indices certified

Native correctness transports along index equality: indices equal to Pickles-correct indices
are Pickles-correct (`importedApplication_picklesCorrect`). `certifyIndices?` applies it to
indices built from an independent source: against a checked application, the first
disagreement with the application's checked indices, or the indices certified, their
Pickles-correctness from the comparator's success turned into the equality the transport
takes. `CertifiedIndices.wrap_handover` and `CertifiedIndices.step_handover` apply the
original capstones to arbitrary connected imported matrices; the comparator stays inside.

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

variable {PD MD CD : Shape} {PL : Layout PD} {ML : Layout MD} {CL : Layout CD}

/-- The wrap-proof capstone for arbitrary connected matrices of certified imported indices. -/
theorem CertifiedIndices.wrap_handover {P : Circuits PD PL} {C : Circuits CD CL}
    (pc : CertifiedIndices P) (cc : CertifiedIndices C)
    (pb : PD.Branch) (cb : CD.Branch) (pi : PD.Slot pb) (ci : CD.Slot cb)
    (ps : StepTable pc.indices pb) (pw : WrapTable pc.indices)
    (cs : StepTable cc.indices cb) (cw : WrapTable cc.indices)
    (h : MatrixWrapHandover P C pc.indices cc.indices pb cb pi ci ps pw cs cw)
    (hp : StepWrapAssumptions P pb pi) (hc : StepWrapAssumptions C cb ci) :
    WrapHandoverConclusion P C pc.indices cc.indices pb cb pi ci ps pw cs cw :=
  matrices_wrap_handover pc.correct cc.correct pb cb pi ci ps pw cs cw h hp hc

/-- The step-proof capstone for arbitrary connected matrices of certified imported indices. -/
theorem CertifiedIndices.step_handover {P : Circuits PD PL} {M : Circuits MD ML}
    {C : Circuits CD CL}
    (pc : CertifiedIndices P) (mc : CertifiedIndices M) (cc : CertifiedIndices C)
    (pb : PD.Branch) (mb : MD.Branch) (cb : CD.Branch) (mi : MD.Slot mb) (ci : CD.Slot cb)
    (pw : WrapTable pc.indices) (ms : StepTable mc.indices mb)
    (mw : WrapTable mc.indices) (cs : StepTable cc.indices cb)
    (h : MatrixStepHandover P M C pc.indices mc.indices cc.indices pb mb cb mi ci pw ms mw cs)
    (hp : WrapStepAssumptions P pb) (hc : WrapStepAssumptions M mb) :
    StepHandoverConclusion P M C pc.indices mc.indices cc.indices pb mb cb mi ci pw ms mw cs h :=
  matrices_step_handover pc.correct mc.correct cc.correct pb mb cb mi ci pw ms mw cs h hp hc

end Pickles.Application
