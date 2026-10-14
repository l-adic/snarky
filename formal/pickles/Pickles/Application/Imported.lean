import Pickles.Application.Certification
import Pickles.Application.Compare

/-!
# Correctness of compared foreign indices

Independent constraint-system comparison is separate from application certification.
`ApplicationCertified.picklesCorrect_of_compare` transports the checked Lean indices'
correctness to foreign indices when `compareIndices?` finds no difference. The existing
matrix verification and handover theorems then apply to those indices directly, without a
second certificate wrapper.
-/

namespace Pickles.Application

variable {D : Shape} {L : Layout D}

/-- A successful comparison transfers the certified Lean indices' lifting guarantees to the
foreign indices. This comparison is not a premise of application key certification. -/
theorem ApplicationCertified.picklesCorrect_of_compare {C : Circuits D L}
    (cert : ApplicationCertified C) (imported : ApplicationIndices D)
    (h : compareIndices? imported cert.indices = none) : PicklesCorrect C imported :=
  compareIndices?_eq_none_iff.mp h ▸ ApplicationCertified.picklesCorrect C cert

end Pickles.Application
