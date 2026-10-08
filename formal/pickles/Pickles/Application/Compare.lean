import Pickles.Application.CheckedCompile
import Kimchi.Index.Compare

/-!
# Equality of an application's indices, decided

Two families of an application's indices are equal exactly when their branch domains agree
and every branch index and the wrap index agree (`compareIndices?_eq_none_iff`). The comparison
reports the first disagreement at its branch or at the wrap circuit, with the datum.
-/

namespace Pickles.Application

open Kimchi.Index

variable {D : Shape}

/-- The first disagreement between two families of an application's indices. -/
inductive IndicesDiff (D : Shape) where
  /-- The branch families differ. -/
  | step (d : FamilyDiff D.Branch)
  /-- The wrap domains differ. -/
  | wrapSize
  /-- The wrap indices differ, at the datum. -/
  | wrap (d : IndexDiff)

/-- Two families' first disagreement: the branches, then the wrap circuit. -/
def compareIndices? (a b : ApplicationIndices D) : Option (IndicesDiff D) :=
  match compareFamily? a.stepSize b.stepSize a.step b.step with
  | some d => some (.step d)
  | none =>
    if h : a.wrapSize = b.wrapSize then (compareIndex? a.wrap (h ▸ b.wrap)).map .wrap
    else some .wrapSize

/-- The comparison succeeds exactly on equal families. -/
theorem compareIndices?_eq_none_iff {a b : ApplicationIndices D} :
    compareIndices? a b = none ↔ a = b := by
  constructor
  · intro h
    obtain ⟨as, ast, aw, awr, ap, aq⟩ := a
    obtain ⟨bs, bst, bw, bwr, bp, bq⟩ := b
    unfold compareIndices? at h
    simp only at h
    split at h
    · cases h
    rename_i hsteps
    obtain ⟨hsize, hstep⟩ := compareFamily?_eq_none_iff.mp hsteps
    subst hsize
    have hst : ast = bst := funext fun i => eq_of_heq (hstep i)
    subst hst
    split at h
    · rename_i hw
      subst hw
      rw [Option.map_eq_none_iff] at h
      have hwr : awr = bwr := compareIndex?_eq_none_iff.mp h
      subst hwr
      rfl
    · cases h
  · rintro rfl
    have hfam : compareFamily? a.stepSize a.stepSize a.step a.step = none :=
      compareFamily?_eq_none_iff.mpr ⟨rfl, fun _ => HEq.rfl⟩
    unfold compareIndices?
    rw [hfam]
    simp [compareIndex?_eq_none_iff]

end Pickles.Application
