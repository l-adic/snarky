import Kimchi.Index.Satisfies
import Kimchi.Columns

/-!
# Equality of indices, decided

Two indices are equal exactly when their stored data agree: every row's gate type,
coefficients and wire pointers, the public count, the masked-row count, the generator, the
endomorphism coefficient, the matrix and the shifts; the laws follow by proof irrelevance.
`compareIndex?` finds the first disagreement, located at its datum, and the success of
`checkIndexEq` is equality (`checkIndexEq_eq_true_iff`). Rows are walked by `List.finRange`,
as `build?` decides its laws, so evaluation is predictable and linear in the domain.

Equality transports satisfaction at a public vector unchanged, the two public-count
equalities taken apart (`SatisfiesVec_of_eq`). A family of indices on domains that may
differ is compared sizes first, then member by member (`compareFamily?`); its success is
equality of the sizes and heterogeneous equality of the members.

## Main definitions

- `IndexDiff`, `compareIndex?`, `checkIndexEq`: the first difference, located, and the
  decision.
- `FamilyDiff`, `compareFamily?`: a family's first difference and its decision.

## Main results

- `compareIndex?_eq_none_iff`, `checkIndexEq_eq_true_iff`: success is equality.
- `SatisfiesVec_of_eq`: equal indices accept the same tables at the same public vector.
- `compareFamily?_eq_none_iff`: success is equality of the sizes and of the members.
-/

namespace Kimchi.Index

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ}

/-- The first disagreement between two indices, located at its datum. -/
inductive IndexDiff where
  /-- The public counts differ. -/
  | publicCount
  /-- The masked-row counts differ. -/
  | zkRows
  /-- The generators differ. -/
  | omega
  /-- The endomorphism coefficients differ. -/
  | endoBase
  /-- The matrices differ. -/
  | mds
  /-- The shifts differ at the column. -/
  | shifts (c : Fin permCols)
  /-- The gate types differ at the row. -/
  | typ (i : ℕ)
  /-- The coefficients differ at the row and column. -/
  | coeff (i : ℕ) (c : Fin coeffCols)
  /-- The wire pointers differ at the row and column. -/
  | wire (i : ℕ) (c : Fin permCols)
  deriving DecidableEq

/-- Two rows' first disagreement: the gate type, then the coefficients, then the wires. -/
private def compareRow? (i : ℕ) (r s : GateRow F n) : Option IndexDiff :=
  if r.typ ≠ s.typ then some (.typ i)
  else
    match (List.finRange coeffCols).find? (fun c => decide (r.coeffs c ≠ s.coeffs c)) with
    | some c => some (.coeff i c)
    | none =>
      match (List.finRange permCols).find? (fun c => decide (r.wires c ≠ s.wires c)) with
      | some c => some (.wire i c)
      | none => none

/-- Two indices' first disagreement: the metadata, then the shifts, then the rows in order. -/
def compareIndex? (a b : Index F n) : Option IndexDiff :=
  if a.publicCount ≠ b.publicCount then some .publicCount
  else if a.zkRows ≠ b.zkRows then some .zkRows
  else if a.omega ≠ b.omega then some .omega
  else if a.endoBase ≠ b.endoBase then some .endoBase
  else if a.mds ≠ b.mds then some .mds
  else
    match (List.finRange permCols).find? (fun c => decide (a.shifts c ≠ b.shifts c)) with
    | some c => some (.shifts c)
    | none => (List.finRange n).findSome? fun i => compareRow? i.val (a.gates i) (b.gates i)

/-- Whether two indices agree on every datum. -/
def checkIndexEq (a b : Index F n) : Bool := (compareIndex? a b).isNone

omit [Field F] [DecidableEq F] in
/-- Rows agreeing on their data are equal. -/
private theorem GateRow.ext_of {r s : GateRow F n} (ht : r.typ = s.typ)
    (hc : ∀ c, r.coeffs c = s.coeffs c) (hw : ∀ c, r.wires c = s.wires c) : r = s := by
  obtain ⟨t, co, w⟩ := r
  obtain ⟨t', co', w'⟩ := s
  simp only at ht hc hw
  subst ht
  rw [funext hc, funext hw]

omit [DecidableEq F] in
/-- Indices agreeing on their data are equal: the laws are propositions. -/
private theorem ext_of_data {a b : Index F n} (hg : ∀ i, a.gates i = b.gates i)
    (hp : a.publicCount = b.publicCount) (hz : a.zkRows = b.zkRows) (ho : a.omega = b.omega)
    (he : a.endoBase = b.endoBase) (hm : a.mds = b.mds) (hs : ∀ c, a.shifts c = b.shifts c) :
    a = b := by
  cases a
  cases b
  simp only at hg hp hz ho he hm hs
  have hg' := funext hg
  have hs' := funext hs
  subst hg' hp hz ho he hm hs'
  rfl

omit [Field F] in
private theorem compareRow?_eq_none_iff {i : ℕ} {r s : GateRow F n} :
    compareRow? i r s = none ↔ r = s := by
  constructor
  · intro h
    unfold compareRow? at h
    split at h
    · cases h
    · rename_i ht
      split at h
      · cases h
      · rename_i hc
        split at h
        · cases h
        · rename_i hw
          refine GateRow.ext_of (not_not.mp ht) (fun c => ?_) (fun c => ?_)
          · simpa using List.find?_eq_none.mp hc c (List.mem_finRange c)
          · simpa using List.find?_eq_none.mp hw c (List.mem_finRange c)
  · rintro rfl
    have hc : (List.finRange coeffCols).find? (fun c => decide (r.coeffs c ≠ r.coeffs c)) =
        none := List.find?_eq_none.mpr (by simp)
    have hw : (List.finRange permCols).find? (fun c => decide (r.wires c ≠ r.wires c)) =
        none := List.find?_eq_none.mpr (by simp)
    unfold compareRow?
    rw [hc, hw]
    simp

/-- The comparison succeeds exactly on equal indices. -/
theorem compareIndex?_eq_none_iff {a b : Index F n} : compareIndex? a b = none ↔ a = b := by
  constructor
  · intro h
    unfold compareIndex? at h
    split at h
    · cases h
    rename_i hp
    split at h
    · cases h
    rename_i hz
    split at h
    · cases h
    rename_i ho
    split at h
    · cases h
    rename_i he
    split at h
    · cases h
    rename_i hm
    split at h
    · cases h
    rename_i hs
    refine ext_of_data (fun i => ?_) (not_not.mp hp) (not_not.mp hz) (not_not.mp ho)
      (not_not.mp he) (not_not.mp hm) (fun c => ?_)
    · exact compareRow?_eq_none_iff.mp
        (List.findSome?_eq_none_iff.mp h i (List.mem_finRange i))
    · simpa using List.find?_eq_none.mp hs c (List.mem_finRange c)
  · rintro rfl
    have hs : (List.finRange permCols).find? (fun c => decide (a.shifts c ≠ a.shifts c)) =
        none := List.find?_eq_none.mpr (by simp)
    unfold compareIndex?
    rw [hs]
    simp [List.findSome?_eq_none_iff, compareRow?_eq_none_iff]

/-- The decision succeeds exactly on equal indices. -/
theorem checkIndexEq_eq_true_iff {a b : Index F n} : checkIndexEq a b = true ↔ a = b := by
  rw [checkIndexEq, Option.isNone_iff_eq_none, compareIndex?_eq_none_iff]

omit [DecidableEq F] in
/-- Equal indices accept the same tables at the same public vector. -/
theorem SatisfiesVec_of_eq {a b : Index F n} (h : a = b) {m : ℕ} {pub : Vector F m}
    (ha : a.publicCount = m) (hb : b.publicCount = m) {table : Fin n → Fin wCols → F} :
    a.SatisfiesVec pub ha table ↔ b.SatisfiesVec pub hb table := by
  subst h
  rfl

/-! ## Families -/

/-- The first disagreement between two families of indices. -/
inductive FamilyDiff (ι : Type) where
  /-- The domain sizes differ at the member. -/
  | size (i : ι)
  /-- The members differ, at the datum. -/
  | member (i : ι) (d : IndexDiff)
  deriving DecidableEq

/-- Two families' first disagreement: the sizes in order, then the members in order, each
compared on the common domain. -/
def compareFamily? {k : ℕ} (sa sb : Fin k → ℕ) (a : (i : Fin k) → Index F (sa i))
    (b : (i : Fin k) → Index F (sb i)) : Option (FamilyDiff (Fin k)) :=
  match (List.finRange k).find? (fun i => decide (sa i ≠ sb i)) with
  | some i => some (.size i)
  | none => (List.finRange k).findSome? fun i =>
      if h : sa i = sb i then (compareIndex? (a i) (h ▸ b i)).map (.member i) else none

/-- The comparison succeeds exactly when the sizes agree and the members are equal. -/
theorem compareFamily?_eq_none_iff {k : ℕ} {sa sb : Fin k → ℕ} {a : (i : Fin k) → Index F (sa i)}
    {b : (i : Fin k) → Index F (sb i)} :
    compareFamily? sa sb a b = none ↔ sa = sb ∧ ∀ i, HEq (a i) (b i) := by
  constructor
  · intro h
    unfold compareFamily? at h
    split at h
    · cases h
    rename_i hs
    have hsize : sa = sb :=
      funext fun i => by simpa using List.find?_eq_none.mp hs i (List.mem_finRange i)
    subst hsize
    refine ⟨rfl, fun i => ?_⟩
    have := List.findSome?_eq_none_iff.mp h i (List.mem_finRange i)
    simp only [dite_true, Option.map_eq_none_iff] at this
    exact heq_of_eq (compareIndex?_eq_none_iff.mp this)
  · rintro ⟨rfl, hab⟩
    have hs : (List.finRange k).find? (fun i => decide (sa i ≠ sa i)) = none :=
      List.find?_eq_none.mpr (by simp)
    unfold compareFamily?
    rw [hs]
    simp only
    rw [List.findSome?_eq_none_iff]
    intro i _
    rw [dif_pos trivial, Option.map_eq_none_iff]
    exact compareIndex?_eq_none_iff.mpr (eq_of_heq (hab i))

end Kimchi.Index
