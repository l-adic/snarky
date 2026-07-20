import Kimchi.Index.Basic
import Kimchi.Quotient.Generic
import Kimchi.Quotient.Poseidon
import Kimchi.Quotient.AddComplete
import Kimchi.Quotient.VarBaseMul
import Kimchi.Quotient.EndoMul
import Kimchi.Quotient.EndoScalar

/-!
# Satisfiability: a witness table against an index

What it means for a `15 × n` witness table to satisfy a circuit: every row's gate
predicate holds (`rowSatisfies` — dispatch on the row's gate type, reusing each gate's
`Holds` through the quotient layer's `rowWitness` layout transcriptions and, for
Poseidon, the `rcMap` round-constant view of the coefficient row), the copy constraints
hold along the wiring (every permuted cell equals its wired-to cell — trivially true on
identity-wired cells, so quantified over the whole grid), and the public rows pin the
first witness column to the public input.

**There is no hand-written checker.** `Satisfies` is the definition; executability is a
derived `Decidable` instance — every gate's `Holds` is `∀ e ∈ constraints, e = 0`, so
each branch is decided by `List.decidableBAll`, and the conjunction over rows and cells
by the `Fintype` instances. `decide` is the checker, generated from the predicate
itself; fixture scripts evaluate it and nothing else.
-/

namespace Kimchi.Index

open Kimchi.Quotient

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ} [NeZero n]

/-- The public value at a row: the input for the public rows, zero beyond them. -/
def pubAt (idx : Index F n) (pub : Fin idx.publicCount → F) (i : Fin n) : F :=
  if h : (i : ℕ) < idx.publicCount then pub ⟨(i : ℕ), h⟩ else 0

/-- Row `i` satisfies its gate: dispatch on the stored gate type. `zero` rows constrain
nothing; `generic` reads its coefficients and current-row cells with the row's public
value folded in (`Generic.withPublic` — the layout knowledge lives with the gate); the
remaining gates go through their
quotient-layer `rowWitness` layout transcriptions (two-row where the gate spans two
rows); Poseidon's round constants are its coefficient row (`rcMap`); `endoMul` consumes
the index's `endoBase`. -/
def rowSatisfies (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin 15 → F) (i : Fin n) : Prop :=
  match (idx.gates i).typ with
  | .zero => True
  | .generic =>
      Gate.Generic.Holds (Gate.Generic.withPublic ⟨idx.coeffTable i, wTab i⟩
        (pubAt idx pub i))
  | .poseidon =>
      Gate.Poseidon.Holds (Poseidon.rcMap (idx.coeffTable i)) (Poseidon.rowWitness wTab i)
  | .completeAdd => Gate.AddComplete.Holds (AddComplete.rowWitness wTab i)
  | .varBaseMul => Gate.VarBaseMul.Holds (VarBaseMul.rowWitness wTab i)
  | .endoMul => Gate.EndoMul.Holds idx.endoBase (EndoMul.rowWitness wTab i)
  | .endoScalar => Gate.EndoScalar.Holds (EndoScalar.rowWitness wTab i)

/-- The value of a permuted cell: column `c.1` (of the seven) at row `c.2`. -/
def cellValue (wTab : Fin n → Fin 15 → F) (c : Fin 7 × Fin n) : F :=
  wTab c.2 (Fin.castLE (by omega) c.1)

/-- A witness table satisfies an index at a public input: every row's gate holds, every
permuted cell equals its wired-to cell, and the public rows pin the first column. -/
def Satisfies (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin 15 → F) : Prop :=
  (∀ i, rowSatisfies idx pub wTab i)
    ∧ (∀ c : Fin 7 × Fin n, cellValue wTab (idx.wiringMap c) = cellValue wTab c)
    ∧ (∀ i : Fin idx.publicCount,
        wTab ⟨(i : ℕ), by have h1 := idx.public_le; have h2 := idx.zk_le; omega⟩ 0 = pub i)

instance (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin 15 → F) (i : Fin n) :
    Decidable (rowSatisfies idx pub wTab i) := by
  unfold rowSatisfies
  split <;> infer_instance

instance (idx : Index F n) (pub : Fin idx.publicCount → F) (wTab : Fin n → Fin 15 → F) :
    Decidable (Satisfies idx pub wTab) := by
  unfold Satisfies
  infer_instance


/-! ## The footprint: `Satisfies` depends only on the unmasked rows

The four mask laws close every read edge into the mask — `masked_zero` (no constraint
sits on a masked row), `masked_boundary` (no two-row gate reads across the boundary),
`masked_identity` with `wiring_region` (no copy edge crosses), `public_le` (the public
pins are unmasked) — so satisfiability is a property of the unmasked restriction: the
mask's contents are simply outside the constraint system's footprint. -/

omit [DecidableEq F] in
/-- `rowSatisfies` reads only unmasked cells. -/
private theorem rowSatisfies_congr_unmasked (idx : Index F n) (pub : Fin idx.publicCount → F)
    {w w' : Fin n → Fin 15 → F}
    (hagree : ∀ i : Fin n, (i : ℕ) < n - idx.zkRows → w i = w' i)
    {i : Fin n} (h : rowSatisfies idx pub w i) : rowSatisfies idx pub w' i := by
  by_cases hm : (i : ℕ) < n - idx.zkRows
  · have hi : w i = w' i := hagree i hm
    have hnext : (idx.gates i).typ.twoRow = true → w (i + 1) = w' (i + 1) := by
      intro htwo
      have hzk := idx.zk_pos
      have hzn := idx.zk_le
      have hlt1 : (i : ℕ) + 1 < n := by omega
      have hval : ((i + 1 : Fin n) : ℕ) = (i : ℕ) + 1 := by
        have h1 : ((1 : Fin n) : ℕ) = 1 := by
          rw [Fin.val_one']
          exact Nat.mod_eq_of_lt (by omega)
        rw [Fin.add_def]
        show ((i : ℕ) + ((1 : Fin n) : ℕ)) % n = (i : ℕ) + 1
        rw [h1]
        exact Nat.mod_eq_of_lt hlt1
      by_cases hb : (i : ℕ) + 1 < n - idx.zkRows
      · exact hagree (i + 1) (by rw [hval]; exact hb)
      · have hbe : (i : ℕ) + 1 = n - idx.zkRows := by omega
        have hlaw := idx.masked_boundary i hbe
        rw [htwo] at hlaw
        cases hlaw
    unfold rowSatisfies at h ⊢
    cases htyp : (idx.gates i).typ with
    | zero => trivial
    | generic =>
      rw [htyp] at h
      rwa [← hi]
    | poseidon =>
      rw [htyp] at h
      have hn := hnext (by rw [htyp]; rfl)
      show Gate.Poseidon.Holds (Poseidon.rcMap (idx.coeffTable i))
        (Poseidon.cellMap (w' i) (w' (i + 1)))
      rw [← hi, ← hn]
      exact h
    | completeAdd =>
      rw [htyp] at h
      show Gate.AddComplete.Holds (AddComplete.cellMap (w' i))
      rw [← hi]
      exact h
    | varBaseMul =>
      rw [htyp] at h
      have hn := hnext (by rw [htyp]; rfl)
      show Gate.VarBaseMul.Holds (VarBaseMul.cellMap (w' i) (w' (i + 1)))
      rw [← hi, ← hn]
      exact h
    | endoMul =>
      rw [htyp] at h
      have hn := hnext (by rw [htyp]; rfl)
      show Gate.EndoMul.Holds idx.endoBase (EndoMul.cellMap (w' i) (w' (i + 1)))
      rw [← hi, ← hn]
      exact h
    | endoScalar =>
      rw [htyp] at h
      show Gate.EndoScalar.Holds (EndoScalar.cellMap (w' i))
      rw [← hi]
      exact h
  · have hz := idx.masked_zero i (Nat.le_of_not_lt hm)
    unfold rowSatisfies
    simp only [hz]

omit [DecidableEq F] in
/-- **`Satisfies` depends only on the unmasked rows.** Tables agreeing off the mask are
satisfiability-equivalent — the mask is outside the constraint system's read
footprint. In particular the honest prover may put anything in the zero-knowledge
rows without changing satisfiability. -/
theorem satisfies_congr_unmasked (idx : Index F n) (pub : Fin idx.publicCount → F)
    {w w' : Fin n → Fin 15 → F}
    (hagree : ∀ i : Fin n, (i : ℕ) < n - idx.zkRows → w i = w' i) :
    Satisfies idx pub w ↔ Satisfies idx pub w' := by
  have key : ∀ {u u' : Fin n → Fin 15 → F},
      (∀ i : Fin n, (i : ℕ) < n - idx.zkRows → u i = u' i) →
      Satisfies idx pub u → Satisfies idx pub u' := by
    intro u u' hag hsat
    obtain ⟨hrow, hcopy, hpub⟩ := hsat
    refine ⟨fun i => rowSatisfies_congr_unmasked idx pub hag (hrow i), ?_, ?_⟩
    · intro c
      by_cases hm : (c.2 : ℕ) < n - idx.zkRows
      · have hc2 : cellValue u' c = cellValue u c := by
          unfold cellValue
          rw [hag c.2 hm]
        have hw : cellValue u' (idx.wiringMap c) = cellValue u (idx.wiringMap c) := by
          unfold cellValue
          rw [hag (idx.wiringMap c).2 ((idx.wiring_region c).mp hm)]
        rw [hc2, hw]
        exact hcopy c
      · rw [show idx.wiringMap c = c from idx.masked_identity c (Nat.le_of_not_lt hm)]
    · intro i
      have hrw := hag
        ⟨(i : ℕ), by have h1 := idx.public_le; have h2 := idx.zk_le; omega⟩
        (lt_of_lt_of_le i.isLt idx.public_le)
      rw [← hrw]
      exact hpub i
  exact ⟨key hagree, key fun i hi => (hagree i hi).symm⟩

end Kimchi.Index
