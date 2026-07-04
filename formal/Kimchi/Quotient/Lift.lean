import Kimchi.Quotient.Domain

/-!
# The generic lift engine

Archon-original polynomial-algebra infrastructure. **Commitment-free**: everything lives over
an abstract field `[Field F]` with a primitive `n`-th root of unity supplied as a hypothesis
(`ω : F`, `hω : IsPrimitiveRoot ω n`, `0 < n`).

Every gate's "rows hold iff the constraint polynomials are divisible by `Z_H`" theorem is one
instantiation of a single abstract lemma. The lemma takes the list `P` of constraint
polynomials, the per-row list `rowCons i` of field-level constraint expressions, and a
**bridge** hypothesis asserting that evaluating `P` at the node `ω^i` reproduces `rowCons i` —
which for each gate is discharged by naturality of its `constraints` together with the
evaluation lemmas for `columnPoly` and `shift ∘ columnPoly`. **No gate formula is ever restated
at this layer.**

## Contents

* `rows_iff_dvd_of` — the ungated engine: `(∀ E ∈ P, Z_H ∣ E) ↔ ∀ i, ∀ e ∈ rowCons i, e = 0`.
* `rowsSel_iff_dvd` — the selector-gated engine: divisibility of `S · E` (with
  `S = columnPoly ω sel` a boolean selector column) is equivalent to the row constraints
  holding only on the selected rows.

Source of truth: `blueprint/src/chapters/Kimchi_Quotient_Lift.tex`.
-/

namespace Kimchi.Quotient

open Polynomial

variable {F : Type*} [Field F] {n : ℕ} {ω : F}

/-! ## The ungated engine -/

/-- **Rows hold iff the constraint polynomials are divisible by `Z_H`.** Given a primitive
`n`-th root of unity `ω` (with `0 < n`), a list `P` of constraint polynomials, per-row
constraint lists `rowCons`, and the bridge hypothesis stating that evaluating `P` at the node
`ω^i` reproduces `rowCons i`, the whole list is divisible by the vanishing polynomial iff every
per-row constraint expression is zero. -/
theorem rows_iff_dvd_of (hω : IsPrimitiveRoot ω n) (hn : 0 < n) (P : List (Polynomial F))
    (rowCons : Fin n → List F)
    (hbridge : ∀ i : Fin n, P.map (·.eval (ω ^ (i : ℕ))) = rowCons i) :
    (∀ E ∈ P, zH F n ∣ E) ↔ ∀ i, ∀ e ∈ rowCons i, e = 0 := by
  constructor
  · intro h i e he
    rw [← hbridge i, List.mem_map] at he
    obtain ⟨E, hE, rfl⟩ := he
    exact (zH_dvd_iff hω hn E).mp (h E hE) i i.isLt
  · intro h E hE
    rw [zH_dvd_iff hω hn]
    intro i hi
    have hmem : E.eval (ω ^ i) ∈ rowCons ⟨i, hi⟩ := by
      rw [← hbridge ⟨i, hi⟩]
      exact List.mem_map.mpr ⟨E, hE, rfl⟩
    exact h ⟨i, hi⟩ (E.eval (ω ^ i)) hmem

/-! ## The selector-gated engine -/

/-- **Selector-gated rows iff divisible.** kimchi multiplies a gate's constraints by a boolean
selector column `S = columnPoly ω sel` that is `1` on the rows the gate occupies and `0`
elsewhere. Divisibility of `S · E` by `Z_H` is equivalent to the row constraints holding only
on the selected rows: an inactive row (`sel i = 0`) imposes nothing. -/
theorem rowsSel_iff_dvd (hω : IsPrimitiveRoot ω n) (hn : 0 < n) (P : List (Polynomial F))
    (rowCons : Fin n → List F) (sel : Fin n → F) (hsel : ∀ i, sel i = 0 ∨ sel i = 1)
    (hbridge : ∀ i : Fin n, P.map (·.eval (ω ^ (i : ℕ))) = rowCons i) :
    (∀ E ∈ P, zH F n ∣ (columnPoly ω sel) * E) ↔
      ∀ i, sel i = 1 → ∀ e ∈ rowCons i, e = 0 := by
  constructor
  · intro h i hsi e he
    rw [← hbridge i, List.mem_map] at he
    obtain ⟨E, hE, rfl⟩ := he
    have hd := (zH_dvd_iff hω hn _).mp (h E hE) i i.isLt
    rw [eval_mul, eval_columnPoly hω sel i, hsi, one_mul] at hd
    exact hd
  · intro h E hE
    rw [zH_dvd_iff hω hn]
    intro i hi
    rw [eval_mul]
    have heq : (columnPoly ω sel).eval (ω ^ i) = sel ⟨i, hi⟩ :=
      eval_columnPoly hω sel ⟨i, hi⟩
    rw [heq]
    rcases hsel ⟨i, hi⟩ with h0 | h1
    · rw [h0, zero_mul]
    · rw [h1, one_mul]
      have hmem : E.eval (ω ^ i) ∈ rowCons ⟨i, hi⟩ := by
        rw [← hbridge ⟨i, hi⟩]
        exact List.mem_map.mpr ⟨E, hE, rfl⟩
      exact h ⟨i, hi⟩ h1 (E.eval (ω ^ i)) hmem

end Kimchi.Quotient
