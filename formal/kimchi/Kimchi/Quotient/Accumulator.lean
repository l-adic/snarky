import Mathlib

/-!
# The permutation accumulator telescopes into a grand-product equality

The bridge between the row-level permutation constraint and the grand-product algebra of
`Kimchi.Quotient.GrandProduct` (proof-systems `permutation.rs`): the accumulator column
`z` satisfies `z(row 0) = 1`, the division-free per-row recurrence
`z(k+1) · denₖ = z(k) · numₖ`, and the boundary pin `z(row m) = 1`; telescoping the
recurrence forces `∏ num = ∏ den`. At the challenges `(β, γ)` the factors are the pair
factors `wᵢ + β·posᵢ + γ`, so the conclusion is exactly the hypothesis of
`multiset_eq_of_prod_eval`.

This is **pure finite induction**: no domain, no root of unity, no polynomials — indexed
families over an abstract field. The kimchi-facing content (the `zkpm`-gated wire
constraint producing the recurrence on the unmasked rows, the Lagrange-gated boundary
pins, the two-row quotient engine) instantiates these hypotheses downstream.

Because kimchi's recurrence is the multiplied-out form, no nonvanishing hypothesis on the
denominators is needed for this direction: the invariant
`z(k) · ∏_{j<k} den = ∏_{j<k} num` is maintained multiplicatively, and the boundary pins
eliminate `z` at both ends.
-/

namespace Kimchi.Quotient

variable {F : Type*} [Field F]

/-- **Accumulator telescoping.** An accumulator pinned to `1` at both ends of a row range
and satisfying the division-free recurrence `z(k+1) · denₖ = z(k) · numₖ` on it forces the
grand products to agree: `∏ num = ∏ den`. -/
theorem prod_eq_of_accumulator {m : ℕ} (num den z : ℕ → F)
    (h0 : z 0 = 1) (hm : z m = 1)
    (hstep : ∀ k < m, z (k + 1) * den k = z k * num k) :
    ∏ k ∈ Finset.range m, num k = ∏ k ∈ Finset.range m, den k := by
  have aux : ∀ k, k ≤ m →
      z k * ∏ j ∈ Finset.range k, den j = ∏ j ∈ Finset.range k, num j := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      intro hk
      have hk' : k < m := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      calc z (k + 1) * ((∏ j ∈ Finset.range k, den j) * den k)
          = (z (k + 1) * den k) * ∏ j ∈ Finset.range k, den j := by ring
        _ = (z k * num k) * ∏ j ∈ Finset.range k, den j := by rw [hstep k hk']
        _ = (z k * ∏ j ∈ Finset.range k, den j) * num k := by ring
        _ = (∏ j ∈ Finset.range k, num j) * num k := by rw [ih hk'.le]
  have h := aux m le_rfl
  rw [hm, one_mul] at h
  exact h.symm

/-- **Accumulator construction** — the converse of `prod_eq_of_accumulator`, and the
completeness direction's witness. With nonzero denominators and agreeing grand
products, the running-ratio column `z k = (∏_{j<k} num) / (∏_{j<k} den)` is an
accumulator: pinned to `1` at both ends and satisfying the division-free recurrence.
This is the one place the nonzero-denominator hypothesis is genuinely needed — the
soundness direction (`prod_eq_of_accumulator`) is division-free. -/
theorem accumulator_of_prod_eq {m : ℕ} (num den : ℕ → F)
    (hden : ∀ k < m, den k ≠ 0)
    (hprod : ∏ k ∈ Finset.range m, num k = ∏ k ∈ Finset.range m, den k) :
    ∃ z : ℕ → F, z 0 = 1 ∧ z m = 1
      ∧ ∀ k < m, z (k + 1) * den k = z k * num k := by
  have hdprod : ∀ k, k ≤ m → (∏ j ∈ Finset.range k, den j) ≠ 0 := fun k hk =>
    Finset.prod_ne_zero_iff.mpr fun j hj =>
      hden j (lt_of_lt_of_le (Finset.mem_range.mp hj) hk)
  refine ⟨fun k => (∏ j ∈ Finset.range k, num j) / (∏ j ∈ Finset.range k, den j),
    by simp, ?_, ?_⟩
  · dsimp only
    rw [hprod, div_self (hdprod m le_rfl)]
  · intro k hk
    dsimp only
    have hd := hdprod k hk.le
    have hdk := hden k hk
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    field_simp

end Kimchi.Quotient
