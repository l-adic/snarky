import Mathlib

/-!
# A `K × 2` combinatorial rectangle in a dense subset of a product

This file is the **combinatorial heart of the special-soundness extraction** for the
kimchi batch-opening grid (forking stage (a)): the purely finite statement that a subset
of a product `α × β` that is *dense enough* must contain a `K × 2` **combinatorial
rectangle** — `K` distinct rows sharing two distinct columns. Composed with the
`KimchiBatchAcc` capstones (`Kimchi/Verifier/Capstone.lean`), it upgrades the grid from
hypothesis to consequence: a prover strategy accepted on enough `(ξ, r)` challenge pairs
*yields* the `43 × 2` extraction grid, hence soundness.

The proof is the classical **heavy-rows / Zarankiewicz (Kővári–Sós–Turán) double count**:
Cauchy–Schwarz on the row degrees `dₓ` forces `|α| · ∑ₓ dₓ(dₓ−1) ≥ |S|·(|S|−|α|)`, the
sum `∑ₓ dₓ(dₓ−1)` counts exactly the incidences (row, ordered pair of distinct columns)
of `S`, and the pigeonhole principle over the `|β|·(|β|−1)` ordered column pairs produces
one pair shared by at least `K` rows as soon as
`(K−1)·|α|·|β|·(|β|−1) < |S|·(|S|−|α|)`.

Quantitatively: asking for a `K × 2` **product** grid (every extracted row against *both*
columns) costs a *quadratic* (square-root) density threshold — the hypothesis reads
`~ K·|α|·|β|²`, i.e. an accepting density `≳ √(K/|β|)` over `α × β` — whereas a
`(K, 2)`-**tree** transcript (fresh second challenges per row) would only cost
`~ K·|α|·|β|`. The accumulated `KimchiBatchAcc` grid consumes the product shape, so the
√-loss is accepted here and priced into the density hypothesis of the capstones (still
`≈ 2⁻¹²⁴` at the `~ 2²⁵⁴` Pasta fields).

The file is pure finite combinatorics: no protocol content, no field structure — just
`Fintype`/`Finset` counting, fully proved (`#print axioms Kimchi.Quotient.exists_rectangle`
= `[propext, Classical.choice, Quot.sound]`).

## Contents

* `exists_rectangle` — **the `K × 2` rectangle from density**: if
  `(K−1)·|α|·|β|·(|β|−1) < |S|·(|S|−|α|)` then `S ⊆ α × β` contains `K` distinct rows
  sharing two distinct columns.

The supporting development is private: row degrees (`rowDeg`) and their column sets
(`colSet`), the Cauchy–Schwarz bound (`key_ineq`), the double count over ordered pairs
of distinct columns (`double_count`), and the pigeonhole + extraction assembly inside
`exists_rectangle` itself.
-/

namespace Kimchi.Quotient

/-! ## The supporting counts -/

section Rectangle

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The row degree of `x`: how many entries of `S` lie in row `x`. -/
private def rowDeg (S : Finset (α × β)) (x : α) : ℕ :=
  (S.filter fun q => q.1 = x).card

/-- The column set of row `x`: the columns `b` with `(x, b) ∈ S`. -/
private def colSet (S : Finset (α × β)) (x : α) : Finset β :=
  (S.filter fun q => q.1 = x).image Prod.snd

/-- The rows through an ordered pair of columns `p`: the `x` with both `(x, p.1)` and
`(x, p.2)` in `S`. -/
private def rowsFor (S : Finset (α × β)) (p : β × β) : Finset α :=
  Finset.univ.filter fun x => (x, p.1) ∈ S ∧ (x, p.2) ∈ S

omit [Fintype α] [Fintype β] in
private lemma mem_colSet {S : Finset (α × β)} {x : α} {b : β} :
    b ∈ colSet S x ↔ (x, b) ∈ S := by
  simp only [colSet, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨qa, qb⟩, ⟨hq, h1⟩, h2⟩
    obtain rfl : qa = x := h1
    obtain rfl : qb = b := h2
    exact hq
  · exact fun hb => ⟨(x, b), ⟨hb, rfl⟩, rfl⟩

omit [Fintype β] in
private lemma mem_rowsFor {S : Finset (α × β)} {p : β × β} {x : α} :
    x ∈ rowsFor S p ↔ (x, p.1) ∈ S ∧ (x, p.2) ∈ S := by
  simp only [rowsFor, Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype α] [Fintype β] in
/-- Row `x` has exactly `rowDeg S x` columns: `Prod.snd` is injective on a fixed row. -/
private lemma card_colSet (S : Finset (α × β)) (x : α) :
    (colSet S x).card = rowDeg S x := by
  refine Finset.card_image_of_injOn fun q hq q' hq' h => ?_
  simp only [Finset.mem_coe, Finset.mem_filter] at hq hq'
  exact Prod.ext (hq.2.trans hq'.2.symm) h

omit [Fintype β] [DecidableEq β] in
/-- The row degrees sum to `|S|` (fibering `S` over `Prod.fst`). -/
private lemma sum_rowDeg (S : Finset (α × β)) : ∑ x, rowDeg S x = S.card := by
  simp only [rowDeg]
  exact (Finset.card_eq_sum_card_fiberwise fun q _ => Finset.mem_univ q.1).symm

/-! ## Step 2 — Cauchy–Schwarz on the row degrees -/

omit [Fintype β] [DecidableEq β] in
/-- **Cauchy–Schwarz bound**: `|S|·(|S|−|α|) ≤ |α| · ∑ₓ dₓ(dₓ−1)` for the row degrees. -/
private lemma key_ineq (S : Finset (α × β)) :
    S.card * (S.card - Fintype.card α)
      ≤ Fintype.card α * ∑ x, rowDeg S x * (rowDeg S x - 1) := by
  have hcs : S.card ^ 2 ≤ Fintype.card α * ∑ x, rowDeg S x ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset α)) (f := rowDeg S)
    rwa [sum_rowDeg, Nat.cast_id, Finset.card_univ] at h
  have hpt : ∀ n : ℕ, n * (n - 1) + n = n * n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rfl
    · calc n * (n - 1) + n = n * (n - 1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ = n * n := by rw [Nat.sub_add_cancel hn]
  have hsum : (∑ x, rowDeg S x * (rowDeg S x - 1)) + S.card = ∑ x, rowDeg S x ^ 2 := by
    rw [← sum_rowDeg S, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [hpt (rowDeg S x), pow_two]
  rw [Nat.mul_sub, tsub_le_iff_right, mul_comm S.card (Fintype.card α)]
  calc S.card * S.card = S.card ^ 2 := (pow_two _).symm
    _ ≤ Fintype.card α * ∑ x, rowDeg S x ^ 2 := hcs
    _ = Fintype.card α * ∑ x, rowDeg S x * (rowDeg S x - 1)
          + Fintype.card α * S.card := by rw [← hsum, mul_add]

/-! ## Step 3 — the double count over ordered pairs of distinct columns -/

/-- **Double count**: `∑ₓ dₓ(dₓ−1)` is the number of incidences (row, ordered pair of
distinct columns), counted column-pair-wise. -/
private lemma double_count (S : Finset (α × β)) :
    ∑ x, rowDeg S x * (rowDeg S x - 1)
      = ∑ p ∈ (Finset.univ : Finset β).offDiag, (rowsFor S p).card := by
  have hrow : ∀ x : α, rowDeg S x * (rowDeg S x - 1)
      = ((Finset.univ : Finset β).offDiag.filter
          fun p => (x, p.1) ∈ S ∧ (x, p.2) ∈ S).card := by
    intro x
    have hset : ((Finset.univ : Finset β).offDiag.filter
        fun p => (x, p.1) ∈ S ∧ (x, p.2) ∈ S) = (colSet S x).offDiag := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_offDiag, mem_colSet, Finset.mem_univ,
        true_and]
      tauto
    rw [hset, Finset.offDiag_card, card_colSet, Nat.mul_sub, Nat.mul_one]
  calc ∑ x, rowDeg S x * (rowDeg S x - 1)
      = ∑ x : α, ((Finset.univ : Finset β).offDiag.filter
          fun p => (x, p.1) ∈ S ∧ (x, p.2) ∈ S).card :=
        Finset.sum_congr rfl fun x _ => hrow x
    _ = ∑ p ∈ (Finset.univ : Finset β).offDiag, (rowsFor S p).card := by
        simp only [Finset.card_filter, rowsFor]
        exact Finset.sum_comm

/-! ## The main theorem — steps 4 (pigeonhole) and 5 (extraction) -/

/-- **A `K × 2` combinatorial rectangle in a dense set.** If
`(K−1)·|α|·|β|·(|β|−1) < |S|·(|S| − |α|)` then `S ⊆ α × β` contains `K` distinct rows
sharing two distinct columns. -/
theorem exists_rectangle (S : Finset (α × β)) (K : ℕ)
    (h : (K - 1) * Fintype.card α * (Fintype.card β * (Fintype.card β - 1))
        < S.card * (S.card - Fintype.card α)) :
    ∃ (a : Fin K → α) (b₁ b₂ : β), Function.Injective a ∧ b₁ ≠ b₂
      ∧ ∀ i, (a i, b₁) ∈ S ∧ (a i, b₂) ∈ S := by
  -- Step 4: some ordered pair of distinct columns is shared by at least `K` rows.
  have hpigeon : ∃ p ∈ (Finset.univ : Finset β).offDiag, K ≤ (rowsFor S p).card := by
    by_contra hcon
    push Not at hcon
    have hbound : ∑ p ∈ (Finset.univ : Finset β).offDiag, (rowsFor S p).card
        ≤ (Finset.univ : Finset β).offDiag.card * (K - 1) := by
      have hle := Finset.sum_le_card_nsmul (Finset.univ : Finset β).offDiag
        (fun p => (rowsFor S p).card) (K - 1)
        (fun p hp => Nat.le_pred_of_lt (hcon p hp))
      simpa [smul_eq_mul] using hle
    have hoff : (Finset.univ : Finset β).offDiag.card
        = Fintype.card β * (Fintype.card β - 1) := by
      rw [Finset.offDiag_card, Finset.card_univ, Nat.mul_sub, Nat.mul_one]
    have hfinal : S.card * (S.card - Fintype.card α)
        ≤ (K - 1) * Fintype.card α * (Fintype.card β * (Fintype.card β - 1)) :=
      calc S.card * (S.card - Fintype.card α)
          ≤ Fintype.card α * ∑ x, rowDeg S x * (rowDeg S x - 1) := key_ineq S
        _ = Fintype.card α * ∑ p ∈ (Finset.univ : Finset β).offDiag, (rowsFor S p).card :=
            by rw [double_count]
        _ ≤ Fintype.card α * ((Finset.univ : Finset β).offDiag.card * (K - 1)) :=
            Nat.mul_le_mul le_rfl hbound
        _ = (K - 1) * Fintype.card α * (Fintype.card β * (Fintype.card β - 1)) := by
            rw [hoff]; ring
    exact absurd h (not_lt.mpr hfinal)
  obtain ⟨⟨b₁, b₂⟩, hpmem, hK⟩ := hpigeon
  have hne : b₁ ≠ b₂ := (Finset.mem_offDiag.mp hpmem).2.2
  -- Step 5: extract `K` of those rows as an injective `Fin K`-family.
  obtain ⟨u, husub, hucard⟩ := Finset.exists_subset_card_eq hK
  have hcardty : Fintype.card ↥u = K := by rw [Fintype.card_coe]; exact hucard
  let e := Fintype.equivFinOfCardEq hcardty
  refine ⟨fun i => ((e.symm i : ↥u) : α), b₁, b₂, ?_, hne, ?_⟩
  · intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  · intro i
    exact mem_rowsFor.mp (husub (e.symm i).property)

end Rectangle

end Kimchi.Quotient
