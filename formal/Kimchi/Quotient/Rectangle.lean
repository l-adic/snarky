import Mathlib

/-!
# The counting toolkit of the forking-lemma elaboration

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

Forking stage (b3) grows the file from "the rectangle" into the **counting toolkit of
the forking-lemma elaboration**. Alongside the rectangle it provides the two further
counting primitives the full-protocol strategy model (stage (b5)) composes with
`exists_rectangle` to derive the transcript tree from accepting density: **heavy rows**
(`card_heavyRows`, the Markov/pigeonhole bound — enough total density forces `m` rows of
degree `≥ θ`) and **distinct-powers selection** (`exists_distinct_powers` — from a large
enough subset of a finite field, avoiding an exclusion set, one can greedily pick `K`
elements with pairwise-distinct `n`-th powers, because each `n`-th-power fiber has at
most `n` elements, `card_pow_fiber_le`). All `Fintype`/counting content of the forking
argument stays in this layer.

The file is pure finite combinatorics (plus, for the power fibers, root counting in a
field): no protocol content — just `Fintype`/`Finset` counting, fully proved
(`#print axioms` on every headline theorem = `[propext, Classical.choice, Quot.sound]`).

## Contents

* `exists_rectangle` — **the `K × 2` rectangle from density**: if
  `(K−1)·|α|·|β|·(|β|−1) < |S|·(|S|−|α|)` then `S ⊆ α × β` contains `K` distinct rows
  sharing two distinct columns.
* `rowDeg`, `rowSlice`, `mem_rowSlice`, `card_rowSlice` — the row-degree / row-slice API
  of a subset of a product.
* `heavyRows`, `mem_heavyRows`, `card_heavyRows` — **heavy rows from density (Markov)**:
  if `(m−1)·|β| + |α|·(θ−1) < |S|` then at least `m` rows have degree `≥ θ`.
* `card_pow_fiber_le` — an `n`-th-power fiber in a field has at most `n` elements (they
  are roots of `Xⁿ − c`).
* `exists_distinct_powers` — **distinct-powers selection**: from `T` with
  `|Excl| + (K−1)·n < |T|` one can pick `K` elements of `T` outside `Excl` with
  pairwise-distinct `n`-th powers.

The supporting development of the rectangle stays private: the column sets (`colSet`),
the Cauchy–Schwarz bound (`key_ineq`), the double count over ordered pairs of distinct
columns (`double_count`), and the pigeonhole + extraction assembly inside
`exists_rectangle` itself. The row degree `rowDeg` is public as part of the counting
API.
-/

namespace Kimchi.Quotient

/-! ## The supporting counts -/

section Rectangle

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The row degree of `x`: how many entries of `S` lie in row `x`. -/
def rowDeg (S : Finset (α × β)) (x : α) : ℕ :=
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

/-! ## The counting toolkit, part 1 — row slices and heavy rows (Markov)

The strategy layer (stage (b5)) works with the rows of the accepting set directly, not
only with the extracted rectangle: it needs the slice of a row as a `Finset` of columns
(`rowSlice`, the public counterpart of the rectangle's private `colSet`) and the Markov
bound producing many rows of high degree from total density (`card_heavyRows`). -/

omit [Fintype α] [Fintype β] in
/-- The slice of `S` at row `a`, as a set of columns: the `b` with `(a, b) ∈ S`. Public
counterpart of the rectangle's private `colSet`, exposed for the strategy layer. -/
def rowSlice (S : Finset (α × β)) (a : α) : Finset β :=
  (S.filter fun q => q.1 = a).image Prod.snd

omit [Fintype α] [Fintype β] in
/-- Membership in the row slice at `a` is membership of the pair in `S`. -/
theorem mem_rowSlice {S : Finset (α × β)} {a : α} {b : β} :
    b ∈ rowSlice S a ↔ (a, b) ∈ S := by
  simp only [rowSlice, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨qa, qb⟩, ⟨hq, h1⟩, h2⟩
    obtain rfl : qa = a := h1
    obtain rfl : qb = b := h2
    exact hq
  · exact fun hb => ⟨(a, b), ⟨hb, rfl⟩, rfl⟩

omit [Fintype α] [Fintype β] in
/-- Row `a` has exactly `rowDeg S a` columns: `Prod.snd` is injective on a fixed row. -/
theorem card_rowSlice (S : Finset (α × β)) (a : α) :
    (rowSlice S a).card = rowDeg S a := by
  refine Finset.card_image_of_injOn fun q hq q' hq' h => ?_
  simp only [Finset.mem_coe, Finset.mem_filter] at hq hq'
  exact Prod.ext (hq.2.trans hq'.2.symm) h

omit [Fintype β] [DecidableEq β] in
/-- The rows of degree at least `θ`. -/
def heavyRows (S : Finset (α × β)) (θ : ℕ) : Finset α :=
  Finset.univ.filter fun a => θ ≤ rowDeg S a

omit [Fintype β] [DecidableEq β] in
/-- Membership in the heavy rows is exactly the degree threshold. -/
theorem mem_heavyRows {S : Finset (α × β)} {θ : ℕ} {a : α} :
    a ∈ heavyRows S θ ↔ θ ≤ rowDeg S a := by
  simp only [heavyRows, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Heavy rows from density (Markov).** If `(m − 1)·|β| + |α|·(θ − 1) < |S|` then at
least `m` rows have degree `≥ θ`: otherwise the `≤ m − 1` heavy rows contribute at most
`(m − 1)·|β|` entries of `S` (a row has at most `|β|` entries) and the light rows at
most `|α|·(θ − 1)` (each has degree `≤ θ − 1`), short of `|S|` in total. -/
theorem card_heavyRows (S : Finset (α × β)) (θ m : ℕ)
    (h : (m - 1) * Fintype.card β + Fintype.card α * (θ - 1) < S.card) :
    m ≤ (heavyRows S θ).card := by
  by_contra hcon
  push Not at hcon
  have hheavy_card : (heavyRows S θ).card ≤ m - 1 := Nat.le_pred_of_lt hcon
  have hdeg_le : ∀ a : α, rowDeg S a ≤ Fintype.card β := fun a => by
    rw [← card_rowSlice]; exact Finset.card_le_univ _
  have hheavy : ∑ a ∈ heavyRows S θ, rowDeg S a ≤ (m - 1) * Fintype.card β :=
    calc ∑ a ∈ heavyRows S θ, rowDeg S a
        ≤ (heavyRows S θ).card * Fintype.card β := by
          simpa [smul_eq_mul] using Finset.sum_le_card_nsmul (heavyRows S θ)
            (fun a => rowDeg S a) (Fintype.card β) fun a _ => hdeg_le a
      _ ≤ (m - 1) * Fintype.card β := Nat.mul_le_mul hheavy_card le_rfl
  have hlight : ∑ a ∈ Finset.univ.filter (fun a => ¬ θ ≤ rowDeg S a), rowDeg S a
      ≤ Fintype.card α * (θ - 1) :=
    calc ∑ a ∈ Finset.univ.filter (fun a => ¬ θ ≤ rowDeg S a), rowDeg S a
        ≤ (Finset.univ.filter fun a => ¬ θ ≤ rowDeg S a).card * (θ - 1) := by
          simpa [smul_eq_mul] using Finset.sum_le_card_nsmul
            (Finset.univ.filter fun a => ¬ θ ≤ rowDeg S a) (fun a => rowDeg S a) (θ - 1)
            fun a ha => Nat.le_pred_of_lt (Nat.lt_of_not_le (Finset.mem_filter.mp ha).2)
      _ ≤ Fintype.card α * (θ - 1) :=
          Nat.mul_le_mul ((Finset.card_filter_le _ _).trans Finset.card_univ.le) le_rfl
  have hsplit : ∑ a ∈ heavyRows S θ, rowDeg S a
      + ∑ a ∈ Finset.univ.filter (fun a => ¬ θ ≤ rowDeg S a), rowDeg S a = S.card := by
    unfold heavyRows
    rw [← sum_rowDeg S]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have htot : S.card ≤ (m - 1) * Fintype.card β + Fintype.card α * (θ - 1) := by
    rw [← hsplit]
    exact Nat.add_le_add hheavy hlight
  exact absurd h (not_lt.mpr htot)

end Rectangle

/-! ## The counting toolkit, part 2 — distinct-powers selection over a finite field

The forking argument re-runs the protocol at fresh challenges whose relevant derived
values (`n`-th powers, e.g. the evaluation points `ζ^n` of a chunked commitment) must be
pairwise distinct and avoid a bad set. Over a field the fiber of `x ↦ xⁿ` above `c` has
at most `n` elements — its members are roots of `Xⁿ − c` (the exact root-counting idiom
of `badZetas`/`card_badZetas_le` in `Kimchi/Quotient/SchwartzZippel.lean`) — so a greedy
pick succeeds as long as the source set beats the exclusion set plus `K − 1` fibers. -/

section DistinctPowers

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- The `n`-th-power fiber over `c` has at most `n` elements: they are roots of the
nonzero polynomial `Xⁿ − c`. -/
theorem card_pow_fiber_le (n : ℕ) (hn : 0 < n) (c : F) :
    (Finset.univ.filter fun x : F => x ^ n = c).card ≤ n := by
  have hsub : (Finset.univ.filter fun x : F => x ^ n = c)
      ⊆ (Polynomial.X ^ n - Polynomial.C c : Polynomial F).roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots']
    refine ⟨Polynomial.X_pow_sub_C_ne_zero hn c, ?_⟩
    simp [Polynomial.IsRoot.def, (Finset.mem_filter.mp hx).2]
  calc (Finset.univ.filter fun x : F => x ^ n = c).card
      ≤ (Polynomial.X ^ n - Polynomial.C c : Polynomial F).roots.toFinset.card :=
        Finset.card_le_card hsub
    _ ≤ Multiset.card (Polynomial.X ^ n - Polynomial.C c : Polynomial F).roots :=
        Multiset.toFinset_card_le _
    _ ≤ (Polynomial.X ^ n - Polynomial.C c : Polynomial F).natDegree :=
        Polynomial.card_roots' _
    _ = n := Polynomial.natDegree_X_pow_sub_C

/-- **Distinct-powers selection.** From a large enough `T`, avoiding an exclusion set
`Excl`, one can pick `K` elements with pairwise-distinct `n`-th powers: greedily, each
new pick must avoid `Excl` plus the (≤ `n`-element, `card_pow_fiber_le`) power fibers of
the previous picks, forbidding at most `|Excl| + (K−1)·n < |T|` elements. -/
theorem exists_distinct_powers (T Excl : Finset F) (n K : ℕ) (hn : 0 < n)
    (h : Excl.card + (K - 1) * n < T.card) :
    ∃ ζs : Fin K → F,
      (∀ s, ζs s ∈ T ∧ ζs s ∉ Excl)
      ∧ Function.Injective fun s => ζs s ^ n := by
  induction K with
  | zero => exact ⟨Fin.elim0, fun s => s.elim0, fun s => s.elim0⟩
  | succ K ih =>
    rw [Nat.add_sub_cancel] at h
    -- The induction hypothesis applies: `(K − 1)·n ≤ K·n`.
    obtain ⟨ζs, hmem, hinj⟩ := ih (lt_of_le_of_lt
      (Nat.add_le_add_left (Nat.mul_le_mul (Nat.sub_le K 1) le_rfl) _) h)
    -- A fresh pick outside the exclusion set and all previous power fibers exists.
    obtain ⟨z, hzT, hzf⟩ : ∃ z ∈ T, z ∉ Excl ∪ Finset.univ.biUnion
        (fun s : Fin K => Finset.univ.filter fun x : F => x ^ n = ζs s ^ n) := by
      by_contra hcon
      push Not at hcon
      have hforb : (Excl ∪ Finset.univ.biUnion fun s : Fin K =>
          Finset.univ.filter fun x : F => x ^ n = ζs s ^ n).card ≤ Excl.card + K * n := by
        refine (Finset.card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
        refine Finset.card_biUnion_le.trans ?_
        calc ∑ s : Fin K, (Finset.univ.filter fun x : F => x ^ n = ζs s ^ n).card
            ≤ ∑ _s : Fin K, n := Finset.sum_le_sum fun s _ => card_pow_fiber_le n hn _
          _ = K * n := by simp [Finset.sum_const, Finset.card_univ]
      exact absurd ((Finset.card_le_card fun z hz => hcon z hz).trans hforb)
        (not_le.mpr h)
    have hzE : z ∉ Excl := fun hz => hzf (Finset.mem_union_left _ hz)
    have hznew : ∀ s : Fin K, z ^ n ≠ ζs s ^ n := fun s hz =>
      hzf (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨s, Finset.mem_univ s, Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz⟩⟩))
    refine ⟨Fin.snoc ζs z, fun s => ?_, fun s t hst => ?_⟩
    · rcases Fin.eq_castSucc_or_eq_last s with ⟨i, rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]; exact hmem i
      · rw [Fin.snoc_last]; exact ⟨hzT, hzE⟩
    · rcases Fin.eq_castSucc_or_eq_last s with ⟨i, rfl⟩ | rfl <;>
          rcases Fin.eq_castSucc_or_eq_last t with ⟨j, rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc] at hst
        exact congrArg Fin.castSucc (hinj hst)
      · simp only [Fin.snoc_castSucc, Fin.snoc_last] at hst
        exact absurd hst.symm (hznew i)
      · simp only [Fin.snoc_castSucc, Fin.snoc_last] at hst
        exact absurd hst (hznew j)
      · rfl

end DistinctPowers

end Kimchi.Quotient
