import Kimchi.Quotient.Aggregate

/-!
# Counting Schwartz–Zippel: single-challenge α-separation

This file replaces the injective-α-family surrogate of `dvd_separation`
(`Kimchi/Quotient/Aggregate.lean`) with the standard **counting** form of the
Schwartz–Zippel argument for kimchi's α-aggregation: a *single* challenge `α` suffices to
separate divisibility across a family of constraint polynomials, provided `α` avoids an
explicit **bad set** whose cardinality is proved small. Statements stay fully deterministic —
"for every `α` outside a proved-small finite set" — so no probability theory enters; the
probabilistic reading (a uniformly random `α` is good except with probability
`≤ n·(K−1)/|F|`) is exactly the cardinality bound.

It is **commitment-free**: everything lives over an abstract field `[Field F]` (with
decidable equality, needed only to *define* the bad sets), with a primitive `n`-th root of
unity supplied as a hypothesis. There is no group, no SRS, no Fiat–Shamir.

## Contents

The `SZ` section is the field-level vocabulary, one row at a time:

* `SZ.combPoly` — the combining polynomial `∑ k, c k · X^k` of a coefficient vector.
* `SZ.badComb` — the bad challenges of one vector: empty for the zero vector, else the
  roots of its (nonzero) combining polynomial.
* `SZ.card_badComb_le` — **counting SZ**: at most `K − 1` challenges hide a nonzero vector.
* `SZ.eq_zero_of_comb_eq_zero` — **the combination lemma**: a good challenge annihilating
  the combination annihilates every entry. This is the atomic "one good challenge suffices"
  step; it replaces every Vandermonde-over-an-injective-family argument.

The main section assembles the rows of the evaluation domain:

* `badAlphas` — the bad challenges of a constraint *family*: the union over domain rows of
  the row-wise bad sets.
* `card_badAlphas_le` — the bad set has at most `n · (K − 1)` elements.
* `dvd_separation` — single-challenge α-separation: divisibility of the α-aggregate for
  ONE good `α` separates across the individual constraint polynomials.
* `badZetas` — the bad ζ for a claimed quotient `C = t · Z_H`: empty when they agree, else
  the roots of `C − t · Z_H`.
* `card_badZetas_le` — **counting SZ, ζ-axis**: at most `D` bad ζ when both sides have degree
  `≤ D`.
* `zH_dvd_of_eval` — a single good ζ pins `C = t · Z_H`, hence `Z_H ∣ C`.
* `dvd_of_evalCheck` — the composed pinning–separation engine of
  `dvd_of_evalCheck` (`Kimchi/Quotient/Lift.lean`), with the α-, ζ- and quotient-families all
  collapsed to a single `α`, a single ζ, and a single quotient `t`.
-/

namespace Kimchi.Quotient

open Polynomial

/-! ## The combining polynomial and its bad-challenge set -/

namespace SZ

variable {F : Type*} [Field F] [DecidableEq F]

/-- The combining polynomial of a coefficient vector: `∑ k, c k · X^k`. -/
noncomputable def combPoly {K : ℕ} (c : Fin K → F) : Polynomial F :=
  ∑ k : Fin K, Polynomial.C (c k) * Polynomial.X ^ (k : ℕ)

omit [DecidableEq F] in
/-- The `k`-th coefficient of `combPoly c` is `c k`: the `Fin K` exponents are distinct, so
the sum contributes exactly one monomial in degree `k`. -/
private theorem combPoly_coeff {K : ℕ} (c : Fin K → F) (k : Fin K) :
    (combPoly c).coeff (k : ℕ) = c k := by
  rw [combPoly, Polynomial.finsetSum_coeff, Finset.sum_eq_single k]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro d _ hdk
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg fun heq => hdk (Fin.val_injective heq).symm, mul_zero]
  · exact fun hk => absurd (Finset.mem_univ k) hk

omit [DecidableEq F] in
/-- The combining polynomial vanishes identically iff the vector is zero. -/
theorem combPoly_eq_zero_iff {K : ℕ} (c : Fin K → F) : combPoly c = 0 ↔ ∀ k, c k = 0 := by
  constructor
  · intro h k
    have hc := combPoly_coeff c k
    rw [h, Polynomial.coeff_zero] at hc
    exact hc.symm
  · intro h
    unfold combPoly
    exact Finset.sum_eq_zero fun k _ => by rw [h k, map_zero, zero_mul]

omit [DecidableEq F] in
/-- Evaluating the combining polynomial computes the α-combination of the vector. -/
theorem combPoly_eval {K : ℕ} (c : Fin K → F) (α : F) :
    (combPoly c).eval α = ∑ k : Fin K, α ^ (k : ℕ) * c k := by
  unfold combPoly
  rw [Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun k _ => by
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring

/-- Bad challenges for one vector: empty if the vector is zero, else the roots of the
(nonzero) combining polynomial. -/
noncomputable def badComb {K : ℕ} (c : Fin K → F) : Finset F :=
  if ∀ k, c k = 0 then ∅ else (combPoly c).roots.toFinset

omit [DecidableEq F] in
/-- The combining polynomial has degree at most `K − 1` (each summand has degree `≤ k`). -/
private theorem natDegree_combPoly_le {K : ℕ} (c : Fin K → F) :
    (combPoly c).natDegree ≤ K - 1 := by
  unfold combPoly
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  rw [Polynomial.natDegree_X_pow]
  have := k.isLt
  omega

/-- **Counting SZ**: at most `K − 1` challenges can hide a nonzero vector. The zero case is
the empty set; otherwise the bad set consists of the distinct roots of a nonzero polynomial
of degree `≤ K − 1`. -/
theorem card_badComb_le {K : ℕ} (c : Fin K → F) : (badComb c).card ≤ K - 1 := by
  unfold badComb
  split_ifs with h
  · simp
  · refine le_trans (Multiset.toFinset_card_le _) ?_
    exact le_trans (Polynomial.card_roots' _) (natDegree_combPoly_le c)

/-- **The combination lemma** — the atomic "one good challenge suffices" step; replaces every
Vandermonde-over-an-injective-family argument. If a challenge outside `badComb c`
annihilates the α-combination of the vector `c`, then `c` is the zero vector. -/
theorem eq_zero_of_comb_eq_zero {K : ℕ} (c : Fin K → F) (α : F)
    (hα : α ∉ badComb c) (hzero : ∑ k : Fin K, α ^ (k : ℕ) * c k = 0) : ∀ k, c k = 0 := by
  by_contra hne
  apply hα
  unfold badComb
  rw [if_neg hne, Multiset.mem_toFinset, Polynomial.mem_roots']
  refine ⟨fun h0 => hne ((combPoly_eq_zero_iff c).mp h0), ?_⟩
  show (combPoly c).eval α = 0
  rw [combPoly_eval]
  exact hzero

end SZ

/-! ## Bad challenges of a constraint family, and single-challenge separation -/

variable {F : Type*} [Field F] [DecidableEq F]

/-- Bad α's for a constraint family: α is bad if at some domain row it kills a nonzero vector
of constraint values. -/
noncomputable def badAlphas {K : ℕ} (C : Fin K → Polynomial F) (ω : F) (n : ℕ) : Finset F :=
  Finset.univ.biUnion fun i : Fin n => SZ.badComb fun k => (C k).eval (ω ^ (i : ℕ))

/-- **The bad set is small**: at most `n · (K − 1)` — `n` rows, each contributing at most
`K − 1` bad challenges by `SZ.card_badComb_le`. -/
theorem card_badAlphas_le {K : ℕ} (C : Fin K → Polynomial F) (ω : F) (n : ℕ) :
    (badAlphas C ω n).card ≤ n * (K - 1) := by
  refine le_trans Finset.card_biUnion_le ?_
  refine le_trans (Finset.sum_le_sum fun i _ => SZ.card_badComb_le _) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **α-separation, single-challenge form** — replaces `dvd_separation`'s injective-α family.
If `Z_H` divides the α-aggregate for ONE challenge `α` outside `badAlphas C ω n`, then `Z_H`
divides each individual constraint polynomial. Argue pointwise on the domain: at each node
`ω^i` the aggregate's value is the α-combination of the row vector `k ↦ (C k)(ω^i)`, and a
good `α` annihilating the combination annihilates every entry. -/
theorem dvd_separation {K n : ℕ} [NeZero n] {ω : F}
    (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (C : Fin K → Polynomial F) (α : F) (hα : α ∉ badAlphas C ω n)
    (hdvd : zH F n ∣ aggregate α C) : ∀ k, zH F n ∣ C k := by
  intro k
  rw [zH_dvd_iff hω hn]
  intro i hi
  -- `α` is good at row `i`.
  have hnotbad : α ∉ SZ.badComb fun d => (C d).eval (ω ^ i) := fun hmem =>
    hα (Finset.mem_biUnion.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, hmem⟩)
  -- The aggregate vanishes at `ω^i`, i.e. the row combination is zero.
  have hagg : (aggregate α C).eval (ω ^ i) = 0 := (zH_dvd_iff hω hn _).mp hdvd i hi
  have hsum : ∑ d : Fin K, α ^ (d : ℕ) * (C d).eval (ω ^ i) = 0 := by
    rw [← hagg]
    unfold aggregate
    rw [Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Polynomial.eval_smul, smul_eq_mul]
  exact SZ.eq_zero_of_comb_eq_zero (fun d => (C d).eval (ω ^ i)) α hnotbad hsum k

/-! ## The ζ-axis: single-challenge pinning of a claimed quotient -/

open Classical in
/-- Bad ζ for a claimed quotient: the roots of `C − t·zH` when they differ. EMPTY when they
agree, so the hypothesis stays satisfiable. -/
noncomputable def badZetas (C t : Polynomial F) (n : ℕ) : Finset F :=
  if C = t * zH F n then ∅ else (C - t * zH F n).roots.toFinset

/-- **Counting SZ, ζ-axis**: at most `D` bad ζ, when both `C` and `t·zH` have degree `≤ D`.
The agreeing case is the empty set; otherwise the bad set is the distinct roots of the
nonzero polynomial `C − t·zH`, whose degree is `≤ D`. The degree hypotheses exist ONLY for
this cardinality bound, not for the implication `zH_dvd_of_eval`. -/
theorem card_badZetas_le (C t : Polynomial F) {n D : ℕ}
    (hC : C.natDegree ≤ D) (ht : (t * zH F n).natDegree ≤ D) :
    (badZetas C t n).card ≤ D := by
  unfold badZetas
  split_ifs with h
  · simp
  · refine le_trans (Multiset.toFinset_card_le _) ?_
    refine le_trans (Polynomial.card_roots' _) ?_
    exact le_trans (Polynomial.natDegree_sub_le C (t * zH F n)) (max_le hC ht)

/-- **Single good ζ pins the quotient**: a challenge ζ outside `badZetas C t n` at which
`C` and `t·zH` agree forces `C = t·zH`, hence `zH ∣ C`. -/
theorem zH_dvd_of_eval {n : ℕ} (C t : Polynomial F) (ζ : F)
    (hζ : ζ ∉ badZetas C t n)
    (h : C.eval ζ = (t * zH F n).eval ζ) : zH F n ∣ C := by
  have : C = t * zH F n := by
    by_contra hCT
    apply hζ
    unfold badZetas
    rw [if_neg hCT, Multiset.mem_toFinset, Polynomial.mem_roots']
    exact ⟨sub_ne_zero.mpr hCT, by rw [IsRoot.def, eval_sub, sub_eq_zero]; exact h⟩
  rw [this]; exact dvd_mul_left _ _

/-- **`dvd_of_evalCheck`, single-challenge form.** One α, one ζ, ONE quotient `t`. A good ζ
outside `badZetas (aggregate α C) t n` at which the aggregate agrees with `t · Z_H` pins
`aggregate α C = t · Z_H` via `zH_dvd_of_eval`, and `dvd_separation` separates across
the constraint indices. -/
theorem dvd_of_evalCheck {K n : ℕ} [NeZero n] {ω : F} (hω : IsPrimitiveRoot ω n)
    (C : Fin K → Polynomial F)
    (α : F) (hα : α ∉ badAlphas C ω n)
    (t : Polynomial F)
    (ζ : F) (hζ : ζ ∉ badZetas (aggregate α C) t n)
    (hcheck : (aggregate α C).eval ζ = (t * zH F n).eval ζ) :
    ∀ k, zH F n ∣ C k :=
  dvd_separation hω (Nat.pos_of_ne_zero (NeZero.ne n)) C α hα
    (zH_dvd_of_eval (aggregate α C) t ζ hζ hcheck)

end Kimchi.Quotient
