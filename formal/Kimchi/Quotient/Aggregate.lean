import Kimchi.Quotient.Domain

/-!
# α-aggregation and constraint separation

Polynomial-algebra infrastructure for kimchi's quotient
argument. It is **commitment-free**: everything lives over an abstract field `[Field F]`,
with a primitive `n`-th root of unity supplied as a hypothesis
(`hω : IsPrimitiveRoot ω n`, `0 < n`).

kimchi combines the several constraint polynomials of a circuit into a single polynomial by
taking a linear combination in consecutive powers of one challenge `α`, one power per
constraint (`references/alphas.rs`, context only). This file models that combination and
proves the **separation** property the soundness argument needs: if the aggregate is
divisible by `Z_H` for enough distinct values of `α`, then *each* individual constraint
polynomial is divisible by `Z_H`.

The "enough distinct αs" premise is an ordinary injectivity hypothesis, **not** a
Fiat–Shamir definition; the underlying mathematics is a Vandermonde / too-many-roots
separation and is standard.

## Contents

* `aggregate` — the α-aggregate `∑_c α^c • E c ∈ F[X]`.
* `dvd_separation` — divisibility of the aggregate at enough distinct challenges separates
  across the individual constraint polynomials.
-/

namespace Kimchi.Quotient

open Polynomial

variable {F : Type*} [Field F] {n k : ℕ} {ω : F}

/-! ## The aggregate polynomial -/

/-- The **α-aggregate** of a finite family of constraint polynomials `E : Fin k → F[X]`:
the linear combination `∑_{c : Fin k} α^c • E c ∈ F[X]` in consecutive powers of the
challenge `α`. -/
noncomputable def aggregate (α : F) (E : Fin k → Polynomial F) : Polynomial F :=
  ∑ c : Fin k, α ^ (c : ℕ) • E c

/-! ## Separation from enough distinct challenges -/

/-- **Divisibility separates across constraints.** If `Z_H` divides the α-aggregate for
every one of `k` distinct challenges `α s`, then `Z_H` divides each individual constraint
polynomial `E c`. Argue pointwise on the domain: at each node `ω^i` the family of scalars
`E c (ω^i)` are the coefficients of a degree-`<k` univariate that vanishes at the `k`
distinct points `α s`, hence is zero. -/
theorem dvd_separation (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (α : Fin k → F) (hα : Function.Injective α) (E : Fin k → Polynomial F)
    (h : ∀ s : Fin k, zH F n ∣ aggregate (α s) E) : ∀ c, zH F n ∣ E c := by
  intro c
  rw [zH_dvd_iff hω hn]
  intro i hi
  -- The scalar values of each constraint at the fixed domain node `ω^i`.
  set a : Fin k → F := fun c => (E c).eval (ω ^ i) with ha
  -- The Vandermonde univariate whose `c`-th coefficient is `a c`.
  set p : Polynomial F := ∑ d : Fin k, Polynomial.monomial (d : ℕ) (a d) with hp
  -- `p` vanishes at every distinct challenge `α s`.
  have hpeval : ∀ s : Fin k, p.eval (α s) = 0 := by
    intro s
    have hs := (zH_dvd_iff hω hn (aggregate (α s) E)).mp (h s) i hi
    rw [hp, eval_finsetSum]
    simp only [Polynomial.eval_monomial]
    rw [← hs]
    unfold aggregate
    rw [eval_finsetSum]
    refine Finset.sum_congr rfl ?_
    intro d _
    rw [eval_smul, smul_eq_mul]
    ring
  -- `p` has degree `< k`.
  have hdeg : p.natDegree < k := by
    apply lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _)
    rw [Finset.fold_max_lt]
    exact ⟨Fin.pos c, fun d _ => lt_of_le_of_lt (Polynomial.natDegree_monomial_le _) d.isLt⟩
  -- Hence `p = 0`.
  have hpzero : p = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hα hpeval
      (by rw [Fintype.card_fin]; exact hdeg)
  -- Reading off the `c`-th coefficient: `a c = 0`.
  have hcoeff : a c = p.coeff (c : ℕ) := by
    rw [hp, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single c]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro d _ hdc
      rw [Polynomial.coeff_monomial, if_neg]
      exact fun heq => hdc (Fin.val_injective heq)
    · intro hc; exact absurd (Finset.mem_univ c) hc
  rw [ha] at hcoeff
  simp only at hcoeff
  rw [hcoeff, hpzero, Polynomial.coeff_zero]

end Kimchi.Quotient
