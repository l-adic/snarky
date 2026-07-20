import Mathlib

/-!
# Evaluation domain and vanishing–divisibility

This file is the **polynomial-algebra substrate** of kimchi's quotient/vanishing argument.
It is **commitment-free**: everything lives over an abstract field `[Field F]`, with a
primitive `n`-th root of unity supplied as a hypothesis (`ω : F`,
`hω : IsPrimitiveRoot ω n`, together with `0 < n`). There is no group, no SRS, no
Fiat–Shamir. The Pasta instantiation (constructing `ω` for a concrete field) is out of scope.

The evaluation domain is the finite set
`H = {ω^0, ω^1, …, ω^(n-1)} ⊆ F`, kimchi's domain `d1` of size `n`. Only `d1` is modelled;
the FFT working domains `d4`/`d8` are prover-side and out of scope.

Source: kimchi `domains.rs` (`EvaluationDomains::d1`, the size-`n` radix-2 domain).

## Contents

* `zH` — the vanishing polynomial `X^n - 1`.
* `zH_eq_prod` — its cyclotomic factorization `∏_{i<n} (X - ω^i)`.
* `zH_dvd_iff` — `Z_H ∣ E ↔ E` vanishes on the whole domain.
* `columnPoly` — the degree-`<n` Lagrange interpolant of a column `v : Fin n → F`.
* `eval_columnPoly` — the interpolant reproduces its column on `H`.
* `eq_of_eval_eq_on_domain` — uniqueness of degree-`<n` interpolants.
* `columnPoly_eval_self` — a degree-`<n` polynomial is the interpolant of its own node
  values (the commitment-world ↔ table-world seam).
-/

namespace Kimchi

open Polynomial

variable {F : Type*} [Field F] {n : ℕ} {ω : F}

/-! ## The vanishing polynomial -/

/-- The vanishing polynomial of the size-`n` domain: `Z_H = X^n - 1 ∈ F[X]`. -/
noncomputable def zH (F : Type*) [Field F] (n : ℕ) : Polynomial F := X ^ n - 1

/-- **Factorization of `Z_H`.** For a primitive `n`-th root of unity `ω` with `0 < n`,
`Z_H = ∏_{i<n} (X - ω^i)`. -/
private theorem zH_eq_prod (hω : IsPrimitiveRoot ω n) (hn : 0 < n) :
    zH F n = ∏ i ∈ Finset.range n, (X - C (ω ^ i)) := by
  unfold zH
  rw [← C_1, X_pow_sub_C_eq_prod hω hn (one_pow n)]
  simp only [mul_one]

/-! ## Vanishing ⟺ divisibility -/

/-- **`Z_H` divides `E` iff `E` vanishes on the domain.** Under a primitive-root hypothesis
and `0 < n`, `Z_H ∣ E ↔ ∀ i < n, E(ω^i) = 0`. -/
theorem zH_dvd_iff (hω : IsPrimitiveRoot ω n) (hn : 0 < n) (E : Polynomial F) :
    zH F n ∣ E ↔ ∀ i < n, E.eval (ω ^ i) = 0 := by
  constructor
  · rintro ⟨q, rfl⟩ i hi
    simp only [zH, eval_mul, eval_sub, eval_pow, eval_X, eval_one]
    have hpow : (ω ^ i) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    rw [hpow]
    ring
  · intro h
    rw [zH_eq_prod hω hn]
    apply Finset.prod_dvd_of_coprime
    · intro i hi j hj hij
      simp only [Function.onFun]
      apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      rw [isUnit_iff_ne_zero, sub_ne_zero]
      intro heq
      exact hij (hω.injOn_pow hi hj heq)
    · intro i hi
      rw [Polynomial.dvd_iff_isRoot]
      exact h i (Finset.mem_range.mp hi)

/-! ## Column interpolants -/

/-- The interpolant of a column `v : Fin n → F` through the domain nodes `i ↦ ω^i`:
`columnPoly v = Lagrange.interpolate univ (fun i => ω^i) v ∈ F[X]`. -/
noncomputable def columnPoly (ω : F) (v : Fin n → F) : Polynomial F :=
  Lagrange.interpolate Finset.univ (fun i : Fin n => ω ^ (i : ℕ)) v

/-- **The column polynomial reproduces its column on the domain.** For a primitive-root `ω`
and every `v : Fin n → F`, `(columnPoly v)(ω^i) = v i`. -/
theorem eval_columnPoly (hω : IsPrimitiveRoot ω n) (v : Fin n → F) (i : Fin n) :
    (columnPoly ω v).eval (ω ^ (i : ℕ)) = v i := by
  have hinj : Set.InjOn (fun j : Fin n => ω ^ (j : ℕ)) ↑(Finset.univ : Finset (Fin n)) := by
    intro a _ b _ heq
    apply Fin.val_injective
    exact hω.injOn_pow (Finset.mem_range.mpr a.isLt) (Finset.mem_range.mpr b.isLt) heq
  exact Lagrange.eval_interpolate_at_node v hinj (Finset.mem_univ i)

/-- The column polynomial has degree `< n`. -/
theorem degree_columnPoly_lt (hω : IsPrimitiveRoot ω n) (v : Fin n → F) :
    (columnPoly ω v).degree < n := by
  have hinj : Set.InjOn (fun j : Fin n => ω ^ (j : ℕ)) ↑(Finset.univ : Finset (Fin n)) := by
    intro a _ b _ heq
    apply Fin.val_injective
    exact hω.injOn_pow (Finset.mem_range.mpr a.isLt) (Finset.mem_range.mpr b.isLt) heq
  simpa [columnPoly, Finset.card_univ] using
    Lagrange.degree_interpolate_lt (v := fun j : Fin n => ω ^ (j : ℕ)) hinj (r := v)

/-- **Uniqueness of degree-`<n` interpolants.** Two polynomials of degree `< n` that agree on
the whole domain are equal. -/
theorem eq_of_eval_eq_on_domain (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    {p q : Polynomial F} (hp : p.degree < n) (hq : q.degree < n)
    (h : ∀ i < n, p.eval (ω ^ i) = q.eval (ω ^ i)) : p = q := by
  rw [← sub_eq_zero]
  apply Polynomial.eq_zero_of_dvd_of_degree_lt (p := zH F n)
  · rw [zH_dvd_iff hω hn]
    intro i hi
    rw [eval_sub, sub_eq_zero]
    exact h i hi
  · have hdeg : (zH F n).degree = n := by
      rw [zH, ← C_1, degree_X_pow_sub_C hn]
    rw [hdeg]
    exact lt_of_le_of_lt (degree_sub_le p q) (max_lt hp hq)

/-- **A low-degree polynomial is the interpolant of its own node values.** The seam
between the commitment world and the table world: a commitment binds a *polynomial*,
satisfiability judges a *table*, and for degree `< n` the two determine each other —
the column read off a bound polynomial interpolates back to that polynomial. The
degree hypothesis is the protocol's own chunk/degree discipline: without it a bound
polynomial could agree with a table on every node yet differ off the domain, where
the verifier's equation constrains it. -/
theorem columnPoly_eval_self (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (p : Polynomial F) (hdeg : p.natDegree < n) :
    columnPoly ω (fun j : Fin n => p.eval (ω ^ (j : ℕ))) = p := by
  refine eq_of_eval_eq_on_domain hω hn (degree_columnPoly_lt hω _)
    (lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hdeg)) ?_
  intro i hi
  rw [show ((ω : F) ^ i) = ω ^ ((⟨i, hi⟩ : Fin n) : ℕ) from rfl, eval_columnPoly hω]

end Kimchi
