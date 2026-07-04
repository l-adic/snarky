import Kimchi.Quotient.Domain

/-!
# ζ-pinning: evaluations at enough distinct points force the identity

This file records the elementary pigeonhole fact underlying kimchi's ζ-evaluation check: a
polynomial identity that is only **verified** at a finite set of evaluation nodes is forced to
hold **as polynomials**, provided there are strictly more evaluation points than the degree
bound. There is no probabilistic content here — the "enough distinct challenges" premise is an
ordinary injectivity hypothesis on the evaluation nodes `ζ : Fin N → F`.

It is **commitment-free**: everything lives over an abstract field `[Field F]`; there is no
group, no SRS, no Fiat–Shamir. The source of truth for the *shape* of the argument is kimchi's
quotient check, but the mathematics is standard.

## Contents

* `identity_of_evals` — degree-`≤ D` polynomials agreeing at `N > D` distinct nodes are equal.
* `zH_dvd_of_evals` — the divisibility corollary: agreeing with a multiple of `Z_H` at enough
  distinct nodes forces `Z_H ∣ C`.

The single engine is the too-many-roots lemma
(`Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`): a polynomial of degree `< N` that
vanishes at `N` distinct points is zero. All degree accounting is kept abstract through a single
bound `D`; nothing kimchi-specific about concrete degrees appears here.
-/

namespace Kimchi.Quotient

open Polynomial

variable {F : Type*} [Field F] {n N : ℕ} {ω : F}

/-! ## Pinning an identity from its evaluations -/

/-- **Identity from enough evaluations.** Let `ζ : Fin N → F` be injective, `C, T ∈ F[X]` and
`D : ℕ` with `deg C ≤ D`, `deg T ≤ D` and `D < N`. If `C(ζ s) = T(ζ s)` for every
`s : Fin N`, then `C = T`. The difference `C - T` has degree `≤ D < N` yet vanishes at `N`
distinct points, so
by the too-many-roots lemma it is the zero polynomial. -/
theorem identity_of_evals (ζ : Fin N → F) (C T : Polynomial F) (hζ : Function.Injective ζ)
    (D : ℕ) (hC : C.natDegree ≤ D) (hT : T.natDegree ≤ D) (hD : D < N)
    (h : ∀ s : Fin N, C.eval (ζ s) = T.eval (ζ s)) : C = T := by
  have hsub : C - T = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (C - T) hζ
    · intro s
      rw [eval_sub, sub_eq_zero]
      exact h s
    · rw [Fintype.card_fin]
      exact lt_of_le_of_lt (le_trans (natDegree_sub_le C T) (max_le hC hT)) hD
  exact sub_eq_zero.mp hsub

/-! ## The divisibility corollary -/

/-- **Divisibility from enough evaluations.** Instantiating `T = t · Z_H` in
`identity_of_evals` turns the pinning statement into the divisibility conclusion the quotient
argument consumes: if `C` agrees with a multiple of the vanishing polynomial at enough distinct
points, then `C` is itself divisible by `Z_H`. -/
theorem zH_dvd_of_evals (hω : IsPrimitiveRoot ω n) (hn : 0 < n) (ζ : Fin N → F)
    (hζ : Function.Injective ζ) (C t : Polynomial F) (D : ℕ) (hC : C.natDegree ≤ D)
    (ht : (t * zH F n).natDegree ≤ D) (hD : D < N)
    (h : ∀ s : Fin N, C.eval (ζ s) = (t * zH F n).eval (ζ s)) : zH F n ∣ C := by
  have heq : C = t * zH F n := identity_of_evals ζ C (t * zH F n) hζ D hC ht hD h
  rw [heq]
  exact dvd_mul_left (zH F n) t

end Kimchi.Quotient
