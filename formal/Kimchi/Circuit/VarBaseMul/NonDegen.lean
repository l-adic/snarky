import Kimchi.Curve
import Kimchi.Gate.VarBaseMul

/-!
# Group-order non-degeneracy toolkit

The two field side conditions the VarBaseMul gate's incomplete additions need, established from
the group structure of a `short-Weierstrass curve`:

* `x_ne_xT_of_ne_base` — a point that is neither `T` nor `−T` has a different `x`-coordinate
  (the non-vertical condition for the first addition), built on `smul_ne_zero_of_lt` (with prime
  `order`, a nonzero point times a scalar strictly between `0` and `order` is nonzero);
* `tne_of_holds` — the gate constraints together with prime `order` already force the
  second-addition condition `t = 2·xi + xb − s1² ≠ 0`, with no exclusion set.
-/

namespace Kimchi.Circuit.VarBaseMul

open Kimchi.Gate.VarBaseMul WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Core non-degeneracy.** With prime `order`, a nonzero point times a scalar strictly
    between `0` and `order` is nonzero. -/
lemma smul_ne_zero_of_lt (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] {T : c.Point} (hT : T ≠ 0)
    {k : ℤ} (h0 : 0 < k) (hlt : k < (c.order : ℤ)) : k • T ≠ 0 := by
  intro h_contra
  -- prime `order` together with `0 < k < order` forces `gcd k order = 1`
  have h_coprime : Int.gcd k (c.order : ℤ) = 1 := by
    refine Nat.coprime_comm.mp (c.order_prime.coprime_iff_not_dvd.mpr fun hd => ?_)
    have := Int.le_of_dvd (by positivity) (Int.natCast_dvd.mpr hd)
    omega
  -- Bézout: `k * a + order * b = 1`
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, k * a + (c.order : ℤ) * b = 1 := by
    have h := Int.gcd_eq_gcd_ab k (c.order : ℤ)
    exact ⟨_, _, h.symm.trans (by rw [h_coprime]; simp)⟩
  -- hence `T = a • (k • T) + b • (order • T)`, and both terms vanish
  have h_decomp : T = a • (k • T) + b • ((c.order : ℤ) • T) := by
    rw [← mul_smul, ← mul_smul, ← add_smul, mul_comm a k, mul_comm b (c.order : ℤ), hab,
      one_zsmul]
  rw [h_contra, c.order_smul, smul_zero, smul_zero, add_zero] at h_decomp
  exact hT h_decomp

/-- **x-coordinate bridge.** On a short-Weierstrass curve, a point that is neither `T`
    nor `−T` has a different `x`-coordinate. -/
lemma x_ne_xT_of_ne_base (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] {x y xT yT : F}
    (h : c.Nonsingular x y) (hT : c.Nonsingular xT yT)
    (hne : Point.some _ _ h ≠ Point.some _ _ hT) (hneg : Point.some _ _ h ≠ -Point.some _ _ hT) :
    x ≠ xT := by
  contrapose! hneg
  contrapose! hne
  simp_all +decide [WeierstrassCurve.Affine.negY]
  have h_eq : y ^ 2 + c.a₁ * xT * y + c.a₃ * y
      = yT ^ 2 + c.a₁ * xT * yT + c.a₃ * yT := by
    have := h.1; have := hT.1
    simp_all +decide [WeierstrassCurve.Affine.equation_iff]
  exact mul_left_cancel₀ (sub_ne_zero_of_ne hne) (by linear_combination h_eq)

/-- **t-condition self-enforcement.** The gate constraints together with prime order
    already force `t ≠ 0` — the forbidden check is NOT needed for the second-addition
    non-degeneracy. If `t = 2·xi + xb − s1² = 0`, then the `xo` constraint
    `u² − t²·(…) = 0` collapses to `u² = 0`, i.e. `u = 2·yi − t·s1 = 2·yi = 0`, so
    `yi = 0`. But a nonsingular affine point with `yi = 0` equals its own negation
    (short Weierstrass), hence is 2-torsion; on a group of odd prime `order` there is no
    such point. Contradiction.

    The hypothesis `c.order ≠ 2` (equivalently, the prime `order` is odd) is genuinely
    required, not a convenience: for `order = 2` the statement is false. E.g. over
    `ZMod 7` with the curve `y² = x³ + 6` (group `(ℤ/2)²`, so `order = 2`), the input
    point `(xi, yi) = (1, 0)` is nonsingular and `singleBitHolds 0 5 0 0 1 0 0 0` holds,
    yet `2·xi + xb − s1² = 2·1 + 5 − 0 = 7 = 0`. The Pasta `order` is a 255-bit prime,
    so `order ≠ 2` there. But `order ≠ 2` does not follow from `order` being prime (`2`
    is prime) or from the short shape, so it is taken as a separate hypothesis. -/
lemma tne_of_holds (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    {b xb yb s1 xi yi xo yo : F}
    (hI : c.Nonsingular xi yi)
    (hh : singleBitHolds b xb yb s1 xi yi xo yo) :
    2 * xi + xb - s1 * s1 ≠ 0 := by
  intro ht
  -- Step 1: the `xo` constraint collapses (with `t = 0`) to `4·yi² = 0`, so `yi = 0`.
  have hyi : yi = 0 := by
    simp only [singleBitHolds] at hh
    obtain ⟨_, _, h3, _⟩ := hh
    have htt : xi - (s1 * s1 - xi - xb) = 0 := by linear_combination ht
    rw [htt] at h3
    have hy2 : yi * yi = 0 := by
      have hfour : (4 : F) * (yi * yi) = 0 := by linear_combination h3
      have h4ne : (4 : F) ≠ 0 := by
        have h44 : (4 : F) = 2 * 2 := by norm_num
        rw [h44]; exact mul_ne_zero h2 h2
      exact (mul_eq_zero.mp hfour).resolve_left h4ne
    exact mul_self_eq_zero.mp hy2
  -- Step 2: with `yi = 0` (and short shape `a₁ = a₃ = 0`), `negY = yi`, so `P = -P`.
  obtain ⟨ha1, -, ha3⟩ := c.short
  have hneg : negY c xi yi = yi := by
    simp [WeierstrassCurve.Affine.negY, ha1, ha3, hyi]
  have hPselfneg : -(Point.some _ _ hI) = Point.some _ _ hI := by
    rw [Point.neg_some]; congr 1
  -- Step 3: `P = -P` gives `2 • P = P + (-P) = 0`.
  have hPne : Point.some _ _ hI ≠ 0 := Point.some_ne_zero hI
  have h2P : (2 : ℤ) • Point.some _ _ hI = 0 := by
    rw [two_zsmul]; nth_rewrite 2 [← hPselfneg]; rw [add_neg_cancel]
  -- Step 4: `0 < 2 < order` (prime, `≠ 2`) contradicts `2 • P = 0` for `P ≠ 0`.
  have hlt : (2 : ℤ) < (c.order : ℤ) := by
    have : 3 ≤ c.order := by have := c.order_prime.two_le; omega
    exact_mod_cast this
  exact smul_ne_zero_of_lt c hPne (by norm_num) hlt h2P

end Kimchi.Circuit.VarBaseMul
