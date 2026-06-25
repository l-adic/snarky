import Kimchi.Cycle.Axioms
import Kimchi.Gate.VarBaseMul

/-!
# Group-order non-degeneracy toolkit

In the point group of a `CMCurve`, the `order` is prime, so a nonzero point times a
scalar strictly between `0` and `order` is itself nonzero. Hence a multiple `k • T` of a
nonzero point `T`, with `k` strictly between `1` and `order − 1`, is neither `T` nor `−T`,
and (on a short-Weierstrass curve) has a different `x`-coordinate than `T`.

These are standalone library lemmas — the mathematical core of "the partial accumulators
stay away from `±T`" — to be wired into the per-row accumulators in a later step.
-/

namespace Kimchi.Cycle

open Kimchi.Gate.VarBaseMul WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Core non-degeneracy.** With prime `order`, a nonzero point times a scalar strictly
    between `0` and `order` is nonzero. -/
lemma smul_ne_zero_of_lt (c : CMCurve F) {T : c.W.Point} (hT : T ≠ 0)
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

/-- A nonzero point times a scalar strictly between `1` and `order − 1` is neither `T`
    nor `−T`. -/
lemma smul_ne_base (c : CMCurve F) {T : c.W.Point} (hT : T ≠ 0)
    {k : ℤ} (h1 : 1 < k) (h2 : k + 1 < (c.order : ℤ)) :
    k • T ≠ T ∧ k • T ≠ -T := by
  refine ⟨?_, ?_⟩
  · intro h_contra
    have h_eq : (k - 1) • T = 0 := by
      rw [sub_smul, one_zsmul, h_contra, sub_self]
    exact smul_ne_zero_of_lt c hT (by linarith) (by linarith) h_eq
  · intro h_contra
    have h_eq : (k + 1) • T = 0 := by
      rw [add_zsmul, one_zsmul, h_contra, neg_add_cancel]
    exact smul_ne_zero_of_lt c hT (by linarith) (by linarith) h_eq

/-- **x-coordinate bridge.** On a short-Weierstrass curve, a point that is neither `T`
    nor `−T` has a different `x`-coordinate. -/
lemma x_ne_xT_of_ne_base (c : CMCurve F) {x y xT yT : F}
    (h : c.W.Nonsingular x y) (hT : c.W.Nonsingular xT yT)
    (hne : Point.some h ≠ Point.some hT) (hneg : Point.some h ≠ -Point.some hT) :
    x ≠ xT := by
  contrapose! hneg
  contrapose! hne
  simp_all +decide [WeierstrassCurve.Affine.negY]
  have h_eq : y ^ 2 + c.W.a₁ * xT * y + c.W.a₃ * y
      = yT ^ 2 + c.W.a₁ * xT * yT + c.W.a₃ * yT := by
    have := h.1; have := hT.1
    simp_all +decide [WeierstrassCurve.Affine.equation_iff]
  exact mul_left_cancel₀ (sub_ne_zero_of_ne hne) (by linear_combination h_eq)

/-- **Second-addition non-vertical guarantee.** The geometric non-degeneracy
    `2·I + Q ≠ 0` forces the field condition `tⱼ = 2·xi + xb − s1² ≠ 0` that the
    `VarBaseMul` gate bundles. -/
lemma singleBit_tne_of_double_ne (c : CMCurve F)
    {b xb yb s1 xi yi xo yo : F}
    (hI : c.W.Nonsingular xi yi)
    (hQ : c.W.Nonsingular xb ((2 * b - 1) * yb))
    (hxne : xi ≠ xb)
    (h : singleBitHolds b xb yb s1 xi yi xo yo)
    (hdbl : (2 : ℤ) • Point.some hI + Point.some hQ ≠ 0) :
    2 * xi + xb - s1 * s1 ≠ 0 := by
  contrapose! hdbl
  -- the first addition `I + Q` is the secant point `R = (rx, ry)` with slope `s1`
  have hR : ∃ hR : c.W.Nonsingular (s1 * s1 - xi - xb)
      (s1 * (xi - (s1 * s1 - xi - xb)) - yi),
      Point.some hI + Point.some hQ = Point.some hR := by
    apply secant_add c.W c.short hI hQ hxne (l := s1)
    · rw [eq_div_iff (sub_ne_zero_of_ne hxne)]
      linear_combination' h.2.1
    · rfl
    · rfl
  grind +suggestions

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
    so `order ≠ 2` there; it is not derivable from the abstract `CMCurve` axioms alone
    (`beta = lam = 1` satisfies them in the counterexample), hence it is assumed. -/
lemma tne_of_holds (c : CMCurve F) (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    {b xb yb s1 xi yi xo yo : F}
    (hI : c.W.Nonsingular xi yi)
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
  obtain ⟨ha1, -, ha3, -⟩ := c.short
  have hneg : negY c.W xi yi = yi := by
    simp [WeierstrassCurve.Affine.negY, ha1, ha3, hyi]
  have hPselfneg : -(Point.some hI) = Point.some hI := by
    rw [Point.neg_some]; congr 1
  -- Step 3: `P = -P` gives `2 • P = P + (-P) = 0`.
  have hPne : Point.some hI ≠ 0 := Point.some_ne_zero hI
  have h2P : (2 : ℤ) • Point.some hI = 0 := by
    rw [two_zsmul]; nth_rewrite 2 [← hPselfneg]; rw [add_neg_cancel]
  -- Step 4: `0 < 2 < order` (prime, `≠ 2`) contradicts `2 • P = 0` for `P ≠ 0`.
  have hlt : (2 : ℤ) < (c.order : ℤ) := by
    have : 3 ≤ c.order := by have := c.order_prime.two_le; omega
    exact_mod_cast this
  exact smul_ne_zero_of_lt c hPne (by norm_num) hlt h2P

end Kimchi.Cycle
