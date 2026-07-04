import Mathlib
import CompElliptic.CurveForms.ShortWeierstrass

/-!
# Curve-order sugar

The VarBaseMul soundness is proved abstractly over a Mathlib affine curve `c : Affine F` — kept
*abstract* so its coefficients stay opaque (a concrete `toW` literal would reduce `a₁,a₃` to `0`
inconsistently and break `ring`/`linear_combination`). For such a curve we need three things,
supplied as auto-threading `Fact`s plus one theorem:

* `c.order` — the group order `#E(F)` (`Nat.card c.Point`);
* `c.order_smul` — that the order annihilates every point, proved from
  `card_nsmul_eq_zero'`: it holds for any group, with no finiteness needed (an infinite
  group has `Nat.card = 0`).
* `[Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]` and `[Fact (Nat.Prime c.order)]` — the
  short-Weierstrass and prime-order hypotheses, as instances so they thread through the
  development by inference. The short-shape condition is the bare conjunction `a₁=a₂=a₃=0`
  (all VarBaseMul needs; `a₄` is free).

The concrete CompElliptic `SWCurve` enters only at instantiation: `C.toAffine` realizes it as a
Mathlib curve and `Kimchi/Pasta.lean` discharges the two `Fact`s (the short-shape one by
`⟨rfl, rfl, rfl⟩`, since every `toW` curve has `a₁=a₂=a₃=0`).
-/

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]

/-- The group order `#E(F)`. -/
noncomputable def order (W : Affine F) : ℕ := Nat.card W.Point

/-- The order annihilates every point: `(order : ℤ) • P = 0`, from `card_nsmul_eq_zero'`.
    Holds for any group with no finiteness hypothesis (an infinite group has
    `Nat.card = 0`). -/
lemma order_smul (W : Affine F) (P : W.Point) : (W.order : ℤ) • P = 0 := by
  rw [natCast_zsmul]; exact card_nsmul_eq_zero'

/-- `[n]·P` reduces its scalar modulo the group order: `(n % order) • P = n • P` — the bridge
    from integer scalars to the finite scalar group. Immediate from `order_smul`. -/
lemma zsmul_mod (W : Affine F) (n : ℤ) (P : W.Point) :
    (n % (W.order : ℤ)) • P = n • P := by
  have h : n • P
      = (n % (W.order : ℤ)) • P + (W.order : ℤ) • ((n / (W.order : ℤ)) • P) := by
    rw [← mul_smul, ← add_smul, Int.emod_add_mul_ediv]
  rw [h, W.order_smul, add_zero]

/-- **Canonical scalar-field representative.** From `P = n•T` recover the unique scalar `s` in
    `[0, order)` with `P = s•T` — the genuine scalar-field element (`s ∈ ZMod order` via `Fin`),
    independent of the integer `n`'s signed-digit magnitude. The bridge a scalar-mul circuit's
    integer output crosses into the finite scalar group (and, on a 2-cycle, into the sister curve's
    base field). -/
theorem exists_canonical_scalar (W : Affine F) (P T : W.Point) (n : ℤ) (hord : 0 < W.order)
    (h : P = n • T) : ∃ s : ℤ, P = s • T ∧ 0 ≤ s ∧ s < (W.order : ℤ) := by
  have hpos : (0 : ℤ) < (W.order : ℤ) := by exact_mod_cast hord
  exact ⟨n % (W.order : ℤ), by rw [zsmul_mod]; exact h,
    Int.emod_nonneg n hpos.ne', Int.emod_lt_of_pos n hpos⟩

omit [DecidableEq F] in
/-- Points with equal coordinates are equal — congruence past the nonsingularity proof. The
    single shared home for what was re-derived privately at several use sites. -/
theorem Point.some_congr {W : Affine F} {x x' y y' : F}
    (h : W.Nonsingular x y) (h' : W.Nonsingular x' y') (hx : x = x') (hy : y = y') :
    Point.some _ _ h = Point.some _ _ h' := by subst hx; subst hy; rfl

/-- **No affine 2-torsion off the x-axis** (`a₁ = a₃ = 0`, `char ≠ 2`): a point with `y ≠ 0` is
    not its own inverse, so `P + P ≠ 0`. This is what makes a `CompleteAdd` *doubling* row's
    infinity branch refutable — the flag `inf = 0` is derivable, not an assumption. -/
theorem Point.add_self_ne_zero (W : Affine F) (ha1 : W.a₁ = 0) (ha3 : W.a₃ = 0)
    {x y : F} (h : W.Nonsingular x y) (hy : y ≠ 0) (h2 : (2 : F) ≠ 0) :
    Point.some x y h + Point.some x y h ≠ 0 := by
  intro hzero
  have hneg : Point.some x y h = -Point.some x y h := eq_neg_of_add_eq_zero_left hzero
  rw [Point.neg_some] at hneg
  have hyy : y = W.negY x y := by simpa using hneg
  rw [WeierstrassCurve.Affine.negY, ha1, ha3] at hyy
  have h2y : 2 * y = 0 := by linear_combination hyy
  exact hy ((mul_eq_zero.mp h2y).resolve_left h2)

/-- An odd-order group has no 2-torsion: `P + P = 0` forces `P = 0` (Bézout on `2` and the odd
    order, via `order_smul`). -/
theorem Point.eq_zero_of_add_self_eq_zero {W : Affine F} (hodd : Odd W.order)
    {P : W.Point} (h : P + P = 0) : P = 0 := by
  obtain ⟨t, ht⟩ := hodd
  have h2 : (2 : ℤ) • P = 0 := by rw [two_zsmul]; exact h
  calc P = (1 : ℤ) • P := (one_zsmul P).symm
    _ = ((W.order : ℤ) - 2 * t) • P := by
        congr 1
        have : (W.order : ℤ) = 2 * t + 1 := by exact_mod_cast ht
        omega
    _ = (W.order : ℤ) • P - (t : ℤ) • ((2 : ℤ) • P) := by
        rw [sub_zsmul, smul_smul, mul_comm (t : ℤ) 2, sub_eq_add_neg]
    _ = 0 := by rw [W.order_smul, h2, smul_zero, sub_zero]

/-- **No point on the x-axis of an odd-order curve** (`a₁ = a₃ = 0`): a nonsingular affine point
    with `y = 0` would be nontrivial 2-torsion. At the Pasta curves (odd prime order) this
    *derives* the ubiquitous `y ≠ 0` side conditions from nonsingularity alone. -/
theorem Point.y_ne_zero_of_odd_order {W : Affine F} (ha1 : W.a₁ = 0) (ha3 : W.a₃ = 0)
    (hodd : Odd W.order)
    {x y : F} (h : W.Nonsingular x y) : y ≠ 0 := by
  intro hy0
  have hneg : Point.some x y h = -Point.some x y h := by
    rw [Point.neg_some]
    exact Point.some_congr _ _ rfl (by rw [WeierstrassCurve.Affine.negY, ha1, ha3, hy0]; ring)
  have hzero : Point.some x y h = 0 :=
    Point.eq_zero_of_add_self_eq_zero hodd (add_eq_zero_iff_eq_neg.mpr hneg)
  exact Point.some_ne_zero h hzero

/-- The prime-order hypothesis as a `Fact`-backed accessor — reads like a field (`c.order_prime`)
    and threads through the development by instance inference. -/
lemma order_prime (W : Affine F) [Fact (Nat.Prime W.order)] : Nat.Prime W.order := Fact.out

/-- The short-Weierstrass coefficients `a₁ = a₂ = a₃ = 0` as a `Fact`-backed accessor
    (`c.short`). This is *all* VarBaseMul needs (no `a₄ = 0`), and every CompElliptic `SWCurve`
    satisfies it by `rfl` — so at a concrete `toW` curve the `Fact` is discharged by
    `⟨rfl, rfl, rfl⟩`, never an assumption. -/
lemma short (W : Affine F) [Fact (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)] :
    W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 := Fact.out

/-- All four short-Weierstrass coefficients are zero: `a₁ = a₂ = a₃ = a₄ = 0`.
    Needed by `CompleteAdd.sound`. Every CompElliptic `SWCurve` with `A = 0` satisfies this by
    `rfl`; the Pasta curves (`A = 0`, `B = 5`) have `a₄ = 0` definitionally. -/
lemma short4 (W : Affine F) [Fact (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)] :
    W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0 := Fact.out

end WeierstrassCurve.Affine

namespace CompElliptic.CurveForms.ShortWeierstrass

variable {F : Type*} [Field F] [DecidableEq F]

/-- The `SWCurve` as a Mathlib affine Weierstrass curve `y² = x³ + A·x + B`. -/
abbrev SWCurve.toAffine (C : SWCurve F) : WeierstrassCurve.Affine F := toW C.A C.B

/-- The Mathlib point group of the curve (with Mathlib's proven `AddCommGroup`; the
    `IsElliptic` instance it needs comes from `instIsElliptic`). -/
abbrev SWCurve.Pt (C : SWCurve F) : Type _ := C.toAffine.Point

end CompElliptic.CurveForms.ShortWeierstrass
