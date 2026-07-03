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

/-- The prime-order hypothesis as a `Fact`-backed accessor — reads like a field (`c.order_prime`)
    and threads through the development by instance inference. -/
lemma order_prime (W : Affine F) [Fact (Nat.Prime W.order)] : Nat.Prime W.order := Fact.out

/-- The short-Weierstrass coefficients `a₁ = a₂ = a₃ = 0` as a `Fact`-backed accessor
    (`c.short`). This is *all* VarBaseMul needs (no `a₄ = 0`), and every CompElliptic `SWCurve`
    satisfies it by `rfl` — so at a concrete `toW` curve the `Fact` is discharged by
    `⟨rfl, rfl, rfl⟩`, never an assumption. -/
lemma short (W : Affine F) [Fact (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)] :
    W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 := Fact.out

end WeierstrassCurve.Affine

namespace CompElliptic.CurveForms.ShortWeierstrass

variable {F : Type*} [Field F] [DecidableEq F]

/-- The `SWCurve` as a Mathlib affine Weierstrass curve `y² = x³ + A·x + B`. -/
abbrev SWCurve.toAffine (C : SWCurve F) : WeierstrassCurve.Affine F := toW C.A C.B

/-- The Mathlib point group of the curve (with Mathlib's proven `AddCommGroup`; the
    `IsElliptic` instance it needs comes from `instIsElliptic`). -/
abbrev SWCurve.Pt (C : SWCurve F) : Type _ := C.toAffine.Point

end CompElliptic.CurveForms.ShortWeierstrass
