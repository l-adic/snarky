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
Mathlib curve and `pasta/Pasta/Basic.lean` discharges the two `Fact`s (the short-shape one by
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

omit [DecidableEq F] in
/-- The prime-order hypothesis as a `Fact`-backed accessor — reads like a field (`c.order_prime`)
    and threads through the development by instance inference. -/
lemma order_prime (W : Affine F) [Fact (Nat.Prime W.order)] : Nat.Prime W.order := Fact.out

omit [DecidableEq F] in
/-- The short-Weierstrass coefficients `a₁ = a₂ = a₃ = 0` as a `Fact`-backed accessor
    (`c.short`). This is *all* VarBaseMul needs (no `a₄ = 0`), and every CompElliptic `SWCurve`
    satisfies it by `rfl` — so at a concrete `toW` curve the `Fact` is discharged by
    `⟨rfl, rfl, rfl⟩`, never an assumption. -/
lemma short (W : Affine F) [Fact (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)] :
    W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 := Fact.out

end WeierstrassCurve.Affine

namespace CompElliptic.CurveForms.ShortWeierstrass

variable {F : Type*} [Field F]

/-- The `SWCurve` as a Mathlib affine Weierstrass curve `y² = x³ + A·x + B`. -/
abbrev SWCurve.toAffine (C : SWCurve F) : WeierstrassCurve.Affine F := toW C.A C.B

end CompElliptic.CurveForms.ShortWeierstrass
