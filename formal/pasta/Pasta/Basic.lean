import Pasta.Curve
import CompElliptic.Curves.Pasta
import CompElliptic.Curves.PastaOrder
import CompElliptic.Fields.Pasta

/-!
# The Pasta curves' group orders

The Pallas group order is the prime `q = PALLAS_SCALAR_CARD` and the Vesta group order is the
prime `p = PALLAS_BASE_CARD` (the Pasta cycle: each curve's order is the other's base-field
size). Both are `CompElliptic.Curves.PastaOrder.card_eq`, which is **unconditional**: the
elementary fibre bound `#E(𝔽) ≤ 2·#𝔽 + 1` plus the `native_decide` prime-order witness
`[order]·G = 𝒪` pin the order outright (Vesta's leftover `#E = 2p` case is excluded because
`-5` is not a cube). No Hasse bound, no axioms — this file only transports the counts to the
Mathlib-`Point` reading and packages primality as `Fact` instances.
-/

namespace Pasta

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta CompElliptic.CurveForms.ShortWeierstrass
  CompElliptic.CurveOrder

/-- The Pallas group order is the prime scalar-field cardinality `q` — the unconditional
    `card_eq`, read through the `SWPoint ≃ Point` bridge. -/
theorem pallas_card : Pallas.curve.toAffine.order = PALLAS_SCALAR_CARD := by
  have h := Pallas.card_eq
  rw [SWPoint.card_eq_point Pallas.curve] at h
  exact h

/-- The Vesta group order is the prime cardinality `p`. -/
theorem vesta_card : Vesta.curve.toAffine.order = PALLAS_BASE_CARD := by
  have h := Vesta.card_eq
  rw [SWPoint.card_eq_point Vesta.curve] at h
  exact h

/-- **The Pasta fields' size in bits.** Both base-field cardinals are 255-bit. This is the one
    place the width is written down — it is the circuit's `FieldSizeInBits`, the bound on
    `bitsUsed = 5·m`, and `pastaFieldBits - 1` is `scaleFast2`'s `s_div_2_bits` range-check width.
    Everything downstream refers to this name rather than a bare `255`/`254`. -/
abbrev pastaFieldBits : ℕ := 255

/-- The register range-check bound: `2^(pastaFieldBits-1) ≤ PALLAS_BASE_CARD` (`scaleFast2`). -/
lemma two_pow_le_pallas_base : 2 ^ (pastaFieldBits - 1) ≤ PALLAS_BASE_CARD := by
  norm_num [PALLAS_BASE_CARD]

/-- The Pallas group order is prime — the point count plus `PALLAS_SCALAR_is_prime`. -/
theorem pallas_order_prime : Nat.Prime Pallas.curve.toAffine.order := by
  rw [pallas_card]; exact PALLAS_SCALAR_is_prime

/-- The Vesta group order is prime — the point count plus `PALLAS_BASE_is_prime`. -/
theorem vesta_order_prime : Nat.Prime Vesta.curve.toAffine.order := by
  rw [vesta_card]; exact PALLAS_BASE_is_prime

/-- `order_prime` for Pallas as the auto-threading `Fact` the soundness theorems consume. -/
instance : Fact (Nat.Prime Pallas.curve.toAffine.order) := ⟨pallas_order_prime⟩

/-- `order_prime` for Vesta likewise. -/
instance : Fact (Nat.Prime Vesta.curve.toAffine.order) := ⟨vesta_order_prime⟩

/-- The short-Weierstrass `Fact` the VarBaseMul soundness consumes — `a₁=a₂=a₃=0`, which every
    `toW` curve satisfies by `rfl` (no `a₄=0`/`A=0` needed). -/
instance : Fact (Pallas.curve.toAffine.a₁ = 0 ∧ Pallas.curve.toAffine.a₂ = 0 ∧
    Pallas.curve.toAffine.a₃ = 0) := ⟨⟨rfl, rfl, rfl⟩⟩

/-- The short-Weierstrass `Fact` for Vesta likewise. -/
instance : Fact (Vesta.curve.toAffine.a₁ = 0 ∧ Vesta.curve.toAffine.a₂ = 0 ∧
    Vesta.curve.toAffine.a₃ = 0) := ⟨⟨rfl, rfl, rfl⟩⟩

end Pasta
