import Kimchi.Curve
import CompElliptic.Curves.Pasta
import CompElliptic.Fields.Pasta

/-!
# The Pasta curves' group orders — the one trusted input

The VarBaseMul soundness is proved abstractly over an `SWCurve` with `order_prime` as a
hypothesis (axiom-free). To instantiate it at the *real* Pasta curves we need their group
orders to be prime — and that rests on the curves' point counts, which Lean cannot derive:
counting `≈2²⁵⁴` points is infeasible for `decide`/`native_decide`, and CompElliptic ships no
point-counting (Schoof etc.).

So the two point counts below are **axioms** — the same trusted status "this is the curve's
order" has in any EC formalization. They are true by the Pasta construction: a curve's scalar
field *is* `ℤ/(group order)`, and Pasta fixes Pallas' order to the prime `PALLAS_SCALAR_CARD`
(`= q`) and Vesta's to `PALLAS_BASE_CARD` (`= p`), with the reciprocity
`VestaBaseField = PallasScalarField`. Should CompElliptic (or we) later prove a point count,
these axioms simply disappear.

This is the ONLY file in the tree that declares an `axiom`; everything upstream is
`#print axioms`-clean.
-/

namespace Kimchi.Pasta

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta CompElliptic.CurveForms.ShortWeierstrass

/-- TRUSTED INPUT: the Pallas curve's group order is the prime scalar-field cardinality `q`. -/
axiom pallas_card : Pallas.curve.toAffine.order = PALLAS_SCALAR_CARD

/-- TRUSTED INPUT: the Vesta curve's group order is the prime cardinality `p`. -/
axiom vesta_card : Vesta.curve.toAffine.order = PALLAS_BASE_CARD

/-- **The Pasta fields' size in bits.** Both base-field cardinals are 255-bit:
    `2^(pastaFieldBits-1) ≤ card < 2^pastaFieldBits` (the four bound lemmas below). This is the one
    place the width is written down — it is the circuit's `FieldSizeInBits`, the bound on
    `bitsUsed = 5·m`, and `pastaFieldBits - 1` is `scaleFast2`'s `s_div_2_bits` range-check width.
    Everything downstream refers to this name rather than a bare `255`/`254`. -/
abbrev pastaFieldBits : ℕ := 255

lemma two_pow_le_pallas_base : 2 ^ (pastaFieldBits - 1) ≤ PALLAS_BASE_CARD := by
  norm_num [PALLAS_BASE_CARD]

lemma pallas_base_lt_two_pow : PALLAS_BASE_CARD < 2 ^ pastaFieldBits := by
  norm_num [PALLAS_BASE_CARD]

lemma two_pow_le_pallas_scalar : 2 ^ (pastaFieldBits - 1) ≤ PALLAS_SCALAR_CARD := by
  norm_num [PALLAS_SCALAR_CARD]

lemma pallas_scalar_lt_two_pow : PALLAS_SCALAR_CARD < 2 ^ pastaFieldBits := by
  norm_num [PALLAS_SCALAR_CARD]

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

end Kimchi.Pasta
