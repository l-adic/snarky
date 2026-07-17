import Mathlib
import CompElliptic.CurveForms.ShortWeierstrass
import CompElliptic.Curves.Pasta
import CompElliptic.Curves.PastaOrder
import CompElliptic.Fields.Pasta

/-!
# The Pasta curves' group orders and the point-group module structure

Also home to the two-declaration generic vocabulary the kimchi EC gates state their
soundness in: `c.order` (the group order `#E(F)` of a Mathlib affine curve, as a name) and
`C.toAffine` (a CompElliptic `SWCurve` realized as a Mathlib curve). The short-shape and
prime-order hypotheses thread through the abstract development as `Fact` instances,
discharged here for the concrete curves and read back with a bare `Fact.out` at use sites.

The Pallas group order is the prime `q = PALLAS_SCALAR_CARD` and the Vesta group order is the
prime `p = PALLAS_BASE_CARD` (the Pasta cycle: each curve's order is the other's base-field
size). Both are `CompElliptic.Curves.PastaOrder.card_eq`, which is **unconditional**: the
elementary fibre bound `#E(𝔽) ≤ 2·#𝔽 + 1` plus the `native_decide` prime-order witness
`[order]·G = 𝒪` pin the order outright (Vesta's leftover `#E = 2p` case is excluded because
`-5` is not a cube). No Hasse bound, no axioms — this file only transports the counts to the
Mathlib-`Point` reading and packages primality as `Fact` instances.
-/

namespace WeierstrassCurve.Affine

/-- The group order `#E(F)` — the scalar modulus every VarBaseMul/EndoMul statement
    quantifies over. -/
noncomputable def order {F : Type*} [Field F] (W : Affine F) : ℕ := Nat.card W.Point

end WeierstrassCurve.Affine

namespace CompElliptic.CurveForms.ShortWeierstrass

/-- The `SWCurve` as a Mathlib affine Weierstrass curve `y² = x³ + A·x + B`. -/
abbrev SWCurve.toAffine {F : Type*} [Field F] (C : SWCurve F) : WeierstrassCurve.Affine F :=
  toW C.A C.B

end CompElliptic.CurveForms.ShortWeierstrass

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

/-- The Pallas group order is prime — the point count plus `PALLAS_SCALAR_is_prime` — as
    the auto-threading `Fact` the soundness theorems consume (read back by `Fact.out`). -/
instance pallas_order_prime : Fact (Nat.Prime Pallas.curve.toAffine.order) :=
  ⟨by rw [pallas_card]; exact PALLAS_SCALAR_is_prime⟩

/-- The Vesta group order is prime, as the auto-threading `Fact`. -/
instance vesta_order_prime : Fact (Nat.Prime Vesta.curve.toAffine.order) :=
  ⟨by rw [vesta_card]; exact PALLAS_BASE_is_prime⟩

/-- The short-Weierstrass `Fact` the VarBaseMul soundness consumes — `a₁=a₂=a₃=0`, which every
    `toW` curve satisfies by `rfl` (no `a₄=0`/`A=0` needed). -/
instance : Fact (Pallas.curve.toAffine.a₁ = 0 ∧ Pallas.curve.toAffine.a₂ = 0 ∧
    Pallas.curve.toAffine.a₃ = 0) := ⟨⟨rfl, rfl, rfl⟩⟩

/-- The short-Weierstrass `Fact` for Vesta likewise. -/
instance : Fact (Vesta.curve.toAffine.a₁ = 0 ∧ Vesta.curve.toAffine.a₂ = 0 ∧
    Vesta.curve.toAffine.a₃ = 0) := ⟨⟨rfl, rfl, rfl⟩⟩

/-! ## The scalar action on the Pasta point groups

Each point group is a module over its scalar field: it is prime-order (the unconditional
point counts), so it is torsion at that prime and `AddCommGroup.zmodModule` equips it with
the `ZMod`-module structure. The action is definitionally the ℕ-action at the canonical
representative (`{vesta,pallas}_smul_val` — `rfl`), which is the form the executable
verifiers compute with. -/

open CompElliptic.Curves.Pasta.Vesta renaming curve → vestaCurve
open CompElliptic.Curves.Pasta.Pallas renaming curve → pallasCurve
open CompElliptic.Fields.Pasta

/-- The Vesta point group is `PALLAS_BASE_CARD`-torsion (its group order, by the unconditional
axiom), hence a module over its scalar field. The action is definitionally `z.val • _`. -/
instance vestaPointModule : Module Fp (SWPoint vestaCurve) :=
  AddCommGroup.zmodModule fun P => by
    rw [← Vesta.card_eq]
    exact card_nsmul_eq_zero'

/-- The Pallas point group is `PALLAS_SCALAR_CARD`-torsion (its group order, under the
point count), hence a module over its scalar field. -/
instance pallasPointModule : Module Fq (SWPoint pallasCurve) :=
  AddCommGroup.zmodModule fun P => by
    rw [← Pallas.card_eq]
    exact card_nsmul_eq_zero'

/-- The module action is the ℕ-action at the canonical representative — the form the
executable verifiers compute with. -/
theorem vesta_smul_val (z : Fp) (P : SWPoint vestaCurve) : z • P = z.val • P :=
  rfl

theorem pallas_smul_val (z : Fq) (P : SWPoint pallasCurve) : z • P = z.val • P :=
  rfl

end Pasta
