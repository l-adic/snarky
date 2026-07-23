import Mathlib
import CompElliptic.CurveForms.ShortWeierstrass
import CompElliptic.Curves.Pasta
import CompElliptic.Curves.PastaOrder
import CompElliptic.Fields.Pasta
import Pasta.CompElliptic

/-!
# The Pasta group orders

The Pallas group has prime order `q = PALLAS_SCALAR_CARD`; the Vesta group has prime
order `p = PALLAS_BASE_CARD` (the Pasta cycle: each curve's order is the other's
base-field size). Primality and the short-Weierstrass shape are `Fact` instances, and
each point group is a module over its scalar field.

`c.order` and `C.toAffine` are the vocabulary the kimchi EC gates are stated in.
-/

namespace WeierstrassCurve.Affine

/-- The group order `#E(F)`. -/
noncomputable def order {F : Type*} [Field F] (W : Affine F) : ℕ := Nat.card W.Point

end WeierstrassCurve.Affine

namespace CompElliptic.CurveForms.ShortWeierstrass

/-- The `SWCurve` as a Mathlib affine Weierstrass curve `y² = x³ + A·x + B`. -/
abbrev SWCurve.toAffine {F : Type*} [Field F] (C : SWCurve F) : WeierstrassCurve.Affine F :=
  toW C.A C.B

/-! ### Bridge to Mathlib's `Affine.Point`

`SWPoint E` and Mathlib's affine point group `Point (toW E.A E.B)` are two representations of
the same group: the computable structure (with `DecidableEq` / `native_decide`-friendly scalar
mul) and Mathlib's inductive `Point` with its proven `AddCommGroup`. The transport maps
`toPt` / `ofPt` are already mutually inverse on valid coordinates, so they package into an
`Equiv`. This lets the `SWPoint`-native order theory (`CompElliptic.CurveOrder`,
`Curves.PastaOrder`) transfer to `Nat.card (Point …)`, the form the `pallas_card` / `vesta_card`
orders below are stated in. Upstream CompElliptic does not carry this bridge; it lives here. -/

open WeierstrassCurve.Affine

/-- The coordinates of any Mathlib point of `toW a b` are `Valid` (on the curve, or the `𝒪`
sentinel). -/
theorem valid_ofPt {F : Type*} [Field F] {a b : F} [(toW a b).IsElliptic]
    (Q : Point (toW a b)) : Valid a b (ofPt Q) := by
  cases Q with
  | zero => exact Or.inr rfl
  | some x y h => exact Or.inl (equation_toW.mp h.left)

/-- `toPt` is a right inverse of `ofPt` (`b ≠ 0` so the `𝒪` sentinel round-trips). -/
theorem toPt_ofPt {F : Type*} [Field F] [DecidableEq F] {a b : F} (hb : b ≠ 0)
    [(toW a b).IsElliptic] (Q : Point (toW a b)) : toPt a b (ofPt Q) = Q := by
  cases Q with
  | zero => exact toPt_zero hb
  | some x y h => exact toPt_some (equation_toW.mp h.left)

/-- `SWPoint E` is equivalent to Mathlib's affine point group `Point (toW E.A E.B)`, via the
coordinate transport `toPt` / `ofPt`. -/
noncomputable def SWPoint.equivPoint {F : Type*} [Field F] [DecidableEq F] (E : SWCurve F) :
    SWPoint E ≃ Point (toW E.A E.B) :=
  haveI := instIsElliptic E
  { toFun := fun P => toPt E.A E.B (P.x, P.y)
    invFun := fun Q => ⟨(ofPt Q).1, (ofPt Q).2, valid_ofPt Q⟩
    left_inv := fun P => SWPoint.ext_pair (ofPt_toPt E.B_nonzero P.onCurve)
    right_inv := fun Q => toPt_ofPt E.B_nonzero Q }

/-- The order counted on `SWPoint E` equals Mathlib's `Nat.card` of the affine point group — the
bridge that carries the `SWPoint`-native order theory to the Mathlib-`Point` side. -/
theorem SWPoint.card_eq_point {F : Type*} [Field F] [DecidableEq F] (E : SWCurve F) :
    Nat.card (SWPoint E) = Nat.card (Point (toW E.A E.B)) :=
  Nat.card_congr (SWPoint.equivPoint E)

end CompElliptic.CurveForms.ShortWeierstrass

namespace Pasta

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta CompElliptic.CurveForms.ShortWeierstrass
  CompElliptic.CurveOrder

/-- The Pallas group order is the prime scalar-field cardinality `q`. -/
theorem pallas_card : Pallas.curve.toAffine.order = PALLAS_SCALAR_CARD := by
  have h := Pallas.card_eq
  rw [SWPoint.card_eq_point Pallas.curve] at h
  exact h

/-- The Vesta group order is the prime cardinality `p`. -/
theorem vesta_card : Vesta.curve.toAffine.order = PALLAS_BASE_CARD := by
  have h := Vesta.card_eq
  rw [SWPoint.card_eq_point Vesta.curve] at h
  exact h

/-- The Pasta base-field bit width: the circuit's `FieldSizeInBits`, the bound on
    `bitsUsed = 5·m`; `pastaFieldBits - 1` is `scaleFast2`'s `s_div_2_bits` range-check
    width. -/
abbrev pastaFieldBits : ℕ := 255

/-- The register range-check bound: `2^(pastaFieldBits-1) ≤ PALLAS_BASE_CARD` (`scaleFast2`). -/
lemma two_pow_le_pallas_base : 2 ^ (pastaFieldBits - 1) ≤ PALLAS_BASE_CARD := by
  norm_num [PALLAS_BASE_CARD]

/-- The Pallas group order is prime. -/
instance pallas_order_prime : Fact (Nat.Prime Pallas.curve.toAffine.order) :=
  ⟨by rw [pallas_card]; exact PALLAS_SCALAR_is_prime⟩

/-- The Vesta group order is prime. -/
instance vesta_order_prime : Fact (Nat.Prime Vesta.curve.toAffine.order) :=
  ⟨by rw [vesta_card]; exact PALLAS_BASE_is_prime⟩

/-- `a₁ = a₂ = a₃ = 0` on Pallas. -/
instance : Fact (Pallas.curve.toAffine.a₁ = 0 ∧ Pallas.curve.toAffine.a₂ = 0 ∧
    Pallas.curve.toAffine.a₃ = 0) := ⟨⟨rfl, rfl, rfl⟩⟩

/-- `a₁ = a₂ = a₃ = 0` on Vesta. -/
instance : Fact (Vesta.curve.toAffine.a₁ = 0 ∧ Vesta.curve.toAffine.a₂ = 0 ∧
    Vesta.curve.toAffine.a₃ = 0) := ⟨⟨rfl, rfl, rfl⟩⟩

/-! ## The scalar action on the Pasta point groups -/

open CompElliptic.Curves.Pasta.Vesta renaming curve → vestaCurve
open CompElliptic.Curves.Pasta.Pallas renaming curve → pallasCurve
open CompElliptic.Fields.Pasta

/-- The Vesta point group as a module over its scalar field. -/
instance vestaPointModule : Module Fp (SWPoint vestaCurve) :=
  AddCommGroup.zmodModule fun P => by
    rw [← Vesta.card_eq]
    exact card_nsmul_eq_zero'

/-- The Pallas point group as a module over its scalar field. -/
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
