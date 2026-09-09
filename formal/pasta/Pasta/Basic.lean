import Mathlib
import CompElliptic.CurveForms.ShortWeierstrass
import CompElliptic.Curves.Pasta
import CompElliptic.Curves.PastaOrder
import CompElliptic.Fields.Pasta
import Pasta.CompElliptic

/-!
# The Pasta group orders

The Pallas group has prime order `q = PALLAS_SCALAR_CARD`; the Vesta group has prime order
`p = PALLAS_BASE_CARD`. That is the Pasta cycle: each curve's order is the other's
base-field size.

- `pallas_card` / `vesta_card` — those orders, in Mathlib's `Nat.card (Point …)` form,
  reached through the transport in `§ Bridge to Mathlib's Affine.Point` below.
- `Fact` instances for primality and for the short-Weierstrass shape `a₁ = a₂ = a₃ = 0`.
- `vestaPointModule` / `pallasPointModule` — each point group as a module over its scalar
  field.
- `pastaFieldBits` — the base-field bit width, and the register range-check bound derived
  from it.

`WeierstrassCurve.Affine.order` and `SWCurve.toAffine` are the vocabulary the kimchi EC
gates are stated in.
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

`SWPoint E` and Mathlib's `Point (toW E.A E.B)` are two representations of the same group.
CompElliptic's `SWPoint` is the computable one, with `DecidableEq` and an executable scalar
mul; Mathlib's inductive `Point` is the one carrying the proven `AddCommGroup`. The
transport maps `toPt` / `ofPt` are mutually inverse on valid coordinates, so they package
into an `Equiv`. That is what carries the `SWPoint`-native order theory
(`CompElliptic.CurveOrder`, `Curves.PastaOrder`) over to `Nat.card (Point …)`, the form
`pallas_card` / `vesta_card` are stated in. Upstream CompElliptic does not carry this
bridge; it lives here. -/

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

/-- `SWPoint E` is additively equivalent to Mathlib's affine point group
`Point (toW E.A E.B)`, via the coordinate transport `toPt` / `ofPt`; `toPt_add` carries
the group structure across. -/
noncomputable def SWPoint.equivPoint {F : Type*} [Field F] [DecidableEq F] (E : SWCurve F) :
    SWPoint E ≃+ Point (toW E.A E.B) :=
  haveI := instIsElliptic E
  { toFun := fun P => toPt E.A E.B (P.x, P.y)
    invFun := fun Q => ⟨(ofPt Q).1, (ofPt Q).2, valid_ofPt Q⟩
    left_inv := fun P => SWPoint.ext_pair (ofPt_toPt E.B_nonzero P.onCurve)
    right_inv := fun Q => toPt_ofPt E.B_nonzero Q
    map_add' := fun P Q => toPt_add E.B_nonzero P.onCurve Q.onCurve }

/-- The order counted on `SWPoint E` equals Mathlib's `Nat.card` of the affine point group. -/
theorem SWPoint.card_eq_point {F : Type*} [Field F] [DecidableEq F] (E : SWCurve F) :
    Nat.card (SWPoint E) = Nat.card (Point (toW E.A E.B)) :=
  Nat.card_congr (SWPoint.equivPoint E).toEquiv

/-- A nonzero point's coordinates are on the curve: the `𝒪` sentinel `(0, 0)` is the only
valid off-curve pair. -/
theorem SWPoint.onCurve_of_ne_zero {F : Type*} [Field F] {E : SWCurve F} {P : SWPoint E}
    (h : P ≠ 0) : OnCurve E.A E.B (P.x, P.y) := by
  rcases P.onCurve with hc | h0
  · exact hc
  · exact absurd (SWPoint.ext_pair (Q := 0) h0) h

/-- An on-curve pair is a nonzero point: the `𝒪` sentinel `(0, 0)` is off every curve
(`B ≠ 0`) — the converse of `onCurve_of_ne_zero`. -/
theorem SWPoint.mk_ne_zero {F : Type*} [Field F] {E : SWCurve F} {x y : F}
    (h : OnCurve E.A E.B (x, y)) : (⟨x, y, Or.inl h⟩ : SWPoint E) ≠ 0 := by
  intro h0
  have hx : x = 0 := (congrArg SWPoint.x h0).trans rfl
  have hy : y = 0 := (congrArg SWPoint.y h0).trans rfl
  subst hx
  subst hy
  simp only [OnCurve] at h
  exact E.B_nonzero (by simpa using h.symm)

/-- At on-curve coordinates `equivPoint` lands on `Point.some` at the same pair —
with `onCurve_of_ne_zero`, the reading of any nonzero `SWPoint` into the gate
theorems' vocabulary. -/
theorem SWPoint.equivPoint_eq_some {F : Type*} [Field F] [DecidableEq F] {E : SWCurve F}
    (P : SWPoint E) (h : OnCurve E.A E.B (P.x, P.y)) :
    SWPoint.equivPoint E P = Point.some P.x P.y (nonsingular_toW h) :=
  toPt_some h

end CompElliptic.CurveForms.ShortWeierstrass

namespace Pasta

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta CompElliptic.CurveForms.ShortWeierstrass
  CompElliptic.CurveOrder

/-- The Pallas group order is the prime scalar-field cardinality `q`. -/
theorem pallas_card : Pallas.curve.toAffine.order = PALLAS_SCALAR_CARD := by
  have h := Pallas.card_eq
  rw [SWPoint.card_eq_point Pallas.curve] at h
  exact h

/-- The Vesta group order is the prime scalar-field cardinality `p`. -/
theorem vesta_card : Vesta.curve.toAffine.order = PALLAS_BASE_CARD := by
  have h := Vesta.card_eq
  rw [SWPoint.card_eq_point Vesta.curve] at h
  exact h

/-- The Pasta base-field bit width — the circuit's `FieldSizeInBits`, which bounds
    `bitsUsed = 5·m`. The width one below it, `pastaFieldBits - 1`, is `scaleFast2`'s
    range-check width `sDiv2Bits` (`Snarky.Circuit.Kimchi.VarBaseMul`). -/
abbrev pastaFieldBits : ℕ := 255

/-- The register range-check bound `2 ^ (pastaFieldBits - 1) ≤ PALLAS_BASE_CARD`, used by
    `scaleFast2`. -/
lemma two_pow_le_pallas_base : 2 ^ (pastaFieldBits - 1) ≤ PALLAS_BASE_CARD := by
  norm_num [PALLAS_BASE_CARD]

/-- The Pallas group order is prime. -/
instance pallas_order_prime : Fact (Nat.Prime Pallas.curve.toAffine.order) :=
  ⟨by rw [pallas_card]; exact PALLAS_SCALAR_is_prime⟩

/-- The Vesta group order is prime. -/
instance vesta_order_prime : Fact (Nat.Prime Vesta.curve.toAffine.order) :=
  ⟨by rw [vesta_card]; exact PALLAS_BASE_is_prime⟩

/-- Pallas is in short-Weierstrass shape: `a₁ = a₂ = a₃ = 0`. -/
instance : Fact (Pallas.curve.toAffine.a₁ = 0 ∧ Pallas.curve.toAffine.a₂ = 0 ∧
    Pallas.curve.toAffine.a₃ = 0) := ⟨⟨rfl, rfl, rfl⟩⟩

/-- Vesta is in short-Weierstrass shape: `a₁ = a₂ = a₃ = 0`. -/
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

/-- The same action on Mathlib's carrier, where the gate theorems live: `equivPoint`
transports the module structure. -/
instance vestaAffineModule : Module Fp vestaCurve.toAffine.Point :=
  AddCommGroup.zmodModule fun Q => by
    rw [← (SWPoint.equivPoint vestaCurve).apply_symm_apply Q, ← map_nsmul, ← Vesta.card_eq,
      card_nsmul_eq_zero', map_zero]

/-- `equivPoint` respects the scalar action: both carriers act by the canonical
representative. -/
theorem vesta_equivPoint_smul (z : Fp) (P : SWPoint vestaCurve) :
    SWPoint.equivPoint vestaCurve (z • P) = z • SWPoint.equivPoint vestaCurve P :=
  map_nsmul _ _ _

/-- The Pallas twin of `vestaAffineModule`. -/
instance pallasAffineModule : Module Fq pallasCurve.toAffine.Point :=
  AddCommGroup.zmodModule fun Q => by
    rw [← (SWPoint.equivPoint pallasCurve).apply_symm_apply Q, ← map_nsmul, ← Pallas.card_eq,
      card_nsmul_eq_zero', map_zero]

/-- The Pallas twin of `vesta_smul_val`. -/
theorem pallas_smul_val (z : Fq) (P : SWPoint pallasCurve) : z • P = z.val • P :=
  rfl

end Pasta
