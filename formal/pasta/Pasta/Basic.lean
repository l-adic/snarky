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

/-- In a `ZMod n`-module, an integer acts as its residue's canonical representative. This is
the integer-to-scalar reduction the in-circuit readers perform when a gadget's integer decode
meets the wire verifier's scalar-field action, which computes with `ZMod.val`.

Stated over the module instance rather than over a bare `∀ x, n • x = 0`: the killing fact is
what builds the instance (`AddCommGroup.zmodModule`), so a consumer that has the instance
should not have to thread the fact as well. -/
theorem zsmul_eq_val_nsmul {G : Type*} [AddCommGroup G] (n : ℕ) [NeZero n] [Module (ZMod n) G]
    (z : ℤ) (x : G) : z • x = ((z : ZMod n).val : ℕ) • x := by
  rw [← Int.cast_smul_eq_zsmul (ZMod n) z x]
  conv_lhs => rw [← ZMod.natCast_zmod_val ((z : ZMod n))]
  rw [Nat.cast_smul_eq_nsmul]

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

/-! ## Scalar multiples of a point of prime order

Two facts about any short-Weierstrass curve of prime order, used wherever a run has to know
that an accumulator has not collapsed onto the base or onto zero. They are pure group theory:
nothing here mentions a gate, a circuit or a sponge. -/

/-- **Core non-degeneracy.** With prime `order`, a nonzero point times a scalar strictly
between `0` and `order` is nonzero. -/
lemma smul_ne_zero_of_lt {F : Type*} [Field F] [DecidableEq F] (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] {T : c.Point} (hT : T ≠ 0)
    {k : ℤ} (h0 : 0 < k) (hlt : k < (c.order : ℤ)) : k • T ≠ 0 := by
  intro h_contra
  -- prime `order` together with `0 < k < order` forces `gcd k order = 1`
  have h_coprime : Int.gcd k (c.order : ℤ) = 1 := by
    refine Nat.coprime_comm.mp
      ((Fact.out : Nat.Prime c.order).coprime_iff_not_dvd.mpr fun hd => ?_)
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
  have hord : (c.order : ℤ) • T = 0 := by rw [natCast_zsmul]; exact card_nsmul_eq_zero'
  rw [h_contra, hord, smul_zero, smul_zero, _root_.add_zero] at h_decomp
  exact hT h_decomp

/-- **Prime order ⇒ full order.** For a nonzero point `T`, a scalar multiple `m • T` vanishes
iff `order ∣ m`. (`order` is prime and `order • T = 0`, so `addOrderOf T ∣ order`; nonzero `T`
rules out `addOrderOf T = 1`, hence it equals `order`.) -/
lemma zsmul_eq_zero_iff_order_dvd {F : Type*} [Field F] [DecidableEq F]
    (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] {T : c.Point} (hT : T ≠ 0) (m : ℤ) :
    m • T = 0 ↔ (c.order : ℤ) ∣ m := by
  have hdvd : (addOrderOf T : ℤ) ∣ (c.order : ℤ) :=
    addOrderOf_dvd_iff_zsmul_eq_zero.mpr (by rw [natCast_zsmul]; exact card_nsmul_eq_zero')
  have horder : addOrderOf T = c.order := by
    have hnat : addOrderOf T ∣ c.order := by exact_mod_cast hdvd
    rcases Nat.Prime.eq_one_or_self_of_dvd (Fact.out : Nat.Prime c.order) _ hnat with h1 | h1
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hT
    · exact h1
  rw [← addOrderOf_dvd_iff_zsmul_eq_zero, horder]

/-- The Pallas twin of `vesta_smul_val`. -/
theorem pallas_smul_val (z : Fq) (P : SWPoint pallasCurve) : z • P = z.val • P :=
  rfl

end Pasta
