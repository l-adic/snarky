import Mathlib
import Pasta.Constants
import Pasta.Curve
import CompElliptic.Curves.Pasta
import CompElliptic.Curves.PastaOrder

/-!
# The Pasta GLV eigenvalue relations — discharging the CM axioms

Both Pasta curves `y² = x³ + 5` carry the GLV endomorphism `φ(x, y) = (β·x, y)`, `β` a
primitive cube root of unity in the base field, acting on the point group as multiplication
by a scalar eigenvalue `λ`. This file **proves** `φ(P) = [λ]·P` for every point, under the
Hasse bound — turning `Pasta.pallas_eigen` / `Pasta.vesta_eigen` from axioms into theorems
(the swap itself happens in `Pasta/Basic.lean`, which consumes `{pallas,vesta}_eigen_of_hasse`
from here). The trust surface shrinks to Hasse + two `native_decide` anchors declared below.

The proof is the classical three-step extension of a single-point certificate:

1. **`φ` is additive on raw coordinates** (`endoPair_add`): for any field `F` and any
   `β` with `β³ = 1`, the map `(x, y) ↦ (β·x, y)` commutes with the complete affine
   addition `ShortWeierstrass.add 0` — pure field algebra, branch by branch (the slope
   scales by `β²`, so `x₃` scales by `β⁴ = β` and `y₃` by `β³ = 1`). No on-curve or
   characteristic hypotheses are needed; division in a Lean field is total (`x/0 = 0`),
   so in the junk cases (vanishing denominators off the curve) both slopes degrade to `0`
   consistently and the identities still hold.
2. **`φ` is a group endomorphism of `SWPoint E`** (`endoHom`): `β³ = 1` also keeps
   on-curve points on the curve (`(β·x)³ = x³`) and fixes the `(0, 0) ≡ 𝒪` sentinel, so
   `endoPair` lifts to an `AddMonoidHom` on any `SWCurve` with `A = 0`.
3. **The anchor extends to every point**: under the Hasse bound the group has prime order
   (`Curves.PastaOrder.card_eq`), so the generator `Gpt` spans: every `P` is `k • Gpt`.
   The `native_decide` certificate `{pallas,vesta}_lam_nsmul_Gpt : λ • Gpt = φ(Gpt)` —
   declared here, in the style of CompElliptic's point counts — then propagates:
   `φ(k • Gpt) = k • φ(Gpt) = k • λ • Gpt = λ • (k • Gpt)`.

Finally `toPtHom` bundles CompElliptic's `toPt` transport as an `AddMonoidHom` into
Mathlib's `WeierstrassCurve.Affine.Point` group, and `{pallas,vesta}_eigen_of_hasse` restate
the eigenvalue relation in exactly the shape of the (former) axioms, parametrized by the
Hasse bound that `Pasta/Basic.lean` supplies from `{pallas,vesta}_hasse`.

**Public surface**: `{pallas,vesta}_eigen_of_hasse` (what `Basic.lean` consumes) and the
anchor certificates with their statement components (`*_lam_nat`, `*_endoGpt`,
`*_lam_nsmul_Gpt` — the axiom gates allow exactly these two `native_decide`s by name).
Every intermediate — the raw endomorphism, its additivity, the homs, the `SWPoint`-level
eigenvalue relations — is `private`.
-/

namespace Pasta

open CompElliptic.CurveForms CompElliptic.CurveForms.ShortWeierstrass
open CompElliptic.Curves.Pasta CompElliptic.CurveOrder CompElliptic.Fields.Pasta
open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Step 1 — the raw endomorphism and its additivity

`endoPair` is `φ` on bare coordinate pairs. `endoPair_add` is the heart of the discharge:
`φ` commutes with the complete affine addition, for **any** field and **any** cube root of
unity — no on-curve hypotheses, no characteristic assumptions. Total division (`x/0 = 0`)
makes the slope identities hold even in the junk branches. -/

/-- The GLV endomorphism on raw coordinate pairs: `φ(x, y) = (β·x, y)`. It fixes the
    `(0, 0) ≡ 𝒪` sentinel (`β·0 = 0`). -/
private def endoPair (β : F) (p : F × F) : F × F := (β * p.1, p.2)

omit [DecidableEq F] in
/-- The shared slope-branch computation behind `endoPair_add`: if the slope scales by `β²`,
    then the output point of the chord/tangent formula scales exactly by `endoPair`
    (`x₃` picks up `β⁴ = β`, `y₃` picks up `β³ = 1`). Stated for an opaque `lam`, so it
    closes both the doubling and the secant branch. -/
private lemma endoPair_branch {β lam x₁ x₂ y₁ : F} (hβ : β ^ 3 = 1) :
    endoPair β (lam ^ 2 - x₁ - x₂, lam * (x₁ - (lam ^ 2 - x₁ - x₂)) - y₁)
      = ((β ^ 2 * lam) ^ 2 - β * x₁ - β * x₂,
         β ^ 2 * lam * (β * x₁ - ((β ^ 2 * lam) ^ 2 - β * x₁ - β * x₂)) - y₁) := by
  simp only [endoPair, Prod.mk.injEq]
  constructor
  · linear_combination (-(β * lam ^ 2)) * hβ
  · linear_combination (lam ^ 3 * β ^ 3 + lam ^ 3 - 2 * lam * x₁ - lam * x₂) * hβ

/-- **`φ` is additive on raw coordinates.** For any `β` with `β³ = 1`,
    `φ(p + q) = φ(p) + φ(q)` where `+` is the complete short-Weierstrass addition with
    curve coefficient `a = 0`. Pure field algebra over the five branches of `add`; the
    junk cases (vanishing denominators) hold because division is total. -/
private theorem endoPair_add {β : F} (hβ : β ^ 3 = 1) (p q : F × F) :
    endoPair β (add (0 : F) p q) = add 0 (endoPair β p) (endoPair β q) := by
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hβ
    exact zero_ne_one hβ
  obtain ⟨x₁, y₁⟩ := p
  obtain ⟨x₂, y₂⟩ := q
  by_cases hp0 : (x₁, y₁) = ((0 : F), (0 : F))
  · rw [hp0, ShortWeierstrass.zero_add,
      show endoPair β ((0 : F), (0 : F)) = ((0 : F), (0 : F)) from by simp [endoPair],
      ShortWeierstrass.zero_add]
  by_cases hq0 : (x₂, y₂) = ((0 : F), (0 : F))
  · rw [hq0, ShortWeierstrass.add_zero,
      show endoPair β ((0 : F), (0 : F)) = ((0 : F), (0 : F)) from by simp [endoPair],
      ShortWeierstrass.add_zero]
  have hp0' : (β * x₁, y₁) ≠ ((0 : F), (0 : F)) := by
    intro hc
    rw [Prod.mk.injEq] at hc
    exact hp0 (by
      rw [Prod.mk.injEq]
      exact ⟨(mul_eq_zero.mp hc.1).resolve_left hβ0, hc.2⟩)
  have hq0' : (β * x₂, y₂) ≠ ((0 : F), (0 : F)) := by
    intro hc
    rw [Prod.mk.injEq] at hc
    exact hq0 (by
      rw [Prod.mk.injEq]
      exact ⟨(mul_eq_zero.mp hc.1).resolve_left hβ0, hc.2⟩)
  rw [show endoPair β (x₁, y₁) = (β * x₁, y₁) from rfl,
      show endoPair β (x₂, y₂) = (β * x₂, y₂) from rfl]
  by_cases hx : x₁ = x₂
  · by_cases hy : y₁ + y₂ = 0
    · -- mutual inverses: both additions return the sentinel, which `φ` fixes
      have e1 : add (0 : F) (x₁, y₁) (x₂, y₂) = ((0 : F), (0 : F)) := by
        unfold ShortWeierstrass.add
        dsimp only
        rw [if_neg hp0, if_neg hq0, if_pos hx, if_pos hy]
      have e2 : add (0 : F) (β * x₁, y₁) (β * x₂, y₂) = ((0 : F), (0 : F)) := by
        unfold ShortWeierstrass.add
        dsimp only
        rw [if_neg hp0', if_neg hq0', if_pos (show β * x₁ = β * x₂ by rw [hx]), if_pos hy]
      rw [e1, e2]
      simp [endoPair]
    · -- doubling: the tangent slope scales by `β²` (shared denominator `2y₁`)
      have hlam : (3 * (β * x₁) ^ 2 + 0) / (2 * y₁)
          = β ^ 2 * ((3 * x₁ ^ 2 + 0) / (2 * y₁)) := by
        rw [← mul_div_assoc]
        congr 1
        ring
      unfold ShortWeierstrass.add
      dsimp only
      rw [if_neg hp0, if_neg hq0, if_pos hx, if_neg hy, if_neg hp0', if_neg hq0',
        if_pos (show β * x₁ = β * x₂ by rw [hx]), if_neg hy, hlam]
      exact endoPair_branch hβ
  · -- secant: the chord slope scales by `β²` (`1/β = β²` clears into the denominator)
    have hx' : ¬ β * x₁ = β * x₂ := fun hc => hx (mul_left_cancel₀ hβ0 hc)
    have hβinv : β⁻¹ = β ^ 2 := inv_eq_of_mul_eq_one_right (by linear_combination hβ)
    have hlam : (y₂ - y₁) / (β * x₂ - β * x₁) = β ^ 2 * ((y₂ - y₁) / (x₂ - x₁)) := by
      rw [show β * x₂ - β * x₁ = β * (x₂ - x₁) from by ring, div_eq_mul_inv, mul_inv,
        hβinv, div_eq_mul_inv]
      ring
    unfold ShortWeierstrass.add
    dsimp only
    rw [if_neg hp0, if_neg hq0, if_neg hx, if_neg hp0', if_neg hq0', if_neg hx', hlam]
    exact endoPair_branch hβ

/-! ## Step 2 — `φ` as a group endomorphism of `SWPoint E`

On a curve with `A = 0`, `β³ = 1` keeps on-curve points on the curve (`(β·x)³ = x³`) and
fixes the sentinel, so `endoPair` lifts to `SWPoint E`; `endoPair_add` makes the lift an
`AddMonoidHom`, and `map_nsmul`/`map_zsmul` come for free. -/

omit [DecidableEq F] in
/-- `φ` preserves representability: on-curve points stay on the curve (`(β·x)³ = x³` by
    `β³ = 1`, and `A = 0` kills the linear term), and the `(0, 0)` sentinel is fixed. -/
private theorem valid_endoPair {E : SWCurve F} (hA : E.A = 0) {β : F} (hβ : β ^ 3 = 1)
    {p : F × F} (hp : Valid E.A E.B p) : Valid E.A E.B (endoPair β p) := by
  rcases hp with h | h
  · left
    obtain ⟨x, y⟩ := p
    simp only [OnCurve, endoPair] at h ⊢
    rw [hA] at h ⊢
    linear_combination h - x ^ 3 * hβ
  · right
    rw [h]
    simp [endoPair]

/-- The GLV endomorphism on `SWPoint E` (for a curve with `A = 0` and a cube root of
    unity `β`): `φ⟨x, y⟩ = ⟨β·x, y⟩`. -/
private def endoPt (E : SWCurve F) (hA : E.A = 0) {β : F} (hβ : β ^ 3 = 1) (P : SWPoint E) :
    SWPoint E :=
  ⟨β * P.x, P.y, valid_endoPair hA hβ P.onCurve⟩

/-- `endoPt` bundled as a group endomorphism of `SWPoint E` — additivity is
    `endoPair_add` transported through `SWPoint.ext_pair`. -/
private def endoHom (E : SWCurve F) (hA : E.A = 0) {β : F} (hβ : β ^ 3 = 1) :
    SWPoint E →+ SWPoint E where
  toFun := endoPt E hA hβ
  map_zero' := SWPoint.ext_pair (by
    show (β * (0 : F), (0 : F)) = ((0 : F), (0 : F))
    rw [mul_zero])
  map_add' P Q := SWPoint.ext_pair (by
    show endoPair β (add E.A (P.x, P.y) (Q.x, Q.y))
      = add E.A (β * P.x, P.y) (β * Q.x, Q.y)
    rw [hA]
    exact endoPair_add hβ (P.x, P.y) (Q.x, Q.y))

/-! ## The computational anchors — `λ • G = φ(G)` at the standard generator

One `native_decide` certificate per curve, in the style of CompElliptic's point counts
(`Curves/PastaOrder.lean`): the eigenvalue relation at the standard generator, evaluated
through the binary double-and-add `nsmul`. These are the only `native_decide`s in the
workspace packages; the axiom gates permit exactly these two declarations by name. -/

/-- `Pasta.pallas_lam` as a bare `ℕ` numeral — the `nsmul` scalar of the anchor.
    `pallas_lam = ↑pallas_lam_nat` is a `decide` step inside `pallas_eigen_of_hasse`. -/
def pallas_lam_nat : ℕ :=
  26005156700822196841419187675678338661165322343552424574062261873906994770353

/-- The image of the standard Pallas generator under `φ(x, y) = (β·x, y)` — on the curve
    since `(β·x)³ = x³`. -/
def pallas_endoGpt : SWPoint Pallas.curve :=
  ⟨pallas_endo * Pallas.G.1, Pallas.G.2, by
    left
    show Pallas.G.2 ^ 2
      = (pallas_endo * Pallas.G.1) ^ 3 + Pallas.a * (pallas_endo * Pallas.G.1) + Pallas.b
    decide⟩

/-- **The Pallas eigenvalue anchor**: `λ • G = φ(G)` at the standard generator. -/
theorem pallas_lam_nsmul_Gpt : pallas_lam_nat • Pallas.Gpt = pallas_endoGpt := by
  native_decide

/-- `Pasta.vesta_lam` as a bare `ℕ` numeral — the `nsmul` scalar of the anchor. -/
def vesta_lam_nat : ℕ :=
  8503465768106391777493614032514048814691664078728891710322960303815233784505

/-- The image of the standard Vesta generator under `φ(x, y) = (β·x, y)`. -/
def vesta_endoGpt : SWPoint Vesta.curve :=
  ⟨vesta_endo * Vesta.G.1, Vesta.G.2, by
    left
    show Vesta.G.2 ^ 2
      = (vesta_endo * Vesta.G.1) ^ 3 + Vesta.a * (vesta_endo * Vesta.G.1) + Vesta.b
    decide⟩

/-- **The Vesta eigenvalue anchor**: `λ • G = φ(G)` at the standard generator. -/
theorem vesta_lam_nsmul_Gpt : vesta_lam_nat • Vesta.Gpt = vesta_endoGpt := by
  native_decide

/-! ## The transport homomorphism into Mathlib's point group

CompElliptic's `toPt` (`𝒪 ↦ 0`, on-curve `(x, y) ↦ Point.some x y _`) is already proved a
homomorphism (`toPt_add`); bundling it lets `map_nsmul` push scalar multiples across the
`SWPoint`/`Affine.Point` seam without a bespoke induction. -/

/-- CompElliptic's `toPt` transport, bundled as an `AddMonoidHom` from `SWPoint E` to
    Mathlib's affine point group of `E.toAffine`. -/
private noncomputable def toPtHom (E : SWCurve F) : SWPoint E →+ Point E.toAffine where
  toFun P := toPt E.A E.B (P.x, P.y)
  map_zero' := toPt_zero E.B_nonzero
  map_add' P Q := toPt_add E.B_nonzero P.onCurve Q.onCurve

/-! ## Step 3 — the anchors extend to every point (under Hasse)

Under the Hasse bound each Pasta group has prime order, so any nonzero point generates —
in particular `Gpt` does. The anchor certificate `*_lam_nsmul_Gpt` at `Gpt` then extends
to all of `SWPoint curve` by additivity of `φ`. -/

/-- `φ` at the order-witness generator is `pallas_endoGpt` — both sides carry the same
    `β` numeral, so the coordinates agree definitionally. -/
private theorem pallas_endoPt_Gpt :
    endoPt Pallas.curve rfl pallas_endo_cube Pallas.Gpt = pallas_endoGpt :=
  SWPoint.ext_pair rfl

/-- **The Pallas eigenvalue relation on `SWPoint`**: `φ(P) = [λ]·P` for every point,
    assuming the Hasse bound. The group is cyclic of prime order (`card_eq`), so
    `P = k • Gpt`; `endoHom` and the `native_decide` anchor `pallas_lam_nsmul_Gpt` do
    the rest. -/
private theorem pallas_endoPt_eq_lam_smul (hH : HasseBound Pallas.curve)
    (P : SWPoint Pallas.curve) :
    endoPt Pallas.curve rfl pallas_endo_cube P = pallas_lam_nat • P := by
  have hmem : P ∈ AddSubgroup.zmultiples Pallas.Gpt :=
    mem_zmultiples_of_prime_card (Pallas.card_eq hH) Pallas.Gpt_ne_zero
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  have hhom : endoPt Pallas.curve rfl pallas_endo_cube (k • Pallas.Gpt)
      = k • endoPt Pallas.curve rfl pallas_endo_cube Pallas.Gpt :=
    map_zsmul (endoHom Pallas.curve rfl pallas_endo_cube) k Pallas.Gpt
  rw [← hk, hhom, pallas_endoPt_Gpt, ← pallas_lam_nsmul_Gpt,
    ← natCast_zsmul, ← natCast_zsmul, ← mul_smul, ← mul_smul, mul_comm]

/-- `φ` at the order-witness generator is `vesta_endoGpt` (Vesta). -/
private theorem vesta_endoPt_Gpt :
    endoPt Vesta.curve rfl vesta_endo_cube Vesta.Gpt = vesta_endoGpt :=
  SWPoint.ext_pair rfl

/-- **The Vesta eigenvalue relation on `SWPoint`**: `φ(P) = [λ]·P` for every point,
    assuming the Hasse bound. -/
private theorem vesta_endoPt_eq_lam_smul (hH : HasseBound Vesta.curve)
    (P : SWPoint Vesta.curve) :
    endoPt Vesta.curve rfl vesta_endo_cube P = vesta_lam_nat • P := by
  have hmem : P ∈ AddSubgroup.zmultiples Vesta.Gpt :=
    mem_zmultiples_of_prime_card (Vesta.card_eq hH) Vesta.Gpt_ne_zero
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  have hhom : endoPt Vesta.curve rfl vesta_endo_cube (k • Vesta.Gpt)
      = k • endoPt Vesta.curve rfl vesta_endo_cube Vesta.Gpt :=
    map_zsmul (endoHom Vesta.curve rfl vesta_endo_cube) k Vesta.Gpt
  rw [← hk, hhom, vesta_endoPt_Gpt, ← vesta_lam_nsmul_Gpt,
    ← natCast_zsmul, ← natCast_zsmul, ← mul_smul, ← mul_smul, mul_comm]

/-! ## Step 4 — the Mathlib-`Point` eigenvalue statements

Exactly the shape of the (former) `pallas_eigen`/`vesta_eigen` axioms, parametrized by the
Hasse bound; `Pasta/Basic.lean` closes them with `pallas_hasse`/`vesta_hasse`. The
`Nonsingular → OnCurve` bridge is `equation_toW`, and `toPtHom` + `map_nsmul` carry the
`SWPoint` relation across; the scalar changes type by `natCast_zsmul` (`pallas_lam` is the
`ℤ`-numeral of `pallas_lam_nat`). -/

/-- **The Pallas eigenvalue relation, Mathlib-`Point` form, under Hasse.** This is the
    exact statement of the former `Pasta.pallas_eigen` axiom with the Hasse bound made an
    explicit hypothesis. -/
theorem pallas_eigen_of_hasse (hH : HasseBound Pallas.curve) {x y : Fp}
    (h : Pallas.curve.toAffine.Nonsingular x y)
    (h' : Pallas.curve.toAffine.Nonsingular (pallas_endo * x) y) :
    Point.some _ _ h' = pallas_lam • Point.some _ _ h := by
  have honc : OnCurve Pallas.curve.A Pallas.curve.B (x, y) := equation_toW.mp h.1
  have honc' : OnCurve Pallas.curve.A Pallas.curve.B (pallas_endo * x, y) :=
    equation_toW.mp h'.1
  set P : SWPoint Pallas.curve := ⟨x, y, Or.inl honc⟩ with hPdef
  have hmap := congrArg (toPtHom Pallas.curve) (pallas_endoPt_eq_lam_smul hH P)
  rw [map_nsmul] at hmap
  have hL : toPtHom Pallas.curve (endoPt Pallas.curve rfl pallas_endo_cube P)
      = Point.some (pallas_endo * x) y h' := by
    show toPt Pallas.curve.A Pallas.curve.B (pallas_endo * x, y) = _
    rw [toPt_some honc']
  have hR : toPtHom Pallas.curve P = Point.some x y h := by
    show toPt Pallas.curve.A Pallas.curve.B (x, y) = _
    rw [toPt_some honc]
  rw [hL, hR] at hmap
  rw [show pallas_lam = (pallas_lam_nat : ℤ) from by decide, natCast_zsmul]
  exact hmap

/-- **The Vesta eigenvalue relation, Mathlib-`Point` form, under Hasse.** The exact
    statement of the former `Pasta.vesta_eigen` axiom with the Hasse bound explicit. -/
theorem vesta_eigen_of_hasse (hH : HasseBound Vesta.curve) {x y : Fq}
    (h : Vesta.curve.toAffine.Nonsingular x y)
    (h' : Vesta.curve.toAffine.Nonsingular (vesta_endo * x) y) :
    Point.some _ _ h' = vesta_lam • Point.some _ _ h := by
  have honc : OnCurve Vesta.curve.A Vesta.curve.B (x, y) := equation_toW.mp h.1
  have honc' : OnCurve Vesta.curve.A Vesta.curve.B (vesta_endo * x, y) :=
    equation_toW.mp h'.1
  set P : SWPoint Vesta.curve := ⟨x, y, Or.inl honc⟩ with hPdef
  have hmap := congrArg (toPtHom Vesta.curve) (vesta_endoPt_eq_lam_smul hH P)
  rw [map_nsmul] at hmap
  have hL : toPtHom Vesta.curve (endoPt Vesta.curve rfl vesta_endo_cube P)
      = Point.some (vesta_endo * x) y h' := by
    show toPt Vesta.curve.A Vesta.curve.B (vesta_endo * x, y) = _
    rw [toPt_some honc']
  have hR : toPtHom Vesta.curve P = Point.some x y h := by
    show toPt Vesta.curve.A Vesta.curve.B (x, y) = _
    rw [toPt_some honc]
  rw [hL, hR] at hmap
  rw [show vesta_lam = (vesta_lam_nat : ℤ) from by decide, natCast_zsmul]
  exact hmap

end Pasta
