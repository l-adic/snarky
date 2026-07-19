import Mathlib
import Pasta.Basic
import CompElliptic.Curves.Pasta
import CompElliptic.Curves.PastaOrder

/-!
# The Pasta GLV endomorphisms

Both Pasta curves `y² = x³ + 5` carry the GLV endomorphism `φ(x, y) = (β·x, y)`, `β` a
primitive cube root of unity in the base field: the coefficients `β` and scalar
eigenvalues `λ`, the eigenvalue relations `φ(P) = [λ]·P` (`{pallas,vesta}_eigen`), and
the GLV lattice short-basis bounds (`{pallas,vesta}_glv_no_short_relation`).

The eigenvalue relation extends a `native_decide` certificate at the generator: `φ` is
additive, the group is cyclic of prime order, and `toPt` transports to Mathlib's point
group.

**Public surface**: `*_endo`, `*_lam`, `*_endo_nonsingular`, the anchors
`*_lam_nsmul_Gpt`, `{pallas,vesta}_eigen`, `{pallas,vesta}_glv_no_short_relation`;
everything else is `private`.
-/

namespace Pasta

open CompElliptic.CurveForms CompElliptic.CurveForms.ShortWeierstrass
open CompElliptic.Curves.Pasta CompElliptic.CurveOrder CompElliptic.Fields.Pasta
open WeierstrassCurve.Affine

/-! ## The GLV constants -/

/-- The Pallas base-field endomorphism coefficient `β`: a primitive cube root of unity,
    so `φ(x, y) = (β·x, y)` maps `y² = x³ + 5` to itself. -/
def pallas_endo : Fp :=
  20444556541222657078399132219657928148671392403212669005631716460534733845831

/-- `β³ = 1` on Pallas. -/
private theorem pallas_endo_cube : pallas_endo ^ 3 = 1 := by decide


/-- The Vesta base-field endomorphism coefficient `β`: a primitive cube root of unity,
    so `φ(x, y) = (β·x, y)` maps `y² = x³ + 5` to itself. It is also the SvdW map-to-curve
    parameter `(√-3 − 1)/2` (`Poseidon.GroupMapVesta`). -/
def vesta_endo : Fq :=
  2942865608506852014473558576493638302197734138389222805617480874486368177743

/-- `β³ = 1` on Vesta. -/
private theorem vesta_endo_cube : vesta_endo ^ 3 = 1 := by decide


/-- The scalar eigenvalue `λ` of the Pallas endomorphism `φ` — a primitive cube root of
    unity in the scalar field (`endo_scalar`, `Snarky.Curves.PastaCurve`). -/
def pallas_lam : ℤ :=
  26005156700822196841419187675678338661165322343552424574062261873906994770353

/-- The scalar eigenvalue `λ` of the Vesta endomorphism `φ` — a primitive cube root of
    unity in the scalar field (`endo_scalar`); also the `λ` of the Fiat-Shamir challenge
    expansion (proof-systems `endos::<Vesta>().1`). -/
def vesta_lam : ℤ :=
  8503465768106391777493614032514048814691664078728891710322960303815233784505

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Additivity of the raw endomorphism -/

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

/-! ## `φ` as a group endomorphism of `SWPoint E` -/

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

/-- The GLV endomorphism `φ⟨x, y⟩ = ⟨β·x, y⟩` as a group endomorphism of `SWPoint E`,
    for a curve with `A = 0` and a cube root of unity `β`. -/
private def endoHom (E : SWCurve F) (hA : E.A = 0) {β : F} (hβ : β ^ 3 = 1) :
    SWPoint E →+ SWPoint E where
  toFun P := ⟨β * P.x, P.y, valid_endoPair hA hβ P.onCurve⟩
  map_zero' := SWPoint.ext_pair (by
    show (β * (0 : F), (0 : F)) = ((0 : F), (0 : F))
    rw [mul_zero])
  map_add' P Q := SWPoint.ext_pair (by
    show endoPair β (add E.A (P.x, P.y) (Q.x, Q.y))
      = add E.A (β * P.x, P.y) (β * Q.x, Q.y)
    rw [hA]
    exact endoPair_add hβ (P.x, P.y) (Q.x, Q.y))

/-! ## The computational anchors — `λ • G = φ(G)` at the standard generator

One `native_decide` certificate per curve — the only `native_decide`s in the workspace
packages; the axiom gates permit exactly these two declarations by name. -/

/-- **The Pallas eigenvalue anchor**: `λ • G = φ(G)` at the standard generator
    (`.toNat` puts the `ℤ` eigenvalue in `nsmul` position). -/
theorem pallas_lam_nsmul_Gpt :
    pallas_lam.toNat • Pallas.Gpt = endoHom Pallas.curve rfl pallas_endo_cube Pallas.Gpt := by
  native_decide

/-- **The Vesta eigenvalue anchor**: `λ • G = φ(G)` at the standard generator. -/
theorem vesta_lam_nsmul_Gpt :
    vesta_lam.toNat • Vesta.Gpt = endoHom Vesta.curve rfl vesta_endo_cube Vesta.Gpt := by
  native_decide

/-! ## The transport homomorphism into Mathlib's point group -/

/-- CompElliptic's `toPt` transport, bundled as an `AddMonoidHom` from `SWPoint E` to
    Mathlib's affine point group of `E.toAffine`. -/
private noncomputable def toPtHom (E : SWCurve F) : SWPoint E →+ Point E.toAffine where
  toFun P := toPt E.A E.B (P.x, P.y)
  map_zero' := toPt_zero E.B_nonzero
  map_add' P Q := toPt_add E.B_nonzero P.onCurve Q.onCurve

/-! ## The anchors extend to every point -/

/-- **The Pallas eigenvalue relation on `SWPoint`**: `φ(P) = [λ]·P` for every point. -/
private theorem pallas_endoHom_eq_lam_smul (P : SWPoint Pallas.curve) :
    endoHom Pallas.curve rfl pallas_endo_cube P = pallas_lam.toNat • P := by
  have hmem : P ∈ AddSubgroup.zmultiples Pallas.Gpt :=
    mem_zmultiples_of_prime_card Pallas.card_eq Pallas.Gpt_ne_zero
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  rw [← hk, map_zsmul, ← pallas_lam_nsmul_Gpt,
    ← natCast_zsmul, ← natCast_zsmul, ← mul_smul, ← mul_smul, mul_comm]

/-- **The Vesta eigenvalue relation on `SWPoint`**: `φ(P) = [λ]·P` for every point. -/
private theorem vesta_endoHom_eq_lam_smul (P : SWPoint Vesta.curve) :
    endoHom Vesta.curve rfl vesta_endo_cube P = vesta_lam.toNat • P := by
  have hmem : P ∈ AddSubgroup.zmultiples Vesta.Gpt :=
    mem_zmultiples_of_prime_card Vesta.card_eq Vesta.Gpt_ne_zero
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  rw [← hk, map_zsmul, ← vesta_lam_nsmul_Gpt,
    ← natCast_zsmul, ← natCast_zsmul, ← mul_smul, ← mul_smul, mul_comm]

/-! ## The Mathlib-`Point` eigenvalue statements -/

/-- `φ` maps curve points to curve points — the `Point.some` obligation of
    `pallas_eigen`'s conclusion. -/
theorem pallas_endo_nonsingular {x y : Fp}
    (h : Pallas.curve.toAffine.Nonsingular x y) :
    Pallas.curve.toAffine.Nonsingular (pallas_endo * x) y := by
  have honc : OnCurve Pallas.curve.A Pallas.curve.B (x, y) := equation_toW.mp h.1
  refine nonsingular_toW ?_
  show y ^ 2 = (pallas_endo * x) ^ 3 + Pallas.curve.A * (pallas_endo * x) + Pallas.curve.B
  have heq : y ^ 2 = x ^ 3 + Pallas.curve.A * x + Pallas.curve.B := honc
  rw [show Pallas.curve.A = 0 from rfl] at heq ⊢
  linear_combination heq - x ^ 3 * pallas_endo_cube

/-- The Pallas endomorphism acts as `[λ]` on the point group: `φ(P) = [λ]·P`, the image
    point supplied by `pallas_endo_nonsingular`. Discharges
    `Kimchi.Gate.EndoMul.endoMul`'s hypothesis `heig`. -/
theorem pallas_eigen {x y : Fp}
    (h : Pallas.curve.toAffine.Nonsingular x y) :
    Point.some _ _ (pallas_endo_nonsingular h) = pallas_lam • Point.some _ _ h := by
  have h' := pallas_endo_nonsingular h
  have honc : OnCurve Pallas.curve.A Pallas.curve.B (x, y) := equation_toW.mp h.1
  have honc' : OnCurve Pallas.curve.A Pallas.curve.B (pallas_endo * x, y) :=
    equation_toW.mp h'.1
  set P : SWPoint Pallas.curve := ⟨x, y, Or.inl honc⟩ with hPdef
  have hmap := congrArg (toPtHom Pallas.curve) (pallas_endoHom_eq_lam_smul P)
  rw [map_nsmul] at hmap
  have hL : toPtHom Pallas.curve (endoHom Pallas.curve rfl pallas_endo_cube P)
      = Point.some (pallas_endo * x) y h' := by
    show toPt Pallas.curve.A Pallas.curve.B (pallas_endo * x, y) = _
    rw [toPt_some honc']
  have hR : toPtHom Pallas.curve P = Point.some x y h := by
    show toPt Pallas.curve.A Pallas.curve.B (x, y) = _
    rw [toPt_some honc]
  rw [hL, hR] at hmap
  rw [show pallas_lam = (pallas_lam.toNat : ℤ) from by decide, natCast_zsmul]
  exact hmap

/-- `φ` maps curve points to curve points — the Vesta twin of
    `pallas_endo_nonsingular`. -/
theorem vesta_endo_nonsingular {x y : Fq}
    (h : Vesta.curve.toAffine.Nonsingular x y) :
    Vesta.curve.toAffine.Nonsingular (vesta_endo * x) y := by
  have honc : OnCurve Vesta.curve.A Vesta.curve.B (x, y) := equation_toW.mp h.1
  refine nonsingular_toW ?_
  show y ^ 2 = (vesta_endo * x) ^ 3 + Vesta.curve.A * (vesta_endo * x) + Vesta.curve.B
  have heq : y ^ 2 = x ^ 3 + Vesta.curve.A * x + Vesta.curve.B := honc
  rw [show Vesta.curve.A = 0 from rfl] at heq ⊢
  linear_combination heq - x ^ 3 * vesta_endo_cube

/-- The Vesta endomorphism acts as `[λ]` on the point group — the Vesta twin of
    `pallas_eigen`. -/
theorem vesta_eigen {x y : Fq}
    (h : Vesta.curve.toAffine.Nonsingular x y) :
    Point.some _ _ (vesta_endo_nonsingular h) = vesta_lam • Point.some _ _ h := by
  have h' := vesta_endo_nonsingular h
  have honc : OnCurve Vesta.curve.A Vesta.curve.B (x, y) := equation_toW.mp h.1
  have honc' : OnCurve Vesta.curve.A Vesta.curve.B (vesta_endo * x, y) :=
    equation_toW.mp h'.1
  set P : SWPoint Vesta.curve := ⟨x, y, Or.inl honc⟩ with hPdef
  have hmap := congrArg (toPtHom Vesta.curve) (vesta_endoHom_eq_lam_smul P)
  rw [map_nsmul] at hmap
  have hL : toPtHom Vesta.curve (endoHom Vesta.curve rfl vesta_endo_cube P)
      = Point.some (vesta_endo * x) y h' := by
    show toPt Vesta.curve.A Vesta.curve.B (vesta_endo * x, y) = _
    rw [toPt_some honc']
  have hR : toPtHom Vesta.curve P = Point.some x y h := by
    show toPt Vesta.curve.A Vesta.curve.B (x, y) = _
    rw [toPt_some honc]
  rw [hL, hR] at hmap
  rw [show vesta_lam = (vesta_lam.toNat : ℤ) from by decide, natCast_zsmul]
  exact hmap

/-! ## The GLV lattice short-basis bounds -/

/-- No short relation in a rank-2 GLV lattice, from a reduced-basis certificate: if
    `(s, t)` lies in the lattice `{(a,b) : a + b·λ ≡ 0 (mod n)}` (`s + t·λ = k₂·n`), is
    primitive (`u·s + v·t = 1`), has `|s| > 2¹²⁶`, and the box `[−2¹²⁶, 2¹²⁶]²` fits below
    the covolume (`2¹²⁶·(|s|+|t|) < n`), then no nonzero `(a,b)` in that box lies in the
    lattice. -/
private theorem glv_no_short_of_cert {n lam s t k2 u v : ℤ} (hn : 0 < n)
    (hcert : s + t * lam = k2 * n) (hbez : u * s + v * t = 1)
    (hsabs : 2 ^ 126 < |s|) (hbnd : 2 ^ 126 * |t| + 2 ^ 126 * |s| < n)
    {a b : ℤ} (hne : a ≠ 0 ∨ b ≠ 0) (ha : |a| ≤ 2 ^ 126) (hb : |b| ≤ 2 ^ 126) :
    ¬ n ∣ (a + b * lam) := by
  intro hdvd
  have hdvd2 : n ∣ (a * t - b * s) := by
    have e : a * t - b * s = t * (a + b * lam) - b * (k2 * n) := by rw [← hcert]; ring
    rw [e]; exact dvd_sub (hdvd.mul_left t) ⟨b * k2, by ring⟩
  have hsmall : |a * t - b * s| < n := by
    have key : |a * t - b * s| ≤ |a| * |t| + |b| * |s| := by
      calc |a * t - b * s| = |a * t + -(b * s)| := by rw [sub_eq_add_neg]
        _ ≤ |a * t| + |-(b * s)| := abs_add_le _ _
        _ = |a| * |t| + |b| * |s| := by rw [abs_neg, abs_mul, abs_mul]
    have hbound : |a| * |t| + |b| * |s| ≤ 2 ^ 126 * |t| + 2 ^ 126 * |s| := by gcongr
    linarith
  have hzero : a * t - b * s = 0 := by
    rcases hdvd2 with ⟨c, hc⟩
    by_contra h0
    have hcne : c ≠ 0 := by rintro rfl; simp at hc; exact h0 hc
    have hge : n ≤ |a * t - b * s| := by
      rw [hc, abs_mul, abs_of_pos hn]
      exact le_mul_of_one_le_right hn.le (Int.one_le_abs hcne)
    linarith
  have hat : a * t = b * s := by linarith
  have hsm : a = s * (u * a + v * b) := by linear_combination v * hat - a * hbez
  have htm : b = t * (u * a + v * b) := by linear_combination -u * hat - b * hbez
  have hm0 : u * a + v * b = 0 := by
    by_contra hmne
    have : |s| ≤ |a| := by
      rw [hsm, abs_mul]; exact le_mul_of_one_le_right (abs_nonneg s) (Int.one_le_abs hmne)
    linarith
  rcases hne with h | h
  · exact h (by rw [hsm, hm0, mul_zero])
  · exact h (by rw [htm, hm0, mul_zero])

/-- **No short relation in the Pallas GLV lattice**: for `(a, b) ≠ 0` with
    `|a|, |b| ≤ 2¹²⁶`, `a + b·λ ≢ 0 (mod order)`. The bound is `2¹²⁶`, not `2¹²⁷` — the
    shortest lattice vector has sup-norm `≈ 9.82·10³⁷ ∈ (2¹²⁶, 2¹²⁷)`; `EndoMul` needs
    `< 2¹²⁴`. Keeps the accumulator off `±T`/`±φT` (`hxne`). -/
theorem pallas_glv_no_short_relation {a b : ℤ} (hne : a ≠ 0 ∨ b ≠ 0)
    (ha : |a| ≤ 2 ^ 126) (hb : |b| ≤ 2 ^ 126) :
    ¬ (Pallas.curve.toAffine.order : ℤ) ∣ (a + b * pallas_lam) := by
  rw [pallas_card]
  exact glv_no_short_of_cert (n := (PALLAS_SCALAR_CARD : ℤ)) (lam := pallas_lam)
    (s := -98231058071100081932162823354453065728)
    (t := 98231058071186745657228807397848383489)
    (k2 := 88244855925979294593813989187869077937)
    (u := -9986202145207451063414818209979305552)
    (v := -9986202145198640800203172615810973695)
    (by decide) (by decide) (by decide) (by decide) (by decide) hne ha hb

/-- **No short relation in the Vesta GLV lattice**: for `(a, b) ≠ 0` with
    `|a|, |b| ≤ 2¹²⁶`, `a + b·λ ≢ 0 (mod order)`; the bound is tight for the same
    shortest-vector reason as Pallas. -/
theorem vesta_glv_no_short_relation {a b : ℤ} (hne : a ≠ 0 ∨ b ≠ 0)
    (ha : |a| ≤ 2 ^ 126) (hb : |b| ≤ 2 ^ 126) :
    ¬ (Vesta.curve.toAffine.order : ℤ) ∣ (a + b * vesta_lam) := by
  rw [vesta_card]
  exact glv_no_short_of_cert (n := (PALLAS_BASE_CARD : ℤ)) (lam := vesta_lam)
    (s := -98231058071186745657228807397848383488)
    (t := 98231058071100081932162823354453065729)
    (k2 := 28855319743320701602732952904011762361)
    (u := 28855319743320701602732952904011762361)
    (v := 28855319743346159024713648477422223361)
    (by decide) (by decide) (by decide) (by decide) (by decide) hne ha hb

end Pasta
