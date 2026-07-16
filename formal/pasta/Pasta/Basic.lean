import Pasta.Curve
import Pasta.Constants
import Pasta.Endo
import CompElliptic.Curves.Pasta
import CompElliptic.Curves.PastaOrder
import CompElliptic.Fields.Pasta

/-!
# The Pasta curves' group orders

The Pallas group order is the prime `q = PALLAS_SCALAR_CARD` and the Vesta group order is the
prime `p = PALLAS_BASE_CARD` (the Pasta cycle: each curve's order is the other's base-field
size). Both are obtained from Hasse's bound `#E(𝔽) ∈ [q+1−2√q, q+1+2√q]` and the point order of a
generator `G` (`[q]·G = 𝒪`): the bound leaves the point order as the only in-interval
possibility. Hasse's bound is the one input Mathlib cannot supply, so it is an axiom
(`pallas_hasse`/`vesta_hasse`); everything else is discharged by `CompElliptic.Curves.PastaOrder`.
-/

namespace Pasta

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta CompElliptic.CurveForms.ShortWeierstrass
  CompElliptic.CurveOrder

/-- **AXIOM (Hasse).** The Pallas group order lies in the Hasse interval
    `[q+1−2√q, q+1+2√q]` (`#E(𝔽) ∈ hasseInterval (#𝔽)`). -/
axiom pallas_hasse : HasseBound Pallas.curve

/-- **AXIOM (Hasse).** The Vesta group order lies in the Hasse interval. -/
axiom vesta_hasse : HasseBound Vesta.curve

/-- The Pallas group order is the prime scalar-field cardinality `q`. -/
theorem pallas_card : Pallas.curve.toAffine.order = PALLAS_SCALAR_CARD := by
  have h := Pallas.card_eq pallas_hasse
  rw [SWPoint.card_eq_point Pallas.curve] at h
  exact h

/-- The Vesta group order is the prime cardinality `p`. -/
theorem vesta_card : Vesta.curve.toAffine.order = PALLAS_BASE_CARD := by
  have h := Vesta.card_eq vesta_hasse
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

/-! ## The Pasta GLV endomorphisms — the trusted inputs for `EndoMul`

Both Pasta curves `y² = x³ + 5` carry the GLV endomorphism `φ(x, y) = (β·x, y)`, where `β` is a
primitive cube root of unity in the base field (so `(β·x)³ = x³` keeps the point on the curve)
and `φ` acts as multiplication by a scalar `λ` on the group. The coefficient `β` and the
eigenvalue relation `φ(P) = [λ]·P` are trusted inputs (the endomorphism analog of the point
counts), discharging `Kimchi.Circuit.EndoMul.endoMul`'s `heig`. The GLV lattice's short-basis
bound, by contrast, is **proved** here (`{pallas,vesta}_glv_no_short_relation`, from a concrete
reduced-basis certificate) — it is the accumulator non-degeneracy fact. -/

open WeierstrassCurve.Affine

/-- **No short relation in a rank-2 GLV lattice, from a reduced-basis certificate.** If `(s, t)`
    lies in the lattice `{(a,b) : a + b·λ ≡ 0 (mod n)}` (`s + t·λ = k₂·n`), is primitive
    (`u·s + v·t = 1`), has `|s| > 2¹²⁶`, and the box `[−2¹²⁶, 2¹²⁶]²` fits below the covolume
    (`2¹²⁶·(|s|+|t|) < n`), then no nonzero `(a,b)` in that box lies in the lattice. Proof: the
    cross product `a·t − b·s` is divisible by `n` yet `|a·t − b·s| < n`, so it is `0`; primitivity
    makes `(a,b)` a multiple of `(s,t)`, ruled out by `|a| ≤ 2¹²⁶ < |s|`. -/
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

/-- The Pallas endomorphism `φ(x, y) = (β·x, y)` acts as `[λ]` on the group: `φ(P) = [λ]·P`.
    PROVED (`Pasta/Endo.lean`): `φ` is a group homomorphism (the addition formulas are
    homogeneous under the `(u², u³)`-rescaling with `u = β⁻¹`), the group is cyclic of prime
    order under the Hasse axiom, and the `native_decide` certificate `pallas_lam_nsmul_Gpt`
    anchors the eigenvalue at the generator. Discharges `Kimchi.Circuit.EndoMul.endoMul`'s
    hypothesis `heig`; trust = the Hasse axiom + the `native_decide` certificates. -/
theorem pallas_eigen {x y : Fp}
    (h : Pallas.curve.toAffine.Nonsingular x y)
    (h' : Pallas.curve.toAffine.Nonsingular (pallas_endo * x) y) :
    Point.some _ _ h' = pallas_lam • Point.some _ _ h :=
  pallas_eigen_of_hasse pallas_hasse h h'

/-- **No short relation in the Pallas GLV lattice.** For `(a, b) ≠ 0` with `|a|, |b| ≤ 2¹²⁶`,
    `a + b·λ ≢ 0 (mod order)`. Proved from the reduced-basis certificate via `glv_no_short_of_cert`
    (`order = PALLAS_SCALAR_CARD` by `pallas_card`). The bound is `2¹²⁶`, not `2¹²⁷`: the shortest
    lattice vector has sup-norm `≈ 9.82·10³⁷ ∈ (2¹²⁶, 2¹²⁷)`, so `2¹²⁷` would be *false* (EndoMul
    only ever needs `< 2¹²⁴`). Keeps the accumulator off `±T`/`±φT` (`hxne`). -/
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

/-- The Vesta endomorphism acts as `[λ]`: `φ(P) = [λ]·P` — PROVED, the Vesta twin of
    `pallas_eigen` (see its docstring for the derivation and trust accounting). -/
theorem vesta_eigen {x y : Fq}
    (h : Vesta.curve.toAffine.Nonsingular x y)
    (h' : Vesta.curve.toAffine.Nonsingular (vesta_endo * x) y) :
    Point.some _ _ h' = vesta_lam • Point.some _ _ h :=
  vesta_eigen_of_hasse vesta_hasse h h'

/-- **No short relation in the Vesta GLV lattice.** For `(a, b) ≠ 0` with `|a|, |b| ≤ 2¹²⁶`,
    `a + b·λ ≢ 0 (mod order)`. Proved from the reduced-basis certificate (`order = PALLAS_BASE_CARD`
    by `vesta_card`); bound `2¹²⁶` for the same shortest-vector reason as Pallas. -/
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
