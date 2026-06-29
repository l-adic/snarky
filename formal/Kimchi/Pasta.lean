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
`VestaBaseField = PallasScalarField`.

This is the ONLY file in the tree that declares an `axiom`; everything upstream is
`#print axioms`-clean.
-/

namespace Kimchi.Pasta

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta CompElliptic.CurveForms.ShortWeierstrass

/-- TRUSTED INPUT: the Pallas curve's group order is the prime scalar-field cardinality `q`. -/
axiom pallas_card : Pallas.curve.toAffine.order = PALLAS_SCALAR_CARD

/-- TRUSTED INPUT: the Vesta curve's group order is the prime cardinality `p`. -/
axiom vesta_card : Vesta.curve.toAffine.order = PALLAS_BASE_CARD

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
and `φ` acts as multiplication by a scalar `λ` on the group. For each curve these facts — the
eigenvalue relation and the GLV lattice's short-basis bound — are the endomorphism analog of the
point counts above: trusted inputs that discharge `Kimchi.Circuit.EndoMul.endoMul`'s `heig` and
the accumulator non-degeneracy. -/

open WeierstrassCurve.Affine

/-- TRUSTED INPUT: the Pallas base-field endomorphism coefficient `β` (a primitive cube root of
    unity), so `φ(x, y) = (β·x, y)` maps `y² = x³ + 5` to itself. -/
axiom pallas_endo : PallasBaseField

/-- TRUSTED INPUT: the scalar eigenvalue `λ` of the Pallas endomorphism `φ` on the group. -/
axiom pallas_lam : ℤ

/-- **AXIOM (CM).** The Pallas endomorphism `φ(x, y) = (β·x, y)` acts as `[λ]` on the group:
    `φ(P) = [λ]·P`. The defining property of the GLV endomorphism — not Mathlib-provable for the
    abstract curve, true by the Pasta construction (same trusted status as the point counts). It
    discharges `Kimchi.Circuit.EndoMul.endoMul`'s eigenvalue hypothesis `heig`. -/
axiom pallas_eigen {x y : PallasBaseField}
    (h : Pallas.curve.toAffine.Nonsingular x y)
    (h' : Pallas.curve.toAffine.Nonsingular (pallas_endo * x) y) :
    Point.some _ _ h' = pallas_lam • Point.some _ _ h

/-- **AXIOM (GLV short basis — to be discharged later).** No short relation in the Pallas GLV
    lattice: for `(a, b) ≠ 0` with `|a|, |b| < 2¹²⁷`, `a + b·λ ≢ 0 (mod order)`. The shortest
    lattice vector is `≈ √order ≈ 2¹²⁷` (the balance that makes GLV efficient) — a finite
    statement about the concrete `λ`, taken as a trusted input for now; it keeps the EndoMul
    accumulator off `±T`/`±φT` (the `hxne` non-degeneracy). -/
axiom pallas_glv_no_short_relation {a b : ℤ} (hne : a ≠ 0 ∨ b ≠ 0)
    (ha : |a| < 2 ^ 127) (hb : |b| < 2 ^ 127) :
    ¬ (Pallas.curve.toAffine.order : ℤ) ∣ (a + b * pallas_lam)

/-- TRUSTED INPUT: the Vesta base-field endomorphism coefficient `β` (a primitive cube root of
    unity), so `φ(x, y) = (β·x, y)` maps `y² = x³ + 5` to itself. -/
axiom vesta_endo : VestaBaseField

/-- TRUSTED INPUT: the scalar eigenvalue `λ` of the Vesta endomorphism `φ` on the group. -/
axiom vesta_lam : ℤ

/-- **AXIOM (CM).** The Vesta endomorphism `φ(x, y) = (β·x, y)` acts as `[λ]` on the group:
    `φ(P) = [λ]·P` — the defining property of the GLV endomorphism (same trusted status as the
    point counts). It discharges `Kimchi.Circuit.EndoMul.endoMul`'s `heig` at Vesta. -/
axiom vesta_eigen {x y : VestaBaseField}
    (h : Vesta.curve.toAffine.Nonsingular x y)
    (h' : Vesta.curve.toAffine.Nonsingular (vesta_endo * x) y) :
    Point.some _ _ h' = vesta_lam • Point.some _ _ h

/-- **AXIOM (GLV short basis — to be discharged later).** No short relation in the Vesta GLV
    lattice: for `(a, b) ≠ 0` with `|a|, |b| < 2¹²⁷`, `a + b·λ ≢ 0 (mod order)` (shortest vector
    `≈ √order ≈ 2¹²⁷`). Keeps the EndoMul accumulator off `±T`/`±φT` at Vesta. -/
axiom vesta_glv_no_short_relation {a b : ℤ} (hne : a ≠ 0 ∨ b ≠ 0)
    (ha : |a| < 2 ^ 127) (hb : |b| < 2 ^ 127) :
    ¬ (Vesta.curve.toAffine.order : ℤ) ∣ (a + b * vesta_lam)

end Kimchi.Pasta
