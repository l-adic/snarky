import Kimchi.Curve
import CompElliptic.CurveForms.ShortWeierstrass

namespace Kimchi.Cycle

open CompElliptic.CurveForms.ShortWeierstrass

/-- A CM (`j = 0`, Pasta-style `y² = x³ + B`) curve, bundling CompElliptic's
    concrete short-Weierstrass curve, its scalar field as the group order, and the
    endomorphism. The curve and its group law are no longer axiomatized: `E : SWCurve F`
    carries proven ellipticity and a genuine `AddCommGroup (SWPoint E)`, so only the
    arithmetic-geometry facts CompElliptic does not prove (the group order, via Schoof,
    and the CM relation) remain as fields. Gate theorems parametrize over `(c : CMCurve F)`. -/
structure CMCurve (F : Type*) [Field F] [DecidableEq F] where
  /-- the curve, as a CompElliptic short-Weierstrass curve `y² = x³ + A x + B`. -/
  E : SWCurve F
  /-- the CM (`j = 0`) condition: `A = 0`, i.e. `y² = x³ + B`. This is what makes the
      coordinate map `φ(x, y) = (β·x, y)` a curve endomorphism. -/
  A_zero : E.A = 0
  /-- the scalar-field cardinality = the group order (a 255-bit prime on Pasta). -/
  order : ℕ
  /-- **AXIOM (Schoof).** The point group has exponent dividing `order`, so scalars
      act through `ℤ/order` (`[n]·P = [n mod order]·P`). For Pasta the group is cyclic
      of *prime* `order`, hence this. -/
  order_smul : ∀ P : SWPoint E, (order : ℤ) • P = 0
  /-- base-field primitive cube root of unity — the endomorphism's `x`-scaling. -/
  beta : F
  beta_cube : beta ^ 3 = 1
  /-- the scalar-field eigenvalue: `φ = [λ]` on the group, with `λ³ ≡ 1 (mod order)`. -/
  lam : ℤ
  /-- **AXIOM (CM).** The coordinate map `φ(x, y) = (β·x, y)` realizes scalar
      multiplication by `λ`: `φ(P) = [λ]·P`. -/
  eigen : ∀ {x y : F} (h : Valid E.A E.B (x, y)) (h' : Valid E.A E.B (beta * x, y)),
    (⟨beta * x, y, h'⟩ : SWPoint E) = lam • (⟨x, y, h⟩ : SWPoint E)

/-- The Pasta two-cycle: two CM curves whose base/scalar fields are reciprocal —
    `E_p / F_p` has order `card F_q`, `E_q / F_q` has order `card F_p`. This is what
    ties an `EndoScalar` computation in one field to an `EndoMul` point-mul on the
    partner curve (whose scalar field is that field), i.e. the genuine top level for
    `endoMul_toField`. -/
structure TwoCycle (Fp Fq : Type*) [Field Fp] [Field Fq] [DecidableEq Fp]
    [DecidableEq Fq] [Fintype Fp] [Fintype Fq] where
  cp : CMCurve Fp
  cq : CMCurve Fq
  /-- **AXIOM (reciprocity).** `|E_p(F_p)| = card F_q`. -/
  recip_p : cp.order = Fintype.card Fq
  /-- **AXIOM (reciprocity).** `|E_q(F_q)| = card F_p`. -/
  recip_q : cq.order = Fintype.card Fp

/-- Scalars act through `ℤ/order`: `[n]·P` depends only on `n mod order`. The first
    real consequence of the order axiom — the basis for the scalar-field re-statements. -/
theorem zsmul_mod (F : Type*) [Field F] [DecidableEq F] (c : CMCurve F)
    (n : ℤ) (P : SWPoint c.E) :
    (n % (c.order : ℤ)) • P = n • P := by
  have h : n • P
      = (n % (c.order : ℤ)) • P + (c.order : ℤ) • ((n / (c.order : ℤ)) • P) := by
    rw [← mul_smul, ← add_smul, Int.emod_add_mul_ediv]
  rw [h, c.order_smul, _root_.add_zero]

end Kimchi.Cycle
