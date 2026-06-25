import Kimchi.Curve

namespace Kimchi.Cycle

open WeierstrassCurve.Affine

/-- A CM (`j = 0`, Pasta-style `y² = x³ + a₆`) curve, bundling its coordinate field,
    its scalar field as the group order, and the endomorphism. Gate theorems
    parametrize over `(c : CMCurve F)`. -/
structure CMCurve (F : Type*) [Field F] [DecidableEq F] where
  /-- the curve (short Weierstrass). -/
  W : WeierstrassCurve.Affine F
  short : IsShortShape W
  /-- the scalar-field cardinality = the group order (a 255-bit prime on Pasta). -/
  order : ℕ
  /-- **AXIOM (Schoof).** The point group has exponent dividing `order`, so scalars
      act through `ℤ/order` (`[n]·P = [n mod order]·P`). For Pasta the group is cyclic
      of *prime* `order`, hence this. -/
  order_smul : ∀ P : W.Point, (order : ℤ) • P = 0
  /-- base-field primitive cube root of unity — the endomorphism's `x`-scaling. -/
  beta : F
  beta_cube : beta ^ 3 = 1
  /-- the scalar-field eigenvalue: `φ = [λ]` on the group, with `λ³ ≡ 1 (mod order)`. -/
  lam : ℤ
  /-- **AXIOM (CM).** The coordinate map `φ(x,y) = (β·x, y)` realizes scalar
      multiplication by `λ`: `φ(P) = [λ]·P`. -/
  eigen : ∀ {x y : F} (h : W.Nonsingular x y) (h' : W.Nonsingular (beta * x) y),
    Point.some _ _ h' = lam • Point.some _ _ h

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
    (n : ℤ) (P : c.W.Point) :
    (n % (c.order : ℤ)) • P = n • P := by
  have h : n • P
      = (n % (c.order : ℤ)) • P + (c.order : ℤ) • ((n / (c.order : ℤ)) • P) := by
    rw [← mul_smul, ← add_smul, Int.emod_add_mul_ediv]
  rw [h, c.order_smul, add_zero]

end Kimchi.Cycle
