import CompPoly.Multivariate.MvPolyEquiv.Instances
import CompPoly.Multivariate.MvPolyEquiv.Eval
import CompPoly.Multivariate.Operations

/-!
# A computable `Algebra` on CompPoly's multivariate polynomials

The reflection route runs the gate constraints at `R := CMvPolynomial n (ZMod p)` and
decides the resulting polynomial identity by computation. CompPoly's `Algebra` instance is
`noncomputable`, which a compiled decision cannot use, though only its proof fields go
through the noncomputable `polyEquiv`; its data is `C`, which computes. This module
re-derives the same instance, reusing CompPoly's proofs, without the marker.

## Main definitions

* `instAlgebraComp`: the polynomial algebra over its coefficient ring, computably.
* `aevalAlgHom`: evaluation at a point as an `R`-algebra homomorphism, which CompPoly
  supplies only as a function and as a ring homomorphism.
-/

namespace Pickles.Reflect

open CPoly CPoly.CMvPolynomial

variable {n : ℕ} {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]

/-- `C` as a ring homomorphism, computably. -/
private def CRingHomComp : R →+* CMvPolynomial n R where
  toFun := C
  map_one' := CRingHom.map_one'
  map_mul' := CRingHom.map_mul'
  map_zero' := CRingHom.map_zero'
  map_add' := CRingHom.map_add'

/-- The polynomial algebra over its coefficient ring, computably. -/
instance (priority := high) instAlgebraComp : Algebra R (CMvPolynomial n R) :=
  Algebra.mk (toSMul := instSMul) CRingHomComp (fun r x => mul_comm (C r) x) (fun _ _ => rfl)

/-! ## Evaluation as an algebra homomorphism

`Kimchi.Lift.Argument.constraints_map` is stated along an `F`-algebra homomorphism; this
packages CompPoly's `eval₂Hom` with `aeval_C` as its `commutes'` field. -/

/-- Evaluation at a point, as an `R`-algebra homomorphism out of the polynomial algebra. -/
noncomputable def aevalAlgHom {n : ℕ} {σ : Type*} [CommRing σ] [Algebra R σ]
    (f : Fin n → σ) : CMvPolynomial n R →ₐ[R] σ :=
  { eval₂Hom (algebraMap R σ) f with
    commutes' := fun c => by simpa using aeval_C (n := n) f c }

@[simp] theorem aevalAlgHom_X {n : ℕ} {σ : Type*} [CommRing σ] [Algebra R σ]
    (f : Fin n → σ) (i : Fin n) : aevalAlgHom (R := R) f (CMvPolynomial.X i) = f i :=
  aeval_X f i

end Pickles.Reflect
