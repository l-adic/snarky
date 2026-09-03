import CompPoly.Multivariate.MvPolyEquiv.Instances
import CompPoly.Multivariate.MvPolyEquiv.Eval
import CompPoly.Multivariate.Operations

/-!
# A computable `Algebra` on CompPoly's multivariate polynomials

The reflection route for the linearization runs the gate constraints at
`R := CMvPolynomial n (ZMod p)` and decides the resulting polynomial identity by
computation. `Kimchi.Lift.Argument.constraints` is already polymorphic in exactly that
way — `∀ {R} [CommRing R] [Algebra F R], ArgumentEnv R → List R` — so the only thing
standing in the way is the `Algebra` instance.

CompPoly ships one (`CPoly.CMvPolynomial.instAlgebra`), but it is `noncomputable`, and a
noncomputable instance in the term is fatal here: the whole point is to run the
computation. The obstruction is incidental rather than essential — the instance's DATA is
`C`, which computes; only its proof obligations are discharged through the noncomputable
`polyEquiv`, and proofs are erased at compile time.

So this module re-derives the same instance without the `noncomputable` marker, reusing
CompPoly's proof fields verbatim. It is definitionally the upstream instance; it merely
carries compiled code. Priority is raised so that instance search prefers it and code
generation never reaches the upstream one.
-/

namespace Pickles.Reflect

open CPoly CPoly.CMvPolynomial

variable {n : ℕ} {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]

/-- `C` as a ring homomorphism, computably. The fields are CompPoly's own proofs; only the
`noncomputable` marker is dropped. -/
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

`Kimchi.Lift.Argument.constraints_map` — the naturality square that carries a gate's
constraint list from one ring to another — is stated along an `F`-ALGEBRA homomorphism.
CompPoly supplies evaluation as a bare function (`aeval`) and as a ring homomorphism
(`eval₂Hom`); this packages the two together with `aeval_C`, which is exactly the
`commutes'` obligation.

Unlike the instance above this may be noncomputable: it appears only in proofs, never in
the certificate's computation. -/

/-- Evaluation at a point, as an `R`-algebra homomorphism out of the polynomial algebra.
`aevalAlgHom_X` is its computation rule on variables; on constants `commutes` serves. -/
noncomputable def aevalAlgHom {n : ℕ} {σ : Type*} [CommRing σ] [Algebra R σ]
    (f : Fin n → σ) : CMvPolynomial n R →ₐ[R] σ :=
  { eval₂Hom (algebraMap R σ) f with
    commutes' := fun c => by simpa using aeval_C (n := n) f c }

@[simp] theorem aevalAlgHom_X {n : ℕ} {σ : Type*} [CommRing σ] [Algebra R σ]
    (f : Fin n → σ) (i : Fin n) : aevalAlgHom (R := R) f (CMvPolynomial.X i) = f i :=
  aeval_X f i

end Pickles.Reflect
