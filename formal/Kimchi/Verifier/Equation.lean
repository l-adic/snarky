import Kimchi.Verifier.Linearization
import Kimchi.Index.Aggregate

/-!
# The verifier equation — the honest evaluation record

The bridge between the verifier's scalar side (`Kimchi/Verifier/Linearization.lean`,
adjudicated by value against production in 3a) and Phase B's quotient interface
(`satisfies_of_evalCheck`). This file opens with `evalsOf`: the evaluation record the
honest protocol hands the scalar side — every column read through its interpolant at
`ζ`, the next-row family at `ω·ζ` — stated over the index's own interpolants
(`selectorPoly`/`coeffPoly`/`sigmaPoly`, `columnPoly` of the witness table) so the
bridge identities are naturality squares of the same objects `fullFamily` is built on.
-/

namespace Kimchi.Verifier.Equation

open Polynomial Kimchi.Quotient Kimchi.Index Kimchi.Verifier.Linearization

variable {F : Type*} [Field F] {n : ℕ}

/-- The honest evaluation record at `ζ`: each witness column's interpolant evaluated at
`ζ` (current) and `ω·ζ` (next), the accumulator `z` at both points, the first six
permutation columns, the coefficient columns, and every gate selector — exactly the
`Evals` the deployed verifier combines from the proof, produced here by the index and
tables themselves. -/
noncomputable def evalsOf (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    (z : Polynomial F) (ζ : F) : Evals F :=
  { w := fun c => (columnPoly idx.omega (fun j => wTab j c)).eval ζ
    wOmega := fun c => (columnPoly idx.omega (fun j => wTab j c)).eval (idx.omega * ζ)
    z := z.eval ζ
    zOmega := z.eval (idx.omega * ζ)
    s := fun i => (idx.sigmaPoly ⟨(i : ℕ), by omega⟩).eval ζ
    coeffs := fun c => (columnPoly idx.omega (fun j => idx.coeffTable j c)).eval ζ
    genericSelector := (idx.selectorPoly .generic).eval ζ
    poseidonSelector := (idx.selectorPoly .poseidon).eval ζ
    completeAddSelector := (idx.selectorPoly .completeAdd).eval ζ
    mulSelector := (idx.selectorPoly .varBaseMul).eval ζ
    emulSelector := (idx.selectorPoly .endoMul).eval ζ
    endoScalarSelector := (idx.selectorPoly .endoScalar).eval ζ }

/-- The evaluation environment of the honest record is the polynomial environment
mapped through evaluation at `ζ` — the junction the gate-side naturality squares
plug into. The next-row side is `eval_comp`: `(p.comp (C ω · X)).eval ζ = p.eval (ω·ζ)`. -/
theorem evalEnv_evalsOf (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    (z : Polynomial F) (ζ : F) :
    evalEnv (evalsOf idx wTab z ζ)
      = (polyEnv idx.omega wTab idx.coeffTable).map
          (⇑(aeval ζ : Polynomial F →ₐ[F] F)) := by
  simp only [evalEnv, evalsOf, polyEnv, ArgumentEnv.map]
  refine congrArg₂ (ArgumentEnv.mk _) ?_ rfl
  funext c
  simp only [Function.comp_apply, Polynomial.coe_aeval_eq_eval, Kimchi.Quotient.shift,
    eval_comp, eval_mul, eval_C, eval_X]

end Kimchi.Verifier.Equation
