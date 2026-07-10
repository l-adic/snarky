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

/-! ## The gate side

The α-power sum of the gate members, evaluated at `ζ`, is the closed-form
`gateLinearization` at the honest record (minus the public interpolant, which the
member at slot `0` carries): per gate, evaluation passes through the constraint list
by the `Argument` naturality square at `aeval ζ` (through the junction
`evalEnv_evalsOf`), and the `getD`-indexed pool sum is `alphaCombo` by
`alphaCombo_eq_sum_getD`. -/

/-- Evaluation commutes with defaulted indexing (the default `0` evaluates to `0`). -/
theorem eval_getD (ζ : F) :
    ∀ (L : List (Polynomial F)) (k : ℕ),
      (L.getD k 0).eval ζ = (L.map (Polynomial.eval ζ)).getD k 0
  | [], _ => by simp
  | _ :: _, 0 => rfl
  | _ :: t, k + 1 => eval_getD ζ t k

/-- Any argument's polynomial constraint list, evaluated at `ζ`, is its field-level
list at the honest record — the naturality square at `aeval ζ`, pasted onto the
junction `evalEnv_evalsOf`. -/
theorem constraints_map_evalsOf (A : Argument F) (idx : Index F n)
    (wTab : Fin n → Fin 15 → F) (z : Polynomial F) (ζ : F) :
    (A.constraints (polyEnv idx.omega wTab idx.coeffTable)).map (Polynomial.eval ζ)
      = A.constraints (evalEnv (evalsOf idx wTab z ζ)) := by
  rw [evalEnv_evalsOf]
  have h := A.constraints_map (aeval ζ : Polynomial F →ₐ[F] F)
    (polyEnv idx.omega wTab idx.coeffTable)
  simpa [Polynomial.coe_aeval_eq_eval] using h

/-- A sum over the gate types, in enumeration order. -/
theorem sum_gateType {M : Type*} [AddCommMonoid M] (f : GateType → M) :
    ∑ g : GateType, f g
      = f .zero + f .generic + f .poseidon + f .completeAdd + f .varBaseMul
        + f .endoMul + f .endoScalar := by
  rw [show (Finset.univ : Finset GateType)
    = {.zero, .generic, .poseidon, .completeAdd, .varBaseMul, .endoMul, .endoScalar}
    from by decide]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.sum_singleton, reduceCtorEq, or_self, not_false_eq_true]
  abel

/-- **The gate side of the verifier equation.** The shared-pool α-sum of the gate
members at `ζ` is the closed-form gate linearization at the honest record, minus the
public interpolant. -/
theorem gateMember_sum_eval [DecidableEq F] [NeZero n] (idx : Index F n)
    (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin 15 → F) (z : Polynomial F) (ζ α : F) :
    ∑ k ∈ Finset.range Index.gateAlphaCount, α ^ k * (idx.gateMember pub wTab k).eval ζ
      = gateLinearization idx.endoBase α (evalsOf idx wTab z ζ)
          - (idx.pubPoly pub).eval ζ := by
  -- split each member into its selector-weighted pool term and the public correction
  have hmem : ∀ k, α ^ k * (idx.gateMember pub wTab k).eval ζ
      = (∑ g : GateType, (idx.selectorPoly g).eval ζ
          * (α ^ k * ((idx.gateConstraints wTab g).map (Polynomial.eval ζ)).getD k 0))
        - (if k = 0 then (idx.pubPoly pub).eval ζ else 0) := by
    intro k
    rw [Index.gateMember, eval_sub, eval_finsetSum, apply_ite (Polynomial.eval ζ),
      eval_zero, mul_sub, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun g _ => by
        rw [eval_mul, eval_getD]
        simp only [Index.selectorPoly]
        ring
    · by_cases hk : k = 0 <;> simp [hk]
  simp only [hmem, Finset.sum_sub_distrib]
  -- the public correction survives only at slot 0
  rw [Finset.sum_ite_eq' (Finset.range Index.gateAlphaCount) 0
      (fun _ => (idx.pubPoly pub).eval ζ),
    if_pos (Finset.mem_range.mpr (by norm_num [Index.gateAlphaCount]))]
  congr 1
  -- swap the sums and collapse each gate's pool sum to its Horner combo
  rw [Finset.sum_comm]
  have hgate : ∀ g : GateType,
      ∑ k ∈ Finset.range Index.gateAlphaCount, (idx.selectorPoly g).eval ζ
          * (α ^ k * ((idx.gateConstraints wTab g).map (Polynomial.eval ζ)).getD k 0)
        = (idx.selectorPoly g).eval ζ
            * alphaCombo α ((idx.gateConstraints wTab g).map (Polynomial.eval ζ)) := by
    intro g
    rw [← Finset.mul_sum, alphaCombo_eq_sum_getD α _ Index.gateAlphaCount
      (by simpa using idx.gateConstraints_length_le wTab g)]
  rw [Finset.sum_congr rfl fun g _ => hgate g, sum_gateType]
  -- the seven gate terms: zero contributes nothing, the six live gates are the
  -- closed-form summands via the naturality square
  rw [gateLinearization]
  simp only [Index.gateConstraints]
  rw [show Gate.Poseidon.constraints (Poseidon.rcPoly idx.omega idx.coeffTable)
        (Poseidon.polyWitness idx.omega wTab)
      = (Kimchi.Quotient.Poseidon.argument (F := F)).constraints
          (polyEnv idx.omega wTab idx.coeffTable) from rfl,
    show Gate.AddComplete.constraints (AddComplete.polyWitness idx.omega wTab)
      = (Kimchi.Quotient.AddComplete.argument (F := F)).constraints
          (polyEnv idx.omega wTab idx.coeffTable) from rfl,
    show Gate.VarBaseMul.constraints (VarBaseMul.polyWitness idx.omega wTab)
      = (Kimchi.Quotient.VarBaseMul.argument (F := F)).constraints
          (polyEnv idx.omega wTab idx.coeffTable) from rfl,
    show Gate.EndoMul.constraints (C idx.endoBase) (EndoMul.polyWitness idx.omega wTab)
      = (Kimchi.Quotient.EndoMul.argument idx.endoBase).constraints
          (polyEnv idx.omega wTab idx.coeffTable) from rfl,
    show Gate.EndoScalar.constraints (EndoScalar.polyWitness idx.omega wTab) (F := F)
      = (Kimchi.Quotient.EndoScalar.argument (F := F)).constraints
          (polyEnv idx.omega wTab idx.coeffTable) from rfl]
  rw [constraints_map_evalsOf (genericArgument (F := F)) idx wTab z ζ,
    constraints_map_evalsOf (Kimchi.Quotient.Poseidon.argument (F := F)) idx wTab z ζ,
    constraints_map_evalsOf (Kimchi.Quotient.AddComplete.argument (F := F)) idx wTab z ζ,
    constraints_map_evalsOf (Kimchi.Quotient.VarBaseMul.argument (F := F)) idx wTab z ζ,
    constraints_map_evalsOf (Kimchi.Quotient.EndoMul.argument idx.endoBase) idx wTab z ζ,
    constraints_map_evalsOf (Kimchi.Quotient.EndoScalar.argument (F := F)) idx wTab z ζ]
  rw [show alphaCombo α (List.map (Polynomial.eval ζ) ([] : List (Polynomial F))) = 0
    from rfl, mul_zero, zero_add]
  rfl

end Kimchi.Verifier.Equation
