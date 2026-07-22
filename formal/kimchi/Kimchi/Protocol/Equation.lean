import Kimchi.Protocol.Accepts
import Kimchi.Index.Degree

/-!
# The verifier equation and the honest evaluation record

The bridge between the verifier's scalar side and the quotient interface. `evalsOf` is
the evaluation record the honest protocol hands the scalar side: every column read
through its interpolant at `ζ`, the next-row family at `ω·ζ`. Stating it over the
circuit's own interpolants makes the bridge identities naturality squares of the very
objects the aggregate family is built on.
-/
namespace Kimchi.Protocol.Equation

open Polynomial Kimchi.Lift Kimchi.Index Kimchi.Protocol.Linearization
open Kimchi.GrandProduct
open Kimchi.Lift.Gate

variable {F : Type*} [Field F] {n : ℕ}

/-- The honest evaluation record at `ζ`: each witness column's interpolant at `ζ` and
`ω·ζ`, the accumulator at both points, the first six permutation columns, the coefficient
columns, and every gate selector — the record a verifier reads off a proof, here produced
by the circuit and its tables. -/
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
private theorem evalEnv_evalsOf (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    (z : Polynomial F) (ζ : F) :
    evalEnv (evalsOf idx wTab z ζ)
      = (polyEnv idx.omega wTab idx.coeffTable).map
          (⇑(aeval ζ : Polynomial F →ₐ[F] F)) := by
  simp only [evalEnv, evalsOf, polyEnv, ArgumentEnv.map]
  refine congrArg₂ (ArgumentEnv.mk _) ?_ rfl
  funext c
  simp only [Function.comp_apply, Polynomial.coe_aeval_eq_eval, Kimchi.shift,
    eval_comp, eval_mul, eval_C, eval_X]

/-! ## Column extraction

Binding delivers *polynomials* behind the witness commitments, while satisfaction and
the evaluation record speak *tables*. `extractTable` reads the table off the bound
polynomials; the honest record at that table evaluates those polynomials themselves, so
the claimed evaluations binding certifies are exactly the record's fields. -/

/-- The witness table read off bound column polynomials: `wTab j c := W_c(ω^j)` — the
table the soundness conclusion exports. -/
def extractTable (ω : F) (W : Fin 15 → Polynomial F) : Fin n → Fin 15 → F :=
  fun j c => (W c).eval (ω ^ (j : ℕ))

/-- The honest record at the extracted table evaluates the bound polynomials: the
current-row field at column `c` is `W_c(ζ)` — binding's claimed evaluation. -/
theorem evalsOf_extractTable_w [NeZero n] (idx : Index F n)
    (W : Fin 15 → Polynomial F) (hW : ∀ c, (W c).natDegree < n)
    (z : Polynomial F) (ζ : F) (c : Fin 15) :
    (evalsOf idx (extractTable idx.omega W) z ζ).w c = (W c).eval ζ := by
  show (columnPoly idx.omega fun j => (W c).eval (idx.omega ^ (j : ℕ))).eval ζ = _
  rw [columnPoly_eval_self idx.omega_prim (Nat.pos_of_neZero n) (W c) (hW c)]

/-- The next-row field at column `c` is `W_c(ωζ)` — binding's claimed evaluation at
the shifted point. -/
theorem evalsOf_extractTable_wOmega [NeZero n] (idx : Index F n)
    (W : Fin 15 → Polynomial F) (hW : ∀ c, (W c).natDegree < n)
    (z : Polynomial F) (ζ : F) (c : Fin 15) :
    (evalsOf idx (extractTable idx.omega W) z ζ).wOmega c
      = (W c).eval (idx.omega * ζ) := by
  show (columnPoly idx.omega fun j => (W c).eval (idx.omega ^ (j : ℕ))).eval
      (idx.omega * ζ) = _
  rw [columnPoly_eval_self idx.omega_prim (Nat.pos_of_neZero n) (W c) (hW c)]

/-! ## The gate side

The α-power sum of the gate members, evaluated at `ζ`, is the closed-form
`gateLinearization` at the honest record (minus the public interpolant, which the
member at slot `0` carries): per gate, evaluation passes through the constraint list
by the `Argument` naturality square at `aeval ζ` (through the junction
`evalEnv_evalsOf`), and the `getD`-indexed pool sum is `alphaCombo` by
`alphaCombo_eq_sum_getD`. -/

/-- Evaluation commutes with defaulted indexing (the default `0` evaluates to `0`). -/
private theorem eval_getD (ζ : F) :
    ∀ (L : List (Polynomial F)) (k : ℕ),
      (L.getD k 0).eval ζ = (L.map (Polynomial.eval ζ)).getD k 0
  | [], _ => by simp
  | _ :: _, 0 => rfl
  | _ :: t, k + 1 => eval_getD ζ t k

/-- Any argument's polynomial constraint list, evaluated at `ζ`, is its field-level
list at the honest record — the naturality square at `aeval ζ`, pasted onto the
junction `evalEnv_evalsOf`. -/
private theorem constraints_map_evalsOf (A : Argument F) (idx : Index F n)
    (wTab : Fin n → Fin 15 → F) (z : Polynomial F) (ζ : F) :
    (A.constraints (polyEnv idx.omega wTab idx.coeffTable)).map (Polynomial.eval ζ)
      = A.constraints (evalEnv (evalsOf idx wTab z ζ)) := by
  rw [evalEnv_evalsOf]
  have h := A.constraints_map (aeval ζ : Polynomial F →ₐ[F] F)
    (polyEnv idx.omega wTab idx.coeffTable)
  simpa [Polynomial.coe_aeval_eq_eval] using h

/-- A sum over the gate types, in enumeration order. -/
private theorem sum_gateType {M : Type*} [AddCommMonoid M] (f : GateType → M) :
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
private theorem gateMember_sum_eval [DecidableEq F] [NeZero n] (idx : Index F n)
    (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin 15 → F) (z : Polynomial F) (ζ α : F) :
    ∑ k ∈ Finset.range Index.gateAlphaCount, α ^ k * (idx.gateMember pub wTab k).eval ζ
      = gateLinearization idx.endoBase idx.mds α (evalsOf idx wTab z ζ)
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
  rw [show Gate.Poseidon.constraints (idx.mds.map C)
        (Poseidon.rcPoly idx.omega idx.coeffTable) (Poseidon.polyWitness idx.omega wTab)
      = (Poseidon.argument idx.mds).constraints
          (polyEnv idx.omega wTab idx.coeffTable) from rfl,
    show Gate.AddComplete.constraints (AddComplete.polyWitness idx.omega wTab)
      = (AddComplete.argument (F := F)).constraints
          (polyEnv idx.omega wTab idx.coeffTable) from rfl,
    show Gate.VarBaseMul.constraints (VarBaseMul.polyWitness idx.omega wTab)
      = (VarBaseMul.argument (F := F)).constraints
          (polyEnv idx.omega wTab idx.coeffTable) from rfl,
    show Gate.EndoMul.constraints (C idx.endoBase) (EndoMul.polyWitness idx.omega wTab)
      = (EndoMul.argument idx.endoBase).constraints
          (polyEnv idx.omega wTab idx.coeffTable) from rfl,
    show Gate.EndoScalar.constraints (EndoScalar.polyWitness idx.omega wTab) (F := F)
      = (EndoScalar.argument (F := F)).constraints
          (polyEnv idx.omega wTab idx.coeffTable) from rfl]
  rw [constraints_map_evalsOf (Generic.argument (F := F)) idx wTab z ζ,
    constraints_map_evalsOf (Poseidon.argument idx.mds) idx wTab z ζ,
    constraints_map_evalsOf (AddComplete.argument (F := F)) idx wTab z ζ,
    constraints_map_evalsOf (VarBaseMul.argument (F := F)) idx wTab z ζ,
    constraints_map_evalsOf (EndoMul.argument idx.endoBase) idx wTab z ζ,
    constraints_map_evalsOf (EndoScalar.argument (F := F)) idx wTab z ζ]
  rw [show alphaCombo α (List.map (Polynomial.eval ζ) ([] : List (Polynomial F))) = 0
    from rfl, mul_zero, zero_add]
  rfl

/-! ## The permutation vanishing mask, as a polynomial evaluation

`zkpmEval` is the verifier's point-value form of the masked-row product; it is the
evaluation at `ζ` of the quotient layer's `Permutation.zkpm` interpolant. Both range over
the same masked window `[n − zkRows, n)`, so the identity is `eval_prod` on that `Ico`. -/

/-- The verifier's masked-row product `zkpmEval` is the evaluation of the quotient's
`Permutation.zkpm` polynomial at `ζ`. -/
private theorem zkpmEval_eq (nn zkRows : ℕ) (ω ζ : F) :
    zkpmEval nn zkRows ω ζ = (Permutation.zkpm ω nn zkRows).eval ζ := by
  simp only [zkpmEval, Permutation.zkpm, Polynomial.eval_prod, eval_sub, eval_X, eval_C]

/-! ## The witness-column bridge

The σ-side products in `ftEval0` read witness columns through the `Evals` record
(`e.w ⟨i, _⟩`), while the quotient's `Permutation.constraints` reads them through the
index's `permWitnessPoly`. Both are the same `columnPoly` interpolant evaluated at `ζ`;
this is the tiny naturality square that lets the σ-side recurrence recombine. -/

/-- The `permWitnessPoly` interpolant of column `col`, evaluated at `ζ`, is the honest
record's witness value in that column. -/
private theorem eval_permWitnessPoly_eq_w [NeZero n] (idx : Index F n)
    (wTab : Fin n → Fin 15 → F) (z : Polynomial F) (ζ : F) (col : Fin 7)
    (h : (col : ℕ) < 15) :
    (idx.permWitnessPoly wTab col).eval ζ = (evalsOf idx wTab z ζ).w ⟨(col : ℕ), h⟩ := by
  rfl

/-! ## The σ-side recurrence recombination

At the first permutation alpha, the `permScalar · σ₆(ζ)` term and `ftEval0`'s σ-side and
shift-side products recombine into that alpha times the quotient's first permutation
constraint at the honest record. -/

/-- **σ-side of the verifier equation.** The permutation scalar against `σ₆(ζ)`, minus
`ftEval0`'s σ-side product against `z(ζω)`, plus its shift-side product against `z(ζ)`,
all at `α²¹·zkpm(ζ)`, equals `α²¹` times the quotient's `0`-th permutation constraint at
the honest record. -/
private theorem permMember_eval [NeZero n] (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    (z : Polynomial F) (ζ β γ α : F) (σ : Fin 7 → Polynomial F)
    (hσ : ∀ i : Fin 6, (σ ⟨(i : ℕ), by omega⟩).eval ζ = (evalsOf idx wTab z ζ).s i)
    (r₀ r₁ : Fin n) :
    permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (evalsOf idx wTab z ζ)
        * (σ 6).eval ζ
      - ((evalsOf idx wTab z ζ).w 6 + γ) * (evalsOf idx wTab z ζ).zOmega
          * α ^ 21 * zkpmEval n idx.zkRows idx.omega ζ
          * ∏ i : Fin 6, (β * (evalsOf idx wTab z ζ).s i
              + (evalsOf idx wTab z ζ).w ⟨(i : ℕ), by omega⟩ + γ)
      + (α ^ 21 * zkpmEval n idx.zkRows idx.omega ζ * (evalsOf idx wTab z ζ).z)
          * ∏ i : Fin 7, (γ + β * ζ * idx.shifts i
              + (evalsOf idx wTab z ζ).w ⟨(i : ℕ), by omega⟩)
      = α ^ 21 * (Permutation.constraints idx.omega idx.zkRows z
          (idx.permWitnessPoly wTab) σ idx.shifts β γ r₀ r₁ 0).eval ζ := by
  rw [zkpmEval_eq]
  simp only [Permutation.constraints, Matrix.cons_val_zero, Permutation.shiftSide,
    Permutation.sigmaSide, Permutation.shiftRow, permScalar, eval_mul, eval_sub,
    eval_prod, eval_add, eval_comp, eval_C, eval_X]
  -- rewrite the shift-side 7-product into the goal's syntactic form
  have hshift : (∏ x : Fin 7,
        (eval ζ (idx.permWitnessPoly wTab x) + γ + β * idx.shifts x * ζ))
      = ∏ i : Fin 7, (γ + β * ζ * idx.shifts i
          + (evalsOf idx wTab z ζ).w ⟨(i : ℕ), by omega⟩) :=
    Finset.prod_congr rfl fun x _ => by
      rw [eval_permWitnessPoly_eq_w idx wTab z ζ x (by omega)]; ring
  -- split the σ-side 7-product off its last factor
  have hsigma : (∏ x : Fin 7,
        (eval ζ (idx.permWitnessPoly wTab x) + γ + β * eval ζ (σ x)))
      = (∏ i : Fin 6, (β * (evalsOf idx wTab z ζ).s i
            + (evalsOf idx wTab z ζ).w ⟨(i : ℕ), by omega⟩ + γ))
          * ((evalsOf idx wTab z ζ).w 6 + γ + β * eval ζ (σ 6)) := by
    rw [Fin.prod_univ_castSucc]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show (i.castSucc : Fin 7) = (⟨(i : ℕ), by omega⟩ : Fin 7) from rfl,
      eval_permWitnessPoly_eq_w idx wTab z ζ ⟨(i : ℕ), by omega⟩ (by omega), hσ i]
    ring
  rw [hshift, hsigma,
    show (∏ i : Fin 6, (γ + β * (evalsOf idx wTab z ζ).s i
            + (evalsOf idx wTab z ζ).w ⟨(i : ℕ), by omega⟩))
        = ∏ i : Fin 6, (β * (evalsOf idx wTab z ζ).s i
            + (evalsOf idx wTab z ζ).w ⟨(i : ℕ), by omega⟩ + γ) from
      Finset.prod_congr rfl fun i _ => by ring]
  simp only [evalsOf, mul_comm idx.omega ζ]
  ring

/-! ## The accumulator boundary pins

`ftEval0`'s `boundary` let is a quotient of the two Lagrange pins, at `α²²` (row `0`,
node `ω⁰ = 1`) and `α²³` (row `n − zkRows`, node `ω^(n−zkRows)`). Away from those two
nodes (`ζ ≠ 1`, `ζ ≠ ω^(n−zkRows)`) the division is exact and the boundary equals the
signed sum of the two quotient permutation-boundary members `(z − 1)·lagNumer r`, via
`lagNumer_mul_sub`. -/

/-- **Boundary side of the verifier equation.** `ftEval0`'s boundary quotient equals
`−α²²·m₁(ζ) − α²³·m₂(ζ)`, the two accumulator-boundary permutation members `(z−1)·lagNumer`
at rows `0` and `n − zkRows`, under `ζ ≠ 1` and `ζ ≠ ω^(n−zkRows)`. -/
private theorem boundary_eval [NeZero n] (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    (z : Polynomial F) (ζ α : F)
    (hζ₁ : ζ ≠ 1) (hζb : ζ ≠ idx.omega ^ (n - idx.zkRows)) :
    ((ζ ^ n - 1) * α ^ 22 * (ζ - idx.omega ^ (n - idx.zkRows))
          + (ζ ^ n - 1) * α ^ 23 * (ζ - 1)) * (1 - (evalsOf idx wTab z ζ).z)
        / ((ζ - idx.omega ^ (n - idx.zkRows)) * (ζ - 1))
      = -(α ^ 22 * ((z - 1) * Permutation.lagNumer idx.omega
              (⟨0, Nat.pos_of_neZero n⟩ : Fin n)).eval ζ)
        - α ^ 23 * ((z - 1) * Permutation.lagNumer idx.omega idx.unmaskedEnd).eval ζ := by
  have hn : 0 < n := Nat.pos_of_neZero n
  have hω := idx.omega_prim
  have hb1 : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ₁
  have hb2 : ζ - idx.omega ^ (n - idx.zkRows) ≠ 0 := sub_ne_zero.mpr hζb
  -- the two Lagrange numerator identities, evaluated at ζ
  have E0 : (Permutation.lagNumer idx.omega (⟨0, Nat.pos_of_neZero n⟩ : Fin n)).eval ζ
        * (ζ - 1) = ζ ^ n - 1 := by
    have h := congrArg (Polynomial.eval ζ)
      (Permutation.lagNumer_mul_sub hω hn (⟨0, Nat.pos_of_neZero n⟩ : Fin n))
    simpa [zH, eval_mul, eval_sub, eval_X, eval_C, pow_zero] using h
  have E1 : (Permutation.lagNumer idx.omega idx.unmaskedEnd).eval ζ
        * (ζ - idx.omega ^ (n - idx.zkRows)) = ζ ^ n - 1 := by
    have h := congrArg (Polynomial.eval ζ)
      (Permutation.lagNumer_mul_sub hω hn idx.unmaskedEnd)
    simpa [zH, eval_mul, eval_sub, eval_X, eval_C, Index.unmaskedEnd] using h
  -- expand the evaluations on both sides
  simp only [evalsOf, eval_mul, eval_sub, eval_one]
  rw [div_eq_iff (mul_ne_zero hb2 hb1)]
  -- close by the two numerator identities
  linear_combination (α ^ 22 * (z.eval ζ - 1) * (ζ - idx.omega ^ (n - idx.zkRows))) * E0
    + (α ^ 23 * (z.eval ζ - 1) * (ζ - 1)) * E1

/-! ## The point bridge

The scalar-side verifier check — `permScalar · σ₆(ζ) − (ζⁿ − 1)·t(ζ)` equals `ftEval0` at
the honest record with public slot `−pub(ζ)` — is equivalent, at honest evaluations, to
the quotient identity `(aggregate α (fullFamily …)).eval ζ = (t · Z_H).eval ζ`, the
aggregate splitting into its gate and permutation halves. -/

/-- At the honest evaluation record, the scalar-side verifier check is equivalent to the
quotient identity at `ζ`. Consumed only by the Schwartz–Zippel core below, on the way to
`Kimchi.Protocol.sound`. -/
private theorem verifierEquation_iff [DecidableEq F] [NeZero n] (idx : Index F n)
    (pub : Fin idx.publicCount → F) (wTab : Fin n → Fin 15 → F)
    (z t : Polynomial F) (ζ β γ α : F)
    (hζ₁ : ζ ≠ 1) (hζb : ζ ≠ idx.omega ^ (n - idx.zkRows)) :
    permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (evalsOf idx wTab z ζ)
          * ((Permutation.sigmaPoly idx.omega idx.shifts idx.wiringPerm) 6).eval ζ
        - (ζ ^ n - 1) * t.eval ζ
      = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase idx.mds α β γ ζ
          (-((idx.pubPoly pub).eval ζ)) (evalsOf idx wTab z ζ)
      ↔ (aggregate α (idx.fullFamily pub wTab z β γ)).eval ζ = (t * zH F n).eval ζ := by
  -- the three permutation constraints at the index's wiring data
  set Cf := Permutation.constraints idx.omega idx.zkRows z (idx.permWitnessPoly wTab)
      (Permutation.sigmaPoly idx.omega idx.shifts idx.wiringPerm) idx.shifts β γ
      (⟨0, Nat.pos_of_neZero n⟩ : Fin n) idx.unmaskedEnd with hCf
  -- expand the aggregate at ζ into the gate block plus the three permutation members
  have hagg : (aggregate α (idx.fullFamily pub wTab z β γ)).eval ζ
      = (∑ k ∈ Finset.range Index.gateAlphaCount,
            α ^ k * (idx.gateMember pub wTab k).eval ζ)
        + (α ^ 21 * (Cf 0).eval ζ + α ^ 22 * (Cf 1).eval ζ + α ^ 23 * (Cf 2).eval ζ) := by
    rw [aggregate, eval_finsetSum, Fin.sum_univ_add]
    -- the else-branch of `fullFamily` folds back to `Cf`
    have hp : ∀ j : Fin Index.permAlphaCount,
        idx.fullFamily pub wTab z β γ (Fin.natAdd Index.gateAlphaCount j) = Cf j := by
      intro j
      simp only [Index.fullFamily]
      rw [dif_neg (show ¬ ((Fin.natAdd Index.gateAlphaCount j :
          Fin (Index.gateAlphaCount + Index.permAlphaCount)) : ℕ) < Index.gateAlphaCount
        from by rw [Fin.val_natAdd]; omega), ← hCf]
      congr 1
      apply Fin.ext
      simp only [Fin.val_natAdd, Index.gateAlphaCount]
      omega
    congr 1
    · rw [← Fin.sum_univ_eq_sum_range
        (fun k => α ^ k * (idx.gateMember pub wTab k).eval ζ) Index.gateAlphaCount]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hg : idx.fullFamily pub wTab z β γ (Fin.castAdd Index.permAlphaCount i)
          = idx.gateMember pub wTab (i : ℕ) := by
        simp only [Index.fullFamily]
        rw [dif_pos (show ((Fin.castAdd Index.permAlphaCount i :
            Fin (Index.gateAlphaCount + Index.permAlphaCount)) : ℕ) < Index.gateAlphaCount
          from by rw [Fin.val_castAdd]; exact i.isLt), Fin.val_castAdd]
      rw [eval_smul, smul_eq_mul, Fin.val_castAdd, hg]
    · rw [Fin.sum_univ_three, eval_smul, eval_smul, eval_smul, smul_eq_mul, smul_eq_mul,
        smul_eq_mul, hp 0, hp 1, hp 2, Fin.val_natAdd, Fin.val_natAdd, Fin.val_natAdd]
      norm_num
  -- σ-side recurrence at α²¹, with σ = the wiring σ, folded to `Cf 0`
  have hperm := permMember_eval idx wTab z ζ β γ α
    (Permutation.sigmaPoly idx.omega idx.shifts idx.wiringPerm) (fun _ => rfl)
    (⟨0, Nat.pos_of_neZero n⟩ : Fin n) idx.unmaskedEnd
  rw [← hCf] at hperm
  -- the boundary members are `Cf 1`, `Cf 2`
  have hCf1 : Cf 1 = (z - 1) * Permutation.lagNumer idx.omega
      (⟨0, Nat.pos_of_neZero n⟩ : Fin n) := by rw [hCf]; rfl
  have hCf2 : Cf 2 = (z - 1) * Permutation.lagNumer idx.omega idx.unmaskedEnd := by
    rw [hCf]; rfl
  have hbnd := boundary_eval idx wTab z ζ α hζ₁ hζb
  rw [← hCf1, ← hCf2] at hbnd
  -- gate block and the vanishing-polynomial product
  have hgate := gateMember_sum_eval idx pub wTab z ζ α
  have htzh : (t * zH F n).eval ζ = t.eval ζ * (ζ ^ n - 1) := by
    simp [zH, eval_mul, eval_sub, eval_pow, eval_X, eval_one]
  rw [hagg, hgate, htzh]
  simp only [ftEval0]
  rw [hbnd]
  constructor
  · intro h; linear_combination h - hperm
  · intro h; linear_combination h + hperm

/-! ## From one good challenge to satisfaction

The scalar-side acceptance equation, holding at a *single* challenge outside an explicit
bad set, implies satisfaction of the circuit. Each challenge is constrained only by a
counted exclusion: `β` and `γ` avoid the bad sets of the permutation argument, `α` avoids
those of the aggregate family, and the evaluation point `ζ` avoids the roots of the
quotient discrepancy. No injective family of points and no degree side-conditions are
needed — one avoiding point pins the identity by the counting bound. -/

open Kimchi.Permutation in
/-- One verifier-equation instance at a good challenge tuple — `β`, `γ`, `α`, and the
evaluation point `ζ` each outside their bad set — implies satisfaction of the circuit.
The Schwartz–Zippel core; consumed only by `Kimchi.Protocol.sound` below (file-private —
`private` is file-scoped, which is why `sound` lives in this file). -/
private theorem satisfies_of_verifierEquation [DecidableEq F] [NeZero n]
    (idx : Index F n) (pub : Fin idx.publicCount → F) (wTab : Fin n → Fin 15 → F)
    (β γ : F)
    (hβ : β ∉ badBetas
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts c.1 * idx.omega ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts (restrictCells idx.wiringPerm idx.wiringPerm_regionPreserving c).1
            * idx.omega
              ^ ((restrictCells idx.wiringPerm idx.wiringPerm_regionPreserving c).2 : ℕ))))
    (hγ : γ ∉ badGammas
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts c.1 * idx.omega ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts (restrictCells idx.wiringPerm idx.wiringPerm_regionPreserving c).1
            * idx.omega
              ^ ((restrictCells idx.wiringPerm idx.wiringPerm_regionPreserving c).2 : ℕ))) β)
    (zg : Polynomial F)
    (α : F)
    (hα : α ∉ badAlphas (idx.fullFamily pub wTab zg β γ) idx.omega n)
    (t : Polynomial F)
    (ζ : F)
    (hζ : ζ ∉ badZetas (aggregate α (idx.fullFamily pub wTab zg β γ)) t n)
    (hζ₁ : ζ ≠ 1)
    (hζb : ζ ≠ idx.omega ^ (n - idx.zkRows))
    (heq :
      permScalar β γ α
          (zkpmEval n idx.zkRows idx.omega ζ)
          (evalsOf idx wTab zg ζ)
        * ((Permutation.sigmaPoly idx.omega idx.shifts idx.wiringPerm) 6).eval
            ζ
        - (ζ ^ n - 1) * t.eval ζ
      = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase idx.mds α β γ
          ζ (-((idx.pubPoly pub).eval ζ))
          (evalsOf idx wTab zg ζ)) :
    Satisfies idx pub wTab := by
  refine idx.satisfies_of_evalCheck pub wTab β γ hβ hγ zg α hα t ζ hζ ?_
  exact (verifierEquation_iff idx pub wTab zg t ζ β γ α hζ₁ hζb).mp heq

end Kimchi.Protocol.Equation

/-! ## The protocol's soundness

The headline over the named acceptance predicate `Accepts` (`Protocol/Accepts.lean`).
It lives in this file — after the `Equation` namespace closes — because its proof consumes
the file-private Schwartz–Zippel core `satisfies_of_verifierEquation`. -/

namespace Kimchi.Protocol

open Polynomial Kimchi.Index Kimchi.Protocol.Equation

variable {F : Type*} [Field F] {n : ℕ}

/-- **Soundness of the polynomial protocol, over the prover's oracles.** The prover's
oracles are the witness-column polynomials `W` and the permutation-accumulator polynomial
`z` (degree `< n`), with a quotient oracle `t` presented per challenge; the verifier has
oracle access, reading them at the challenge point. The four Schwartz–Zippel bad challenge
sets are small (β/γ bounded by `7·(n − zkRows)`, α by `n·(K − 1)`, ζ by
`Index.degreeBound n`) and quantified BEFORE the challenges; and for every tuple avoiding
them at which `Accepts` holds on the oracle evaluations, the assignment read off the
witness oracles satisfies the circuit — the satisfying table is named EXPLICITLY in the
conclusion (`extractTable idx.omega W`): the witness IS the oracles' own data, extracted,
never supplied. Nothing here mentions commitments, an SRS,
or a group: this is the idealized protocol. The commitment layer instantiates it by
binding the oracles to commitments and certifying the claimed evaluations are the true
oracle evaluations (`kimchiProof_sound_of_openings`). Packaged in the same `∃ bad sets,
card bounds ∧ guarded implication` shape as the compiled roots, so the interface is a
direct hand-off. -/
theorem sound [DecidableEq F] [NeZero n] (idx : Index F n)
    (pub : Fin idx.publicCount → F) (W : Fin 15 → Polynomial F)
    (z : Polynomial F) (hz : z.natDegree < n) :
    ∃ (badB : Finset F) (badG : F → Finset F) (badA : F → F → Finset F)
        (badZ : F → F → F → Polynomial F → Finset F),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial F), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n))
      ∧ ∀ (β γ α : F) (t : Polynomial F) (ζ : F),
          β ∉ badB → γ ∉ badG β → α ∉ badA β γ → ζ ∉ badZ β γ α t →
          ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) →
          Accepts idx pub (evalsOf idx (extractTable idx.omega W) z ζ) t β γ α ζ →
          Satisfies idx pub (extractTable idx.omega W) := by
  classical
  set m₁ : Multiset (F × F) :=
    Finset.univ.val.map fun c : Fin 7 × Fin (n - idx.zkRows) =>
      ((idx.permWitnessPoly (extractTable idx.omega W) c.1).eval (idx.omega ^ (c.2 : ℕ)),
        idx.shifts c.1 * idx.omega ^ (c.2 : ℕ)) with hm₁def
  set m₂ : Multiset (F × F) :=
    Finset.univ.val.map fun c : Fin 7 × Fin (n - idx.zkRows) =>
      ((idx.permWitnessPoly (extractTable idx.omega W) c.1).eval (idx.omega ^ (c.2 : ℕ)),
        idx.shifts (Kimchi.Permutation.restrictCells idx.wiringPerm
              idx.wiringPerm_regionPreserving c).1
          * idx.omega ^ ((Kimchi.Permutation.restrictCells idx.wiringPerm
              idx.wiringPerm_regionPreserving c).2 : ℕ)) with hm₂def
  have hcard : ∀ (f : Fin 7 × Fin (n - idx.zkRows) → F × F),
      Multiset.card (Finset.univ.val.map f) = 7 * (n - idx.zkRows) := by
    intro f
    rw [Multiset.card_map]
    simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  refine ⟨Kimchi.GrandProduct.badBetas m₁ m₂, fun β => Kimchi.GrandProduct.badGammas m₁ m₂ β,
    fun β γ => Kimchi.badAlphas
      (idx.fullFamily pub (extractTable idx.omega W) z β γ) idx.omega n,
    fun β γ α t => Kimchi.badZetas
      (Kimchi.aggregate α
        (idx.fullFamily pub (extractTable idx.omega W) z β γ)) t n,
    ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · refine le_trans (Kimchi.GrandProduct.card_badBetas_le m₁ m₂) ?_
    rw [hm₁def, hm₂def, hcard, hcard]
    exact le_of_eq (max_self _)
  · intro β
    refine le_trans (Kimchi.GrandProduct.card_badGammas_le m₁ m₂ β) ?_
    rw [hm₁def, hm₂def, hcard, hcard]
    exact le_of_eq (max_self _)
  · intro β γ
    exact Kimchi.card_badAlphas_le
      (idx.fullFamily pub (extractTable idx.omega W) z β γ) idx.omega n
  · intro β γ α t ht
    exact Kimchi.card_badZetas_le
      (Kimchi.aggregate α
        (idx.fullFamily pub (extractTable idx.omega W) z β γ)) t
      (Index.aggregate_natDegree_le idx pub (extractTable idx.omega W) z hz β γ α)
      (Index.t_zH_natDegree_le t ht)
  · intro β γ α t ζ hβ hγ hα hζ hζ₁ hζb heq
    exact satisfies_of_verifierEquation idx pub (extractTable idx.omega W) β γ hβ hγ z α hα
      t ζ hζ hζ₁ hζb heq

end Kimchi.Protocol
