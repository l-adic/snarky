import Kimchi.Lift

/-!
# The verifier's scalar side, in closed form

The scalar check reads the proof's evaluations at `ζ` and `ζω` together with the
Fiat–Shamir challenges and forms two quantities: `ft(ζ)`, and the scalar multiplying the
permutation commitment. An implementation computes the gate part by interpreting a
compiled expression; here the same functions are given in closed form over the gate
constraint families, instantiated at the field carrier with the evaluation environment
`⟨w(ζ), w(ζω), coeffs(ζ)⟩`.

Every gate selector is evaluated in the proof, so the whole gate linearization lands in
the constant term and the commitment side reduces to a single permutation term.

Alpha layout: each gate weights its `k`-th constraint by `αᵏ` from a shared pool, and the
permutation argument holds the next three powers `α²¹, α²², α²³`.
-/
namespace Kimchi.Protocol.Linearization

open Kimchi.Lift
open Kimchi.Lift.Gate

variable {F : Type*} [Field F]

/-- The combined evaluations the scalar side reads: each column at `ζ`, with the witness
and the accumulator also at `ζω`. -/
structure Evals (F : Type*) where
  w : Fin 15 → F
  wOmega : Fin 15 → F
  z : F
  zOmega : F
  s : Fin 6 → F
  coeffs : Fin 15 → F
  genericSelector : F
  poseidonSelector : F
  completeAddSelector : F
  mulSelector : F
  emulSelector : F
  endoScalarSelector : F

/-- The evaluations as a gate cell environment: current row `w(ζ)`, next row `w(ζω)`,
coefficients at `ζ`. -/
def evalEnv (e : Evals F) : ArgumentEnv F :=
  ⟨e.w, e.wOmega, e.coeffs⟩

/-- `∑ₖ αᵏ · cₖ` over a constraint list, as a Horner fold. -/
def alphaCombo (α : F) (L : List F) : F :=
  L.foldr (fun c acc => c + α * acc) 0

/-- Once `m` covers the list, the Horner fold is the indexed α-power sum. -/
theorem alphaCombo_eq_sum_getD (α : F) :
    ∀ (L : List F) (m : ℕ), L.length ≤ m →
      alphaCombo α L = ∑ k ∈ Finset.range m, α ^ k * L.getD k 0
  | [], m, _ => by simp [alphaCombo]
  | c :: t, m + 1, h => by
    have ih := alphaCombo_eq_sum_getD α t m (by simpa using h)
    rw [show alphaCombo α (c :: t) = c + α * alphaCombo α t from rfl, ih,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, one_mul]
    rw [add_comm, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring

/-- The gate linearization: each gate's α-weighted constraint list, evaluated at the
cell environment and weighted by its evaluated selector. Gates share the alpha pool, so
every list starts at `α⁰`. -/
def gateLinearization (endo : F) (mds : Kimchi.Gate.Poseidon.Mds F) (α : F)
    (e : Evals F) : F :=
  e.genericSelector * alphaCombo α ((Generic.argument (F := F)).constraints (evalEnv e))
    + e.poseidonSelector
      * alphaCombo α ((Poseidon.argument mds).constraints (evalEnv e))
    + e.completeAddSelector
      * alphaCombo α ((AddComplete.argument (F := F)).constraints (evalEnv e))
    + e.mulSelector
      * alphaCombo α ((VarBaseMul.argument (F := F)).constraints (evalEnv e))
    + e.emulSelector * alphaCombo α ((EndoMul.argument endo).constraints (evalEnv e))
    + e.endoScalarSelector
      * alphaCombo α ((EndoScalar.argument (F := F)).constraints (evalEnv e))

/-- The scalar multiplying the permutation commitment: the negated `z(ζω)`-side product
row of the permutation recurrence, at the first permutation alpha. -/
def permScalar (β γ α zkpmZ : F) (e : Evals F) : F :=
  -(e.zOmega * β * α ^ 21 * zkpmZ
    * ∏ i : Fin 6, (γ + β * e.s i + e.w ⟨i, by omega⟩))

/-- The permutation vanishing polynomial at a point:
`zkpm(ζ) = (ζ − ω^{n−zkRows})(ζ − ω^{n−zkRows+1})(ζ − ω^{n−1})` — production's
three-factor `permutation_vanishing_polynomial` (permutation.rs:105–121), which
coincides with the full `∏_{[n−zkRows, n)}` window only at `zkRows = 3`. -/
def zkpmEval (n zkRows : ℕ) (ω ζ : F) : F :=
  (ζ - ω ^ (n - zkRows)) * (ζ - ω ^ (n - zkRows + 1)) * (ζ - ω ^ (n - 1))

/-- The verifier's `ft(ζ)`: the permutation recurrence read at `ζ`, minus the public-input
evaluation, plus the accumulator boundary quotient pinning the two masked rows, minus the
gate linearization. -/
def ftEval0 (n zkRows : ℕ) (ω : F) (shifts : Fin 7 → F) (endo : F)
    (mds : Kimchi.Gate.Poseidon.Mds F) (α β γ ζ pubEval : F) (e : Evals F) : F :=
  let zkpmZ := zkpmEval n zkRows ω ζ
  let zeta1m1 := ζ ^ n - 1
  let wBoundary := ω ^ (n - zkRows)
  let sigmaSide := ((e.w 6 + γ) * e.zOmega * α ^ 21 * zkpmZ)
    * ∏ i : Fin 6, (β * e.s i + e.w ⟨i, by omega⟩ + γ)
  let shiftSide := (α ^ 21 * zkpmZ * e.z)
    * ∏ i : Fin 7, (γ + β * ζ * shifts i + e.w ⟨i, by omega⟩)
  let boundary := ((zeta1m1 * α ^ 22 * (ζ - wBoundary) + zeta1m1 * α ^ 23 * (ζ - 1))
    * (1 - e.z)) / ((ζ - wBoundary) * (ζ - 1))
  sigmaSide - pubEval - shiftSide + boundary - gateLinearization endo mds α e

end Kimchi.Protocol.Linearization
