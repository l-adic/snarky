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

-- `Argument.constraints` and `ArgumentEnv.map` bind their rings in the SAME universe as
-- the gate's field, so carriers are named at one explicit universe rather than `Type*`.
universe u

open Kimchi.Lift
open Kimchi.Lift.Gate

-- The evaluation record and the two functions that read it need no division, so they are
-- stated over a commutative ring: that is what lets them be instantiated at a polynomial
-- algebra, which `Kimchi.Lift.Argument.constraints` already supports and
-- `Pickles.Linearization.Spec.gateLinearizationAt` exploits. Everything below `Evals`
-- keeps `Field` — `Argument` itself requires one, and `ftEval0` divides.
variable {F : Type*} [CommRing F]

/-- The combined evaluations the scalar side reads: each column at `ζ`, with the witness
and the accumulator also at `ζω`. -/
@[ext]
structure Evals (F : Type*) where
  /-- The witness columns (`wCols`) at `ζ`. -/
  w : Fin wCols → F
  /-- The witness columns (`wCols`) at `ζω`. -/
  wOmega : Fin wCols → F
  /-- The permutation accumulator at `ζ`. -/
  z : F
  /-- The permutation accumulator at `ζω`. -/
  zOmega : F
  /-- The evaluated σ columns (`sigmaRows`) at `ζ`. -/
  s : Fin sigmaRows → F
  /-- The coefficient columns (`coeffCols`) at `ζ`. -/
  coeffs : Fin coeffCols → F
  /-- The generic selector at `ζ`. -/
  genericSelector : F
  /-- The poseidon selector at `ζ`. -/
  poseidonSelector : F
  /-- The completeAdd selector at `ζ`. -/
  completeAddSelector : F
  /-- The varBaseMul selector at `ζ`. -/
  mulSelector : F
  /-- The endoMul selector at `ζ`. -/
  emulSelector : F
  /-- The endoScalar selector at `ζ`. -/
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

/-! ### Naturality along an `F`-algebra map

Every `Argument` carries a naturality square (`Kimchi.Lift.Argument.constraints_map`), so
the whole gate linearization transports along an `F`-algebra homomorphism. This is what
lets the linearization be computed once over a polynomial algebra and read back at the
field: the polynomial identity, pushed through the evaluation homomorphism, IS the field
identity. -/

/-- Push a carrier map through the evaluations, cell by cell. -/
def Evals.map {R S : Type*} (φ : R → S) (e : Evals R) : Evals S where
  w i := φ (e.w i)
  wOmega i := φ (e.wOmega i)
  z := φ e.z
  zOmega := φ e.zOmega
  s i := φ (e.s i)
  coeffs i := φ (e.coeffs i)
  genericSelector := φ e.genericSelector
  poseidonSelector := φ e.poseidonSelector
  completeAddSelector := φ e.completeAddSelector
  mulSelector := φ e.mulSelector
  emulSelector := φ e.emulSelector
  endoScalarSelector := φ e.endoScalarSelector

/-- Mapping the evaluations and taking their cell environment is taking the cell
environment and mapping it: both are `⟨φ ∘ e.w, φ ∘ e.wOmega, φ ∘ e.coeffs⟩`. The two
spellings meet where `constraints_map` hands back the one and `gateLinearization` wants the
other. -/
private theorem evalEnv_map {R S : Type u} (φ : R → S) (e : Evals R) :
    evalEnv (e.map φ) = (evalEnv e).map φ := rfl

section Field

variable {F : Type u} [Field F]

/-- The gate linearization: each gate's α-weighted constraint list, evaluated at the
cell environment and weighted by its evaluated selector. Gates share the alpha pool, so
every list starts at `α⁰`.

Read at an arbitrary `F`-algebra `R`, which is the freedom
`Kimchi.Lift.Argument.constraints` already offers (`∀ {R} [CommRing R] [Algebra F R]`) and
which a reflection proof needs in order to run the gates at a polynomial algebra. The gate
PARAMETERS stay at `F` — they build the `Argument`s themselves — while the evaluations live
at `R`. At `R := F` this is the ordinary scalar-side linearization, so `ftEval0` and the
fixture drivers read it unchanged. -/
def gateLinearization {R : Type u} [CommRing R] [Algebra F R] (endo : F)
    (mds : Kimchi.Gate.Poseidon.Mds F) (α : R) (e : Evals R) : R :=
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

/-- **The gate linearization transports along an `F`-algebra map.** Computing it over `R`
and pushing the result through `φ` is computing it over `S` from the pushed evaluations.

The gate parameters `endo` and `mds` are untouched: they live at `F` and build the
`Argument`s themselves, so `φ` never sees them. Each summand goes through in three moves —
`φ` is a ring hom, so it splits the selector off the α-combination; the combination is a
Horner fold, so `φ` distributes through it onto the constraint list; and that mapped list
is `constraints_map`, the naturality square every gate already discharges. -/
theorem gateLinearization_map {R S : Type u} [CommRing R] [CommRing S]
    [Algebra F R] [Algebra F S] (φ : R →ₐ[F] S) (endo : F)
    (mds : Kimchi.Gate.Poseidon.Mds F) (α : R) (e : Evals R) :
    φ (gateLinearization endo mds α e) = gateLinearization endo mds (φ α) (e.map φ) := by
  -- `φ` through a Horner fold, which is all `alphaCombo` is.
  have hcombo : ∀ (L : List R), φ (alphaCombo α L) = alphaCombo (φ α) (L.map φ) := by
    intro L
    induction L with
    | nil => simp [alphaCombo]
    | cons c t ih =>
      rw [show alphaCombo α (c :: t) = c + α * alphaCombo α t from rfl, List.map_cons,
        show alphaCombo (φ α) (φ c :: t.map φ) = φ c + φ α * alphaCombo (φ α) (t.map φ)
          from rfl, map_add, map_mul, ih]
  -- One gate's summand: split, distribute, then cross with the naturality square.
  have hgate : ∀ (G : Kimchi.Lift.Argument F) (sel : R),
      φ (sel * alphaCombo α (G.constraints (evalEnv e)))
        = φ sel * alphaCombo (φ α) (G.constraints (evalEnv (e.map φ))) := by
    intro G sel
    rw [map_mul, hcombo, G.constraints_map φ, evalEnv_map]
  simp only [gateLinearization, map_add, hgate]
  rfl

/-- The scalar multiplying the permutation commitment: the negated `z(ζω)`-side product
row of the permutation recurrence, at the first permutation alpha. -/
def permScalar (β γ α zkpmZ : F) (e : Evals F) : F :=
  -(e.zOmega * β * α ^ 21 * zkpmZ
    * ∏ i : Fin sigmaRows, (γ + β * e.s i + e.w (sigmaCol i)))

/-- The permutation vanishing polynomial at a point:
`zkpm(ζ) = (ζ − ω^{n−zkRows})(ζ − ω^{n−zkRows+1})(ζ − ω^{n−1})` — production's
three-factor `permutation_vanishing_polynomial` (permutation.rs:105–121), which
coincides with the full `∏_{[n−zkRows, n)}` window only at `zkRows = 3`. -/
def zkpmEval (n zkRows : ℕ) (ω ζ : F) : F :=
  (ζ - ω ^ (n - zkRows)) * (ζ - ω ^ (n - zkRows + 1)) * (ζ - ω ^ (n - 1))

/-- The verifier's `ft(ζ)`: the permutation recurrence read at `ζ`, minus the public-input
evaluation, plus the accumulator boundary quotient pinning the two masked rows, minus the
gate linearization. -/
def ftEval0 (n zkRows : ℕ) (ω : F) (shifts : Fin permCols → F) (endo : F)
    (mds : Kimchi.Gate.Poseidon.Mds F) (α β γ ζ pubEval : F) (e : Evals F) : F :=
  let zkpmZ := zkpmEval n zkRows ω ζ
  let zeta1m1 := ζ ^ n - 1
  let wBoundary := ω ^ (n - zkRows)
  let sigmaSide := ((e.w 6 + γ) * e.zOmega * α ^ 21 * zkpmZ)
    * ∏ i : Fin sigmaRows, (β * e.s i + e.w (sigmaCol i) + γ)
  let shiftSide := (α ^ 21 * zkpmZ * e.z)
    * ∏ i : Fin permCols, (γ + β * ζ * shifts i + e.w (permCol i))
  let boundary := ((zeta1m1 * α ^ 22 * (ζ - wBoundary) + zeta1m1 * α ^ 23 * (ζ - 1))
    * (1 - e.z)) / ((ζ - wBoundary) * (ζ - 1))
  sigmaSide - pubEval - shiftSide + boundary - gateLinearization endo mds α e

end Field

end Kimchi.Protocol.Linearization
