import Kimchi.Quotient.Generic
import Kimchi.Quotient.Poseidon
import Kimchi.Quotient.AddComplete
import Kimchi.Quotient.VarBaseMul
import Kimchi.Quotient.EndoMul
import Kimchi.Quotient.EndoScalar

/-!
# The verifier's scalar side — the linearization, in closed form

The kimchi verifier's scalar-side check (`verifier.rs`): from the proof's evaluations at
`ζ` and `ζω` and the Fiat–Shamir challenges, compute `ft(ζ)` (`ft_eval0`) and the
`f_comm` scalar — and check them through the PCS batch. Production evaluates the *gate*
part via the compiled expression framework (`PolishToken::evaluate` of
`linearization.constant_term`); this module gives the same functions in closed form over
the library's own gate constraint lists — the `Argument` primitives of
`Kimchi/Quotient/`, instantiated at the *field* carrier with the evaluation environment
`⟨w(ζ), w(ζω), coeffs(ζ)⟩`. The token stream never appears here: it is adjudicated by
value against these closed forms in `scripts/check_linearization.lean`, on a fixture
recorded from a real production proof (`tools/fixture-dump`'s `linearization_dump`).

At this proof-systems pin every gate selector is evaluated in the proof, so the entire
gate linearization lands in the constant term (`linearization.index_terms` is empty) and
`f_comm` is the single σ-commitment term (`perm_scalars`).

The alpha layout is the shared pool of Phase B (`Kimchi/Index/Aggregate.lean`): every
gate weights its `k`-th constraint by `α^k`, and the permutation argument holds the next
three powers `α^21, α^22, α^23`.

## Contents

* `Evals` — the combined evaluations the scalar side reads.
* `evalEnv` — the evaluations as a gate cell environment (`ArgumentEnv F`).
* `alphaCombo` — `∑ₖ αᵏ · cₖ` of a constraint list, by Horner.
* `gateLinearization` — the six-gate selector-weighted combination: production's
  `constant_term`.
* `permScalar` — `perm_scalars`, the σ-commitment scalar of `f_comm`.
* `zkpmEval` — the permutation vanishing polynomial `∏ (ζ − ω^j)` over the zk rows.
* `ftEval0` — the verifier's `ft(ζ)`.
-/

namespace Kimchi.Verifier.Linearization

open Kimchi.Quotient

variable {F : Type*} [Field F]

/-- The combined evaluations the scalar side reads: each column at `ζ` (and the witness
and `z` at `ζω`). Mirrors the verifier's `evals` after `combine` (one chunk here). -/
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

/-- The evaluations as a gate cell environment: current row = `w(ζ)`, next row =
`w(ζω)`, coefficients at `ζ`. This is the field-carrier instance of the same
`ArgumentEnv` the quotient layer reads at rows and at polynomials. -/
def evalEnv (e : Evals F) : ArgumentEnv F :=
  ⟨e.w, e.wOmega, e.coeffs⟩

/-- `∑ₖ αᵏ · cₖ` over a constraint list, as the Horner fold
`c₀ + α(c₁ + α(c₂ + …))`. -/
def alphaCombo (α : F) (L : List F) : F :=
  L.foldr (fun c acc => c + α * acc) 0

/-- Horner ↔ indexed: once `m` covers the list, `alphaCombo` is the `getD`-indexed
α-power sum — the form the aggregate's shared-pool members consume. -/
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

/-- **The gate linearization** — production's `linearization.constant_term`: each
gate's α-weighted constraint list (the `Argument` primitives, at the evaluation
environment), weighted by its evaluated selector. The gates share the alpha pool, so
every list starts at `α^0`. -/
def gateLinearization (endo α : F) (e : Evals F) : F :=
  e.genericSelector * alphaCombo α ((genericArgument (F := F)).constraints (evalEnv e))
    + e.poseidonSelector
      * alphaCombo α ((Poseidon.argument (F := F)).constraints (evalEnv e))
    + e.completeAddSelector
      * alphaCombo α ((AddComplete.argument (F := F)).constraints (evalEnv e))
    + e.mulSelector
      * alphaCombo α ((VarBaseMul.argument (F := F)).constraints (evalEnv e))
    + e.emulSelector * alphaCombo α ((EndoMul.argument endo).constraints (evalEnv e))
    + e.endoScalarSelector
      * alphaCombo α ((EndoScalar.argument (F := F)).constraints (evalEnv e))

/-- **The σ-commitment scalar** (`perm_scalars`): the negated `z(ζω)`-side product row
of the permutation recurrence at the first permutation alpha `α^21`,
`−z(ζω)·β·α²¹·zkpm(ζ) · ∏ᵢ₌₀⁵ (γ + β·σᵢ(ζ) + wᵢ(ζ))`. -/
def permScalar (β γ α zkpmZ : F) (e : Evals F) : F :=
  -(e.zOmega * β * α ^ 21 * zkpmZ
    * ∏ i : Fin 6, (γ + β * e.s i + e.w ⟨i, by omega⟩))

/-- The permutation vanishing polynomial at a point:
`zkpm(ζ) = ∏ⱼ (ζ − ω^j)` over the `zkRows` masked rows `j ∈ [n − zkRows, n)`. -/
def zkpmEval (n zkRows : ℕ) (ω ζ : F) : F :=
  ∏ j ∈ Finset.Ico (n - zkRows) n, (ζ - ω ^ j)

/-- **The verifier's `ft(ζ)`** (`ft_eval0`, `verifier.rs`): the permutation recurrence
read at `ζ` (the `σ`-side product against `z(ζω)` minus the shift-side product against
`z(ζ)`, both at `α²¹·zkpm(ζ)`), minus the public-input evaluation, plus the accumulator
boundary quotient (the two Lagrange pins at rows `0` and `n − zkRows`, at `α²²`/`α²³`),
minus the gate linearization. `pubEval` is the combined public evaluation at `ζ`. -/
def ftEval0 (n zkRows : ℕ) (ω : F) (shifts : Fin 7 → F) (endo : F)
    (α β γ ζ pubEval : F) (e : Evals F) : F :=
  let zkpmZ := zkpmEval n zkRows ω ζ
  let zeta1m1 := ζ ^ n - 1
  let wBoundary := ω ^ (n - zkRows)
  let sigmaSide := ((e.w 6 + γ) * e.zOmega * α ^ 21 * zkpmZ)
    * ∏ i : Fin 6, (β * e.s i + e.w ⟨i, by omega⟩ + γ)
  let shiftSide := (α ^ 21 * zkpmZ * e.z)
    * ∏ i : Fin 7, (γ + β * ζ * shifts i + e.w ⟨i, by omega⟩)
  let boundary := ((zeta1m1 * α ^ 22 * (ζ - wBoundary) + zeta1m1 * α ^ 23 * (ζ - 1))
    * (1 - e.z)) / ((ζ - wBoundary) * (ζ - 1))
  sigmaSide - pubEval - shiftSide + boundary - gateLinearization endo α e

end Kimchi.Verifier.Linearization
