import Kimchi.Protocol.Linearization
import Kimchi.Index.Aggregate

/-!
# The polynomial protocol: the verifier's acceptance check

The named definition of the kimchi polynomial protocol — what the polynomial verifier
*checks*, stated with no reference to any commitment scheme. The verifier holds an index
`idx` and a public input `pub`; the prover's messages are polynomial oracles, and what the
verifier reads off them at the challenge point is an evaluation record `E : Evals F`
together with a quotient `t`. `Accepts` is the single algebraic identity the verifier
demands of that data at the challenges `(β, γ, α, ζ)`: the linearized permutation scalar
against the last σ-column, minus the vanishing-weighted quotient value, equals the
closed-form `ftEval0` with the public interpolant in the constant slot.

`Accepts` is PCS-free — it is the protocol. Its soundness is `Kimchi.Protocol.sound`
(`Equation.lean`): for oracles read honestly (`evalsOf` at an extracted table), one
accepting challenge tuple outside explicit counted bad sets forces circuit satisfaction.
The commitment layer (`Kimchi/Verifier/`) instantiates the oracles with commitments and
certifies the record `E` it feeds here is the true oracle evaluations.

The σ-column term uses the polynomial-layer `Permutation.sigmaPoly`; the wire-facing form
`idx.sigmaPoly` agrees via `Index.sigmaPoly_eq_wiring`.
-/
namespace Kimchi.Protocol

open Polynomial Kimchi.Index Kimchi.Protocol.Linearization

variable {F : Type*} [Field F] {n : ℕ}

/-- The polynomial verifier's acceptance check: the linearized identity on an evaluation
record `E` (the oracle evaluations at `ζ` and `ωζ`) and a quotient `t`, at the challenges
`(β, γ, α, ζ)`. PCS-free — this is the protocol. -/
def Accepts (idx : Index F n) (pub : Fin idx.publicCount → F)
    (E : Evals F) (t : Polynomial F) (β γ α ζ : F) : Prop :=
  permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) E
      * ((Permutation.sigmaPoly idx.omega idx.shifts idx.wiringPerm) 6).eval ζ
    - (ζ ^ n - 1) * t.eval ζ
  = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase idx.mds α β γ ζ
      (-((idx.pubPoly pub).eval ζ)) E

end Kimchi.Protocol
