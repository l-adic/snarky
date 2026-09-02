import Pickles.Linearization.Circuit
import Pickles.Reflect.Certificate

/-!
# The circuit computes the gate linearization

Where the three developments meet.

* `Pickles.Linearization.evaluate_spec` — the constraints the in-circuit interpreter emits
  pin its output to the pure interpreter's value.
* `Pickles.Linearization.inputs_circuitCompatible` — the concrete circuit environment
  computes the specified one.
* `Pickles.Reflect.evaluate_fpTokens` — the deployed stream's pure value IS the closed-form
  gate linearization.

Composing them gives a statement whose right-hand side is the verifier's own quantity
rather than a restatement of the token program: the gate contribution to `ftEval0`.

It is RELATIVE faithfulness. It says the circuit computes what the wire protocol computes;
whether the wire protocol is sound is a separate question and out of scope — see
`formal/docs/soundness-line-retirement.md`.

Completeness — that the honest prover run succeeds — is NOT proved here. Without it this
statement is satisfiable by a circuit no assignment satisfies, so it is half the story.
-/

namespace Pickles.Reflect

open Std.Do Snarky Pickles.Linearization Kimchi.Protocol.Linearization

variable {c : Type} [BasicSystem Fp c] [ConstraintHolds Fp c] [LawfulBasicSystem Fp c]

/-- **The in-circuit reading of the deployed stream computes the gate contribution to
`ftEval0`.** Any valuation satisfying the emitted constraints reads the interpreter's
output as `gateLinearization` at the readings of the circuit's own inputs.

The α-table hypothesis is the caller's obligation: the powers must be precomputed and read
correctly, which is what `precomputeAlphaPowers` establishes on the PureScript side. It is
what keeps `alphaPow` free — a lookup rather than a per-site exponentiation at each of the
stream's 124 α-occurrences. -/
theorem circuit_gateLinearization {V : Valuation Fp} (inp : Inputs Fp) (α : Fp)
    (htab : ∀ n, (inp.alphaPows n).val V = α ^ n) :
    ⦃⌜True⌝⦄
    evaluate (inp.toEnv (c := Builder V c) Pasta.pallasEndo symMds lookupZero
      (fun _ => false)) fpTokens
    ⦃⇓ a _ => ⌜a.val V = gateLinearization Pasta.pallasEndo symMds α
      (inp.evals.map (·.val V))⌝⦄ := by
  have h := inputs_circuitCompatible (c := c) (V := V) Pasta.pallasEndo symMds
    lookupZero (fun _ => false) inp α htab
  rw [lookupZero_map] at h
  have hdc : ∀ f (t n : Unit → CircuitM Fp (Builder V c) (FVar Fp)),
      (inp.toEnv (c := Builder V c) Pasta.pallasEndo symMds lookupZero
        (fun _ => false)).ifFeature f t n = n () := by
    intro f t n; simp [Inputs.toEnv]
  have hdp : ∀ f (t n : Unit → Id Fp),
      ((inp.evals.map (·.val V)).toEnv Pasta.pallasEndo symMds α (inp.beta.val V)
        (inp.gamma.val V) (inp.jointCombiner.val V) (inp.vanishes.val V) (fun _ _ => 0)
        LookupEvals.zero (fun _ => false)).ifFeature f t n = n () := by
    intro f t n; simp [Evals.toEnv]
  have hs := evaluate_spec h hdc hdp fpTokens
  rw [evaluate_fpTokens] at hs
  exact hs

end Pickles.Reflect
