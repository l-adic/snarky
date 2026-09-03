import Pickles.Linearization.Circuit
import Pickles.Reflect.Certificate

/-!
# The circuit computes the gate linearization

The in-circuit reading of a deployed token stream computes the gate contribution to
`ftEval0`, the wire verifier's own quantity.

## Main results

* `circuit_gateLinearization`: for any stream with a reflection endpoint, any satisfying
  valuation of the constraints the in-circuit interpreter emits reads its output as
  `gateLinearization` at the readings of the circuit's inputs.
* `circuit_gateLinearization_fp`, `circuit_gateLinearization_fq`: the two deployed
  streams, one per side of the cycle. These are the results the package stands behind and
  the axiom gate roots; everything else is in their closure.

## Implementation notes

The composition is `evaluate_spec` (the emitted constraints pin the pure value),
`inputs_circuitCompatible` (the circuit environment computes the pure one at its own
readings), `evaluate_withAlphaPow` and `evaluate_withUlb` (the run reads the α-table only
at the stream's exponents and never reaches the Lagrange basis), and the stream's
reflection endpoint from `Certificate.lean`. Nothing in it is field-specific except the
endpoint, so the generic theorem takes the endpoint as a hypothesis.

This is relative faithfulness: the circuit computes what the wire protocol computes.
Whether the wire protocol is sound is out of scope (`formal/docs/soundness-line-retirement.md`),
and completeness, that the honest prover run succeeds, is not proved here.
-/

namespace Pickles.Reflect

open Std.Do Snarky Pickles.Linearization Kimchi.Protocol.Linearization

/-- Any valuation satisfying the constraints the in-circuit interpreter emits reads its
output as `gateLinearization` at the readings of the circuit's inputs, for any stream with
reflection endpoint `hcert` that reaches no Lagrange basis (`hvis`), given an α-table
correct at the exponents the stream reads (`htab`). The Lagrange-basis gadget `ulb` is
unconstrained. -/
theorem circuit_gateLinearization {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] {V : Valuation F}
    (endo : F) (mds : Kimchi.Gate.Poseidon.Mds F) (toks : Array PolishToken)
    (hcert : ∀ (α β γ jc van : F) (e : Evals F),
      (evaluate (e.toEnv endo mds α β γ jc van (fun _ _ => 0) LookupEvals.zero
        (fun _ => false)) toks : F) = gateLinearization endo mds α e)
    (hvis : ∀ i ∈ visitedAll toks, noUlbAt toks i = true)
    (ulb : Bool → Int → CircuitM F (Builder V c) (FVar F)) (inp : Inputs F) (α : F)
    (htab : ∀ n ∈ alphaExponents toks, (inp.alphaPows n).val V = α ^ n) :
    ⦃⌜True⌝⦄
    evaluate (inp.toEnv (c := Builder V c) endo mds lookupZero (fun _ => false) ulb) toks
    ⦃⇓ a _ => ⌜a.val V = gateLinearization endo mds α (inp.evals.map (·.val V))⌝⦄ := by
  have h := inputs_circuitCompatible (c := c) (V := V) endo mds lookupZero
    (fun _ => false) inp α
  rw [lookupZero_map] at h
  have hdc : ∀ f (t n : Unit → CircuitM F (Builder V c) (FVar F)),
      (inp.toEnv (c := Builder V c) endo mds lookupZero (fun _ => false)
        (fun _ _ => pure (.const 0))).ifFeature f t n = n () := by
    intro f t n; simp [Inputs.toEnv]
  have hdp : ∀ f (t n : Unit → Id F),
      (((inp.evals.map (·.val V)).toEnv endo mds α (inp.beta.val V) (inp.gamma.val V)
        (inp.jointCombiner.val V) (inp.vanishes.val V) (fun _ _ => 0) LookupEvals.zero
        (fun _ => false)).withAlphaPow (fun n => (inp.alphaPows n).val V)).ifFeature f t n
        = n () := by
    intro f t n; simp [Env.withAlphaPow]
  have hs := evaluate_spec h hdc hdp toks
  rw [evaluate_withAlphaPow _ _ _ (fun n hn => by simpa using htab n hn), hcert] at hs
  rw [← Inputs.toEnv_withUlb endo mds lookupZero (fun _ => false) (fun _ _ => pure (.const 0))
    ulb inp, evaluate_withUlb _ _ _ hdc hvis]
  exact hs

/-! ## The deployed streams

One corollary per side of the cycle, each supplying its endpoint and reachability facts
from `Certificate.lean`. A precomputed α-table of length `alphaBound + 1` is all a caller
owes. -/

/-- The `Fp` stream in circuit computes the gate contribution to `ftEval0`. -/
theorem circuit_gateLinearization_fp {c : Type} [BasicSystem Fp c] [ConstraintHolds Fp c]
    [LawfulBasicSystem Fp c] {V : Valuation Fp}
    (ulb : Bool → Int → CircuitM Fp (Builder V c) (FVar Fp)) (inp : Inputs Fp) (α : Fp)
    (htab : ∀ n ≤ alphaBound, (inp.alphaPows n).val V = α ^ n) :
    ⦃⌜True⌝⦄
    evaluate (inp.toEnv (c := Builder V c) Pasta.pallasEndo symMds lookupZero
      (fun _ => false) ulb) fpTokens
    ⦃⇓ a _ => ⌜a.val V = gateLinearization Pasta.pallasEndo symMds α
      (inp.evals.map (·.val V))⌝⦄ :=
  circuit_gateLinearization Pasta.pallasEndo symMds fpTokens
    (fun α β γ jc van e => evaluate_fpTokens α β γ jc van _ e) visited_fpTokens_noUlb ulb
    inp α fun n hn => htab n (alphaExponents_fpTokens_le n hn)

/-- The `Fq` stream in circuit computes the gate contribution to `ftEval0`. -/
theorem circuit_gateLinearization_fq {c : Type} [BasicSystem Fq c] [ConstraintHolds Fq c]
    [LawfulBasicSystem Fq c] {V : Valuation Fq}
    (ulb : Bool → Int → CircuitM Fq (Builder V c) (FVar Fq)) (inp : Inputs Fq) (α : Fq)
    (htab : ∀ n ≤ alphaBound, (inp.alphaPows n).val V = α ^ n) :
    ⦃⌜True⌝⦄
    evaluate (inp.toEnv (c := Builder V c) Pasta.vestaEndo symMdsQ lookupZero
      (fun _ => false) ulb) fqTokens
    ⦃⇓ a _ => ⌜a.val V = gateLinearization Pasta.vestaEndo symMdsQ α
      (inp.evals.map (·.val V))⌝⦄ :=
  circuit_gateLinearization Pasta.vestaEndo symMdsQ fqTokens
    (fun α β γ jc van e => evaluate_fqTokens α β γ jc van _ e) visited_fqTokens_noUlb ulb
    inp α fun n hn => htab n (alphaExponents_fqTokens_le n hn)

end Pickles.Reflect
