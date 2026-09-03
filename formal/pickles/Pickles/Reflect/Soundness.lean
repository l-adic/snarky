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
readings), `evaluate_congr` twice (the run reads the α-table only where the stream looks,
and never reaches the Lagrange basis, so the table is the powers of `α` and the gadget
drops out), and the stream's reflection endpoint from `Certificate.lean`. Nothing in it is
field-specific or specialised: the generic theorem takes the stream, the feature predicate,
the endpoint and the decided reachability fact as hypotheses, and only the two corollaries
fix them.

This is relative faithfulness: the circuit computes what the wire protocol computes.
Whether the wire protocol is sound is out of scope (`formal/docs/soundness-line-retirement.md`),
and completeness, that the honest prover run succeeds, is not proved here.
-/

namespace Pickles.Reflect

open Std.Do Snarky Pickles.Linearization Kimchi.Protocol.Linearization

/-- Any valuation satisfying the constraints the in-circuit interpreter emits reads its
output as `gateLinearization` at the readings of the circuit's inputs, for any stream with
reflection endpoint `hcert` under the feature predicate `feat`, given an α-table correct
up to `bound` (`htab`) and the decided fact that, under `feat`, the stream reads the
table no further than `bound` and never reads the Lagrange basis (`hreads`). The
Lagrange-basis gadget `ulb` is unconstrained. -/
theorem circuit_gateLinearization {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] {V : Valuation F}
    (endo : F) (mds : Kimchi.Gate.Poseidon.Mds F) (toks : Array PolishToken)
    (feat : FeatureFlag → Bool) (bound : Nat)
    (hcert : ∀ (α β γ jc van : F) (e : Evals F),
      (evaluate (e.toEnv endo mds (fun n => α ^ n) β γ jc van (fun _ _ => 0)
        LookupEvals.zero feat) toks : F) = gateLinearization endo mds α e)
    (hreads : ∀ i ∈ visitedAll toks feat, readsWithin toks bound i = true)
    (ulb : Bool → Int → CircuitM F (Builder V c) (FVar F)) (inp : Inputs F) (α : F)
    (htab : ∀ n ≤ bound, (inp.alphaPows n).val V = α ^ n) :
    ⦃⌜True⌝⦄
    evaluate (inp.toEnv (c := Builder V c) endo mds lookupZero feat ulb) toks
    ⦃⇓ a _ => ⌜a.val V = gateLinearization endo mds α (inp.evals.map (·.val V))⌝⦄ := by
  -- the compatibility, at the constant-zero gadget and the table's own readings
  have h := inputs_circuitCompatible (c := c) (V := V) endo mds lookupZero feat
    (fun _ _ => pure (.const 0)) (fun _ _ => 0) (fun _ _ => by mvcgen) inp
  rw [lookupZero_map] at h
  have hs := evaluate_spec h feat (fun _ _ _ => rfl) (fun _ _ _ => rfl) toks
  -- the pure side: the table's readings are the powers of `α` where the stream looks
  have hpure : ∀ i ∈ visitedAll toks feat,
      ((inp.evals.map (·.val V)).toEnv endo mds (fun n => (inp.alphaPows n).val V)
        (inp.beta.val V) (inp.gamma.val V) (inp.jointCombiner.val V) (inp.vanishes.val V)
        (fun _ _ => 0) LookupEvals.zero feat).agreeAt
      ((inp.evals.map (·.val V)).toEnv endo mds (fun n => α ^ n)
        (inp.beta.val V) (inp.gamma.val V) (inp.jointCombiner.val V) (inp.vanishes.val V)
        (fun _ _ => 0) LookupEvals.zero feat) toks i :=
    fun i hi => Evals.toEnv_agreeAt endo mds (fun n => (inp.alphaPows n).val V)
      (inp.beta.val V) (inp.gamma.val V) (inp.jointCombiner.val V) (inp.vanishes.val V)
      (fun _ _ => 0) LookupEvals.zero feat (inp.evals.map (·.val V)) (fun n => α ^ n)
      (fun _ _ => 0) toks i (fun n hn => htab n (readsWithin_alpha (hreads i hi) hn))
      (readsWithin_noUlb (hreads i hi))
  rw [evaluate_congr _ _ toks feat hpure (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl,
    hcert] at hs
  -- the circuit side: the gadget is never reached
  have hcirc : ∀ i ∈ visitedAll toks feat,
      (inp.toEnv (c := Builder V c) endo mds lookupZero feat ulb).agreeAt
      (inp.toEnv (c := Builder V c) endo mds lookupZero feat (fun _ _ => pure (.const 0)))
      toks i :=
    fun i hi => Inputs.toEnv_agreeAt endo mds lookupZero feat ulb
      (fun _ _ => pure (.const 0)) inp toks i (readsWithin_noUlb (hreads i hi))
  rw [evaluate_congr _ _ toks feat hcirc (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl]
  exact hs

/-! ## The deployed streams

One corollary per side of the cycle, each supplying its endpoint and reachability fact
from `Certificate.lean` under the modelled feature predicate, every feature disabled. A
precomputed α-table of length `alphaBound + 1` is all a caller owes. -/

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
  circuit_gateLinearization Pasta.pallasEndo symMds fpTokens (fun _ => false) alphaBound
    (fun α β γ jc van e => evaluate_fpTokens α β γ jc van _ e) fpTokens_reads ulb inp α
    htab

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
  circuit_gateLinearization Pasta.vestaEndo symMdsQ fqTokens (fun _ => false) alphaBound
    (fun α β γ jc van e => evaluate_fqTokens α β γ jc van _ e) fqTokens_reads ulb inp α
    htab

end Pickles.Reflect
