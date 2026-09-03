import Pickles.Linearization.Circuit
import Pickles.Reflect.Certificate

/-!
# The circuit computes the gate linearization

Where the three developments meet.

* `Pickles.Linearization.evaluate_spec` — the constraints the in-circuit interpreter emits
  pin its output to the pure interpreter's value.
* `Pickles.Linearization.inputs_circuitCompatible` — the concrete circuit environment
  computes the specified one, with the α-table read as it is.
* `Pickles.Linearization.evaluate_withAlphaPow` — the run reads the table only at the
  stream's exponents, so a finite table discharges the identification with `α^n`.
* `Pickles.Reflect.evaluate_fpTokens` / `evaluate_fqTokens` — each deployed stream's pure
  value IS the closed-form gate linearization, and `alphaExponents_f{p,q}Tokens_le` — each
  reads the table no further than `alphaBound`.

Composing them gives a statement whose right-hand side is the verifier's own quantity
rather than a restatement of the token program: the gate contribution to `ftEval0`.

The composition is GENERIC — `circuit_gateLinearization` takes the stream and its
reflection endpoint as arguments and knows nothing of Pasta — because nothing in it is
field-specific; only the endpoint is. The two deployed corollaries instantiate it on each
side of the cycle: `circuit_gateLinearization_fp` for the `Fp` stream, where a Pallas proof
is verified, and `circuit_gateLinearization_fq` for the `Fq` stream, where a Vesta proof
is. Those two are the results this package stands behind, and the axiom gate roots them:
everything above is in their closure.

It is RELATIVE faithfulness. It says the circuit computes what the wire protocol computes;
whether the wire protocol is sound is a separate question and out of scope — see
`formal/docs/soundness-line-retirement.md`.

Completeness — that the honest prover run succeeds — is NOT proved here. Without it this
statement is satisfiable by a circuit no assignment satisfies, so it is half the story.
-/

namespace Pickles.Reflect

open Std.Do Snarky Pickles.Linearization Kimchi.Protocol.Linearization

/-- **The in-circuit reading of a certified stream computes the gate contribution to
`ftEval0`**, for a table correct where the stream looks. Any valuation satisfying the
emitted constraints reads the interpreter's output as `gateLinearization` at the readings
of the circuit's own inputs.

`hcert` is the stream's reflection endpoint — its pure value is the closed form at every
evaluation and every challenge — and is all that ties the statement to a particular
stream. The α-table obligation is on `alphaExponents toks` alone: the run reads the table
nowhere else (`evaluate_withAlphaPow`), so a caller with a finite table owes nothing about
the entries the stream never touches. The Lagrange-basis gadget `ulb` is unconstrained:
`hvis` says the disabled-features run never reaches one (`evaluate_withUlb`). -/
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

One corollary per side of the cycle. Each supplies its endpoint and its two decided
reachability facts from `Certificate.lean`, trading the exponent-set obligation for the
bound `alphaBound`: a precomputed table of that length is all a caller owes, and the
Lagrange-basis gadget is whatever the caller has. -/

/-- **The `Fp` stream in circuit computes the gate contribution to `ftEval0`** — Vesta's
scalar field, where a Pallas proof is verified. -/
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

/-- **The `Fq` stream in circuit computes the gate contribution to `ftEval0`** — Pallas's
scalar field, where a Vesta proof is verified. -/
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
