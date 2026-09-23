import Pickles.Reflect.Soundness
import Kimchi.Columns

set_option mvcgen.warning false

/-!
# The circuit computes `ftEval0`

The step verifier's `ftEval0` gadget — the permutation recurrence read at `ζ`, the public-input
evaluation, the accumulator boundary quotient and the interpreted gate linearization — proved
to compute the wire verifier's `Kimchi.Protocol.Linearization.ftEval0`. It transcribes, op for
op, the permutation contribution of `PlonkChecks.purs` followed by the constant-term
subtraction of `Step/FinalizeOtherProof.purs`.

## Main definitions

* `PermInputs`: the variables the permutation half reads beyond the interpreter's
  `Pickles.Linearization.Inputs`, and the coset shifts.
* `ftEval0Circuit`: the gadget, one body in the source's operation order.

## Main results

* `ftEval0Circuit_spec`: any valuation satisfying the emitted constraints reads the output
  as `ftEval0` at the readings of the inputs, for any stream with a reflection endpoint.
* `ftEval0Circuit_spec_fp`, `ftEval0Circuit_spec_fq`: the two deployed streams.

## Implementation notes

`zkPoly`, `zetaToNMinus1` and `omegaZk` are computed before the gadget, so here they are
inputs, each with a hypothesis saying what it reads as. One α-table hypothesis serves both
halves. The shifts are constants, so each product with one folds to a scaling in `Snarky.mul` and
emits no row.

The two folds are unrolled, over `sigmaRows` and `permCols` columns, with `β·ζ` recomputed
every step as the source does. The postcondition is stated against the members of `ftEval0`
(`sigmaSideEval`, `shiftSideEval`, `boundaryEval`, glued by `ftEval0_eq`).
`formal/scripts/check_cs.lean` compares the compiled constraint system row for row against
the harness `FtEval0Common.purs`, which pins the operation order.

`Snarky.div` reads as the field's total division (its inverse row makes a zero divisor
unsatisfiable), as `boundaryEval` does, so no `ζ ∉ {1, ω^{n − zkRows}}` hypothesis is needed.
-/

namespace Pickles

open Std.Do Snarky Pickles.Linearization Pickles.Reflect Kimchi.Protocol.Linearization
open scoped Kimchi

/-- The variables the permutation half of `ftEval0` reads beyond the interpreter's
`Inputs`, and the coset shifts. -/
structure PermInputs (F : Type) where
  /-- The evaluation point `ζ`. -/
  zeta : FVar F
  /-- The public-input polynomial at `ζ`. -/
  pubEval : FVar F
  /-- The permutation vanishing polynomial at `ζ`, computed upstream. -/
  zkPoly : FVar F
  /-- `ζⁿ − 1`, computed upstream. -/
  zetaToNMinus1 : FVar F
  /-- `ω^{n − zkRows}`, computed upstream. -/
  omegaZk : FVar F
  /-- The coset shifts, verifier-key constants. -/
  shifts : Fin permCols → F

variable {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]

/-- The `ftEval0` gadget: the permutation contribution minus the interpreted constant term,
in the source's operation order. -/
def ftEval0Circuit (endo : F) (mds : Kimchi.Gate.Poseidon.Mds F) (toks : Array PolishToken)
    (feat : FeatureFlag → Bool) (ulb : Bool → Int → CircuitM F c (FVar F))
    (inp : Inputs F) (ext : PermInputs F) : CircuitM F c (FVar F) := do
  let w := inp.evals.w
  let s := inp.evals.s
  let β := inp.beta
  let γ := inp.gamma
  let ζ := ext.zeta
  let a21 := inp.alphaPows 21
  let a22 := inp.alphaPows 22
  let a23 := inp.alphaPows 23
  -- σ side: the initial factor
  let t ← mul (CVar.add_ (w 6) γ) inp.evals.zOmega
  let t ← mul t a21
  let acc ← mul t ext.zkPoly
  -- σ side: the fold over the `sigmaRows` evaluated σ columns
  let bs ← mul β (s 0)
  let acc ← mul (CVar.add_ (CVar.add_ bs (w 0)) γ) acc
  let bs ← mul β (s 1)
  let acc ← mul (CVar.add_ (CVar.add_ bs (w 1)) γ) acc
  let bs ← mul β (s 2)
  let acc ← mul (CVar.add_ (CVar.add_ bs (w 2)) γ) acc
  let bs ← mul β (s 3)
  let acc ← mul (CVar.add_ (CVar.add_ bs (w 3)) γ) acc
  let bs ← mul β (s 4)
  let acc ← mul (CVar.add_ (CVar.add_ bs (w 4)) γ) acc
  let bs ← mul β (s 5)
  let term1 ← mul (CVar.add_ (CVar.add_ bs (w 5)) γ) acc
  let term1MinusP := CVar.sub_ term1 ext.pubEval
  -- shift side: the initial factor
  let t ← mul a21 ext.zkPoly
  let acc ← mul t inp.evals.z
  -- shift side: the fold over the `permCols` columns; `β·ζ` is recomputed every step
  let t ← mul β ζ
  let bzs ← mul t (.const (ext.shifts 0))
  let acc ← mul acc (CVar.add_ (CVar.add_ γ bzs) (w 0))
  let t ← mul β ζ
  let bzs ← mul t (.const (ext.shifts 1))
  let acc ← mul acc (CVar.add_ (CVar.add_ γ bzs) (w 1))
  let t ← mul β ζ
  let bzs ← mul t (.const (ext.shifts 2))
  let acc ← mul acc (CVar.add_ (CVar.add_ γ bzs) (w 2))
  let t ← mul β ζ
  let bzs ← mul t (.const (ext.shifts 3))
  let acc ← mul acc (CVar.add_ (CVar.add_ γ bzs) (w 3))
  let t ← mul β ζ
  let bzs ← mul t (.const (ext.shifts 4))
  let acc ← mul acc (CVar.add_ (CVar.add_ γ bzs) (w 4))
  let t ← mul β ζ
  let bzs ← mul t (.const (ext.shifts 5))
  let acc ← mul acc (CVar.add_ (CVar.add_ γ bzs) (w 5))
  let t ← mul β ζ
  let bzs ← mul t (.const (ext.shifts 6))
  let term2 ← mul acc (CVar.add_ (CVar.add_ γ bzs) (w 6))
  -- boundary quotient
  let zetaMinusOmegaZk := CVar.sub_ ζ ext.omegaZk
  let zetaMinus1 := CVar.sub_ ζ (.const 1)
  let t ← mul ext.zetaToNMinus1 a23
  let term23 ← mul t zetaMinus1
  let t ← mul ext.zetaToNMinus1 a22
  let term22 ← mul t zetaMinusOmegaZk
  let oneMinusZ := CVar.sub_ (.const 1) inp.evals.z
  let nominator ← mul (CVar.add_ term22 term23) oneMinusZ
  let denominator ← mul zetaMinusOmegaZk zetaMinus1
  let boundary ← div nominator denominator
  let permResult := CVar.add_ (CVar.sub_ term1MinusP term2) boundary
  -- the gate linearization's constant term
  let constantTerm ← evaluate (inp.toEnv endo mds lookupZero feat ulb) toks
  pure (CVar.sub_ permResult constantTerm)

/-- Under any valuation satisfying the emitted constraints, the output reads as `ftEval0` at
the inputs' readings, given the α-table reads as the powers of `α` up to `bound ≥ 23` and the
upstream inputs as `zkpmEval n zkRows ω ζ`, `ζⁿ − 1` and `ω^{n − zkRows}`. The stream
hypotheses `hcert` and `hreads` are those of `Pickles.Reflect.circuit_gateLinearization`. -/
private theorem ftEval0Circuit_spec [ConstraintHolds F c] [LawfulBasicSystem F c] {V : Valuation F}
    (endo : F) (mds : Kimchi.Gate.Poseidon.Mds F) (toks : Array PolishToken)
    (feat : FeatureFlag → Bool) (bound : Nat)
    (hcert : ∀ (α β γ jc van : F) (e : Evals F),
      (evaluate (e.toEnv endo mds (fun n => α ^ n) β γ jc van (fun _ _ => 0)
        LookupEvals.zero feat) toks : F) = gateLinearization endo mds α e)
    (hreads : ∀ i ∈ visitedAll toks feat, readsWithin toks bound i = true)
    (hbound : 23 ≤ bound)
    (ulb : Bool → Int → CircuitM F (Builder V c) (FVar F)) (inp : Inputs F)
    (ext : PermInputs F) (n zkRows : ℕ) (ω ζ α : F)
    (htab : ∀ k ≤ bound, (inp.alphaPows k).val V = α ^ k)
    (hζ : ext.zeta.val V = ζ)
    (hzk : ext.zkPoly.val V = zkpmEval n zkRows ω ζ)
    (hz1 : ext.zetaToNMinus1.val V = ζ ^ n - 1)
    (hω : ext.omegaZk.val V = ω ^ (n - zkRows)) :
    ⦃⌜True⌝⦄
    ftEval0Circuit (c := Builder V c) endo mds toks feat ulb inp ext
    ⦃⇓ a _ => ⌜a.val V = ftEval0 n zkRows ω ext.shifts endo mds α (inp.beta.val V)
      (inp.gamma.val V) ζ (ext.pubEval.val V) (inp.evals.map (·.val V))⌝⦄ := by
  have hlin := circuit_gateLinearization (c := c) (V := V) endo mds toks feat bound hcert
    hreads ulb inp α htab
  have h21 := htab 21 (by omega)
  have h22 := htab 22 (by omega)
  have h23 := htab 23 (by omega)
  clear htab hcert hreads
  simp only [ftEval0Circuit]
  -- the interpreter call is a black box to `mvcgen`: `hlin` is its only specification
  generalize evaluate (inp.toEnv (c := Builder V c) endo mds lookupZero feat ulb) toks = E
    at hlin ⊢
  mvcgen [hlin]
  simp only [CVar.val_add_, CVar.val_sub_, CVar.val, hζ, hzk, hz1, hω, h21, h22, h23] at *
  rw [ftEval0_eq]
  simp only [sigmaSideEval, shiftSideEval, boundaryEval, Fin.prod_univ_six,
    Fin.prod_univ_seven, Evals.map, Kimchi.sigmaCol, Kimchi.permCol, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Fin.reduceFinMk]
  clear hlin
  -- the chain of intermediate readings, substituted from the last back to the inputs;
  -- what remains differs from the members only in the association of the products
  simp only [*]
  ac_rfl

/-! ## The deployed streams

One corollary per side of the cycle, each supplying its stream, endpoint and reachability
fact as `circuit_gateLinearization_fp` and `circuit_gateLinearization_fq` do. -/

/-- The gadget over the `Fp` stream computes `ftEval0`. -/
theorem ftEval0Circuit_spec_fp {c : Type} [BasicSystem Fp c] [ConstraintHolds Fp c]
    [LawfulBasicSystem Fp c] {V : Valuation Fp}
    (ulb : Bool → Int → CircuitM Fp (Builder V c) (FVar Fp)) (inp : Inputs Fp)
    (ext : PermInputs Fp) (n zkRows : ℕ) (ω ζ α : Fp)
    (htab : ∀ k ≤ alphaBound, (inp.alphaPows k).val V = α ^ k)
    (hζ : ext.zeta.val V = ζ)
    (hzk : ext.zkPoly.val V = zkpmEval n zkRows ω ζ)
    (hz1 : ext.zetaToNMinus1.val V = ζ ^ n - 1)
    (hω : ext.omegaZk.val V = ω ^ (n - zkRows)) :
    ⦃⌜True⌝⦄
    ftEval0Circuit (c := Builder V c) Pasta.pallasEndo symMds fpTokens (fun _ => false) ulb
      inp ext
    ⦃⇓ a _ => ⌜a.val V = ftEval0 n zkRows ω ext.shifts Pasta.pallasEndo symMds α
      (inp.beta.val V) (inp.gamma.val V) ζ (ext.pubEval.val V)
      (inp.evals.map (·.val V))⌝⦄ :=
  ftEval0Circuit_spec Pasta.pallasEndo symMds fpTokens (fun _ => false) alphaBound
    (fun α β γ jc van e => evaluate_fpTokens α β γ jc van _ e) fpTokens_reads (by decide)
    ulb inp ext n zkRows ω ζ α htab hζ hzk hz1 hω

/-- The gadget over the `Fq` stream computes `ftEval0`. -/
theorem ftEval0Circuit_spec_fq {c : Type} [BasicSystem Fq c] [ConstraintHolds Fq c]
    [LawfulBasicSystem Fq c] {V : Valuation Fq}
    (ulb : Bool → Int → CircuitM Fq (Builder V c) (FVar Fq)) (inp : Inputs Fq)
    (ext : PermInputs Fq) (n zkRows : ℕ) (ω ζ α : Fq)
    (htab : ∀ k ≤ alphaBound, (inp.alphaPows k).val V = α ^ k)
    (hζ : ext.zeta.val V = ζ)
    (hzk : ext.zkPoly.val V = zkpmEval n zkRows ω ζ)
    (hz1 : ext.zetaToNMinus1.val V = ζ ^ n - 1)
    (hω : ext.omegaZk.val V = ω ^ (n - zkRows)) :
    ⦃⌜True⌝⦄
    ftEval0Circuit (c := Builder V c) Pasta.vestaEndo symMdsQ fqTokens (fun _ => false) ulb
      inp ext
    ⦃⇓ a _ => ⌜a.val V = ftEval0 n zkRows ω ext.shifts Pasta.vestaEndo symMdsQ α
      (inp.beta.val V) (inp.gamma.val V) ζ (ext.pubEval.val V)
      (inp.evals.map (·.val V))⌝⦄ :=
  ftEval0Circuit_spec Pasta.vestaEndo symMdsQ fqTokens (fun _ => false) alphaBound
    (fun α β γ jc van e => evaluate_fqTokens α β γ jc van _ e) fqTokens_reads (by decide)
    ulb inp ext n zkRows ω ζ α htab hζ hzk hz1 hω

/-! The gadget is sealed after its specs: a consumer composes `ftEval0Circuit_spec_fp` /
`ftEval0Circuit_spec_fq`, never the body. -/
attribute [irreducible] ftEval0Circuit

end Pickles
