import Pickles.FtEval0
import Pickles.IPA
import Pickles.CombinedInnerProduct
import Pickles.PermScalar
import Pickles.FrSponge
import Pickles.Domain
import Snarky.Types.Shifted

set_option mvcgen.warning false

/-!
# `finalize_other_proof`

Port of the PureScript `Pickles.Step.FinalizeOtherProof` and `Pickles.Wrap.FinalizeOtherProof`
(OCaml `step_verifier.ml`, `wrap_verifier.ml`): the circuit that checks the scalar-side
values a proof defers to the other field. `kimchiVerify` computes those values itself; the
group circuit cannot, so it takes them as claims from the public input and this circuit
recomputes each from the evaluations and compares.

## Main definitions

* `finalizeOtherProofCore`: the shared body from the expanded challenges on — `ζω`, the
  challenge polynomials, the fr-sponge, the `ζ^(2^k)` rows, the α-table, the generator
  powers, the zk polynomial, `ζⁿ − 1`, `ft_eval0`, the combined inner product, `b`, the
  permutation scalar, and the four checks combined.
* `finalizeOtherProofStep`, `finalizeOtherProofWrap`: each side's prelude — the challenge
  expansions in the side's order, the wrap side's seals, the step side's known-domain
  selection — and the side's shifted-value conventions.

## Implementation notes

The evaluations are one `PointEvaluations` per column: the one-chunk form. `zkRows` is a
parameter throughout, so the generator powers are not tied to it, but the chunk count is.
Known-domains mode only; the side-loaded path is a separate port.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Pickles.Linearization
open scoped Kimchi

variable {F c : Type} [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c]

/-- The public-input side of a proof to finalize (PS `PerProofUnfinalized`): the five 128-bit
prechallenges, the three shifted plonk scalars and the two shifted IPA scalars as their inner
variables (the side decides the shift encoding), the 16 raw bulletproof challenges, and the
fq-sponge digest before evaluations. -/
structure UnfinalizedProof (F : Type) where
  /-- The 128-bit `α` prechallenge. -/
  alpha : SizedF 128 (FVar F)
  /-- The 128-bit `β`. -/
  beta : SizedF 128 (FVar F)
  /-- The 128-bit `γ`. -/
  gamma : SizedF 128 (FVar F)
  /-- The 128-bit `ζ` prechallenge. -/
  zeta : SizedF 128 (FVar F)
  /-- The 128-bit `ξ` prechallenge. -/
  xi : SizedF 128 (FVar F)
  /-- The shifted `ζ^(srs length)`. -/
  zetaToSrsLength : FVar F
  /-- The shifted `ζⁿ`. -/
  zetaToDomainSize : FVar F
  /-- The shifted permutation scalar. -/
  perm : FVar F
  /-- The shifted combined inner product. -/
  combinedInnerProduct : FVar F
  /-- The shifted `b`. -/
  b : FVar F
  /-- The 16 raw 128-bit bulletproof challenges. -/
  bulletproofChallenges : List (SizedF 128 (FVar F))
  /-- The fq-sponge digest before evaluations. -/
  spongeDigestBeforeEvaluations : FVar F

/-- The witness evaluations (PS `ProofWitness`'s `AllEvals`): `ft(ζω)`, the public pair and
the proof's evaluations at `ζ` and `ζω`. -/
structure ProofWitness (F : Type) where
  /-- `ft(ζω)`. -/
  ftEval1 : FVar F
  /-- The public-input polynomial at `ζ` and `ζω`. -/
  pub : PointEvaluations (FVar F)
  /-- The proof's evaluations. -/
  evals : ProofEvaluations (FVar F)

/-- The side-independent parameters (PS `Params`, less the domains): the fr-sponge, the
scalar endomorphism `λ` the 128-bit expansions use, the linearization's endomorphism
coefficient, MDS matrix and token stream, the coset shifts, `srs_length_log2` and
`zk_rows`. -/
structure FopParams (F : Type) where
  /-- The fr-sponge parameters. -/
  sponge : Poseidon.Params F
  /-- The scalar endomorphism `λ` (`EndoScalar.toField`). -/
  endoLam : F
  /-- The linearization's endomorphism coefficient. -/
  endo : F
  /-- The Poseidon MDS matrix the linearization reads. -/
  mds : Kimchi.Gate.Poseidon.Mds F
  /-- The linearization's token stream. -/
  toks : Array PolishToken
  /-- The coset shifts. -/
  shifts : Fin permCols → F
  /-- `srs_length_log2`. -/
  srsLengthLog2 : ℕ
  /-- `zk_rows`. -/
  zkRows : ℕ

/-- The side's shifted-value conventions (PS `FopShiftOps`): the decode of a claim, and the
comparison of a claim with a computed scalar. -/
structure FopShiftOps (F c : Type) where
  /-- The decode of a shifted claim. -/
  unshift : FVar F → FVar F
  /-- The comparison of a shifted claim with a computed scalar. -/
  shiftedEqual : FVar F → FVar F → CircuitM F c (BoolVar F)

/-- The result (PS `Output`): the four checks and their conjunction, the raw and the expanded
bulletproof challenges. -/
structure FopOutput (F : Type) where
  /-- All four checks. -/
  finalized : BoolVar F
  /-- `ξ` recomputed equals the claim. -/
  xiCorrect : BoolVar F
  /-- `b` recomputed equals the claim. -/
  bCorrect : BoolVar F
  /-- The combined inner product recomputed equals the claim. -/
  cipCorrect : BoolVar F
  /-- The permutation scalar recomputed equals the claim. -/
  plonkOk : BoolVar F
  /-- The raw 128-bit bulletproof challenges. -/
  challenges : List (SizedF 128 (FVar F))
  /-- The bulletproof challenges expanded through `λ`. -/
  expandedChallenges : List (FVar F)

/-- The linearization's view of the evaluations: the `ζ` column of each, and `ζω` of the
witness and `z`. -/
def linEvals (e : ProofEvaluations (FVar F)) : Kimchi.Protocol.Linearization.Evals (FVar F) where
  w i := e.w[i].zeta
  wOmega i := e.w[i].zetaOmega
  z := e.z.zeta
  zOmega := e.z.zetaOmega
  s i := e.s[i].zeta
  coeffs i := e.coefficients[i].zeta
  genericSelector := e.genericSelector.zeta
  poseidonSelector := e.poseidonSelector.zeta
  completeAddSelector := e.completeAddSelector.zeta
  mulSelector := e.mulSelector.zeta
  emulSelector := e.emulSelector.zeta
  endoScalarSelector := e.endomulScalarSelector.zeta

/-- The 43 evaluations of a batch at one point in the combination order (PS
`extractEvalFields`): `z`, the six selectors, the 15 witness columns, the 15 coefficients,
the six `σ`. -/
def evalFields (proj : PointEvaluations (FVar F) → FVar F) (e : ProofEvaluations (FVar F)) :
    List (FVar F) :=
  proj e.z :: [proj e.genericSelector, proj e.poseidonSelector, proj e.completeAddSelector,
    proj e.mulSelector, proj e.emulSelector, proj e.endomulScalarSelector]
    ++ e.w.toList.map proj ++ e.coefficients.toList.map proj ++ e.s.toList.map proj

/-- The shared body from the expanded challenges on (PS steps 3–14 on either side): `ζω`,
the challenge polynomials at `ζω` then `ζ`, the fr-sponge with `ξ` compared to its claim,
`ξ` and `r` expanded, the `ζ^(2^k)` rows of both points, the α-table, the generator powers,
the zk polynomial, `ζⁿ − 1`, `ft_eval0`, the combined inner product against its claim, the
challenges expanded and `b` against its claim, the permutation scalar, the voided
`ζ^(2^srs)`, the shifted comparison, and the conjunction. -/
def finalizeOtherProofCore (P : FopParams F) (ops : FopShiftOps F c)
    (xiConstrainLowBits : Bool) (digest : CircuitM F c (FVar F)) (gen : FVar F)
    (pow2Log2 : ℕ) (vanishing : FVar F → CircuitM F c (FVar F)) (mask : List (BoolVar F))
    (u : UnfinalizedProof F) (w : ProofWitness F) (prev : List (List (FVar F)))
    (zeta alpha beta gamma perm : FVar F) : CircuitM F c (FopOutput F) := do
  let endoVar : FVar F := .const P.endoLam
  let zetaw ← mul gen zeta
  let sgZetaw ← challengePolyEvals zetaw prev
  let sgZeta ← challengePolyEvals zeta prev
  let (xiActual, rActual) ← squeezeXiR P.sponge u.spongeDigestBeforeEvaluations digest
    w.ftEval1 w.pub w.evals endoVar xiConstrainLowBits
  let xiCorrect ← equals xiActual.val u.xi.val
  let xi ← EndoScalar.toField 8 u.xi.val endoVar
  let r ← EndoScalar.toField 8 rActual.val endoVar
  let _ ← pow2PowSquare zeta pow2Log2
  let _ ← pow2PowSquare zetaw pow2Log2
  let pows ← precomputeAlphaPowers alpha
  let alphaPows (n : ℕ) : FVar F := pows[n]?.getD (.const 0)
  let omegas ← omegaPowers gen P.zkRows
  let zkPoly ← zkPolynomial zeta omegas
  let zetaToNMinus1 ← vanishing zeta
  let omegaFor (zk : Bool) (offset : Int) : FVar F :=
    match zk, offset with
    | false, 0 => .const 1
    | false, 1 => gen
    | false, -1 => omegas.omegaToMinus1
    | false, -2 => omegas.omegaToZkPlus1
    | false, -3 => omegas.omegaToZk
    | true, 0 => omegas.omegaToZk
    | _, _ => .const 1
  let ulb (zk : Bool) (offset : Int) : CircuitM F c (FVar F) :=
    div zetaToNMinus1 (CVar.sub_ zeta (omegaFor zk offset))
  let evals := linEvals w.evals
  let inp : Inputs F :=
    { evals := evals, alphaPows := alphaPows, beta := beta, gamma := gamma,
      jointCombiner := .const 1, vanishes := .const 1 }
  let ext : PermInputs F :=
    { zeta := zeta, pubEval := w.pub.zeta, zkPoly := zkPoly, zetaToNMinus1 := zetaToNMinus1,
      omegaZk := omegas.omegaToZk, shifts := P.shifts }
  let ftEval0 ← ftEval0Circuit P.endo P.mds P.toks (fun _ => false) ulb inp ext
  let actualCip ← combinedInnerProduct xi r
    (buildEvalList (mask.zip sgZeta) w.pub.zeta ftEval0 (evalFields (·.zeta) w.evals))
    (buildEvalList (mask.zip sgZetaw) w.pub.zetaOmega w.ftEval1
      (evalFields (·.zetaOmega) w.evals))
  let cipCorrect ← equals (ops.unshift u.combinedInnerProduct) actualCip
  let expanded ← computeChallenges endoVar (u.bulletproofChallenges.map (·.val))
  let bCorrect ← bCorrectCircuit expanded zeta zetaw r (ops.unshift u.b)
  let actualPerm ← permScalarCircuit (fun i => evals.w ⟨i, by omega⟩) evals.s evals.zOmega
    beta gamma zkPoly (alphaPows 21)
  let _ ← Snarky.pow zeta (2 ^ P.srsLengthLog2)
  let plonkOk ← ops.shiftedEqual perm actualPerm
  let finalized ← Snarky.all [xiCorrect, bCorrect, cipCorrect, plonkOk]
  pure ⟨finalized, xiCorrect, bCorrect, cipCorrect, plonkOk, u.bulletproofChallenges, expanded⟩

/-- A known domain the prev proof may have: its `log2` and generator. -/
structure KnownDomain (F : Type) where
  /-- `log2` of the domain size. -/
  log2 : ℕ
  /-- The domain generator `ω`. -/
  generator : F

/-- The step side's shifted-value conventions: Type1 claims, compared by encoding the
computed scalar. -/
def stepShiftOps : FopShiftOps F c where
  unshift x := Type1.fromShiftedCircuit 255 ⟨x⟩
  shiftedEqual claimed actual := equals claimed (Type1.ofFieldCircuit 255 actual)

/-- The wrap side's shifted-value conventions: Type2 claims, compared by decoding the
claim. -/
def wrapShiftOps : FopShiftOps F c where
  unshift x := Type2.fromShiftedCircuit 255 ⟨x⟩
  shiftedEqual claimed actual := equals (Type2.fromShiftedCircuit 255 ⟨claimed⟩) actual

/-- The step side (PS `finalizeOtherProofCircuit`, known-domains mode): `ζ` then `α`
expanded, the domain selected from the runtime `domain_log2` and its generator
mask-selected, then the core with the masked challenge digest, `ξ` by `squeeze_challenge`,
the `ζ^(2^srs)` rows and the known-domain vanishing polynomial. -/
def finalizeOtherProofStep (P : FopParams F) (domains : List (KnownDomain F))
    (u : UnfinalizedProof F) (w : ProofWitness F) (mask : List (BoolVar F))
    (prev : List (List (FVar F))) (domainLog2Var : FVar F) : CircuitM F c (FopOutput F) := do
  let endoVar : FVar F := .const P.endoLam
  let zeta ← EndoScalar.toField 8 u.zeta.val endoVar
  let alpha ← EndoScalar.toField 8 u.alpha.val endoVar
  let log2s := domains.map (·.log2)
  let whiches ← knownDomainWhiches domainLog2Var log2s
  let gen ← Pseudo.mask whiches (domains.map fun d => .const d.generator)
  let maxLog2 := log2s.foldl max 0
  finalizeOtherProofCore P stepShiftOps true (maskedChallengeDigest P.sponge mask prev) gen
    P.srsLengthLog2 (knownDomainVanishingPolynomial whiches log2s maxLog2) mask u w prev
    zeta alpha u.beta.val u.gamma.val u.perm

/-- The wrap side (PS `wrapFinalizeOtherProofCircuit`): `ζ`, `γ`, `β`, `α` in that order with
`γ`, `β` sealed, the three shifted plonk claims sealed, then the core at the constant
generator with the plain challenge digest, `ξ` by `squeeze_scalar`, the `ζ^(2^log2)` rows
and the caller's vanishing polynomial. -/
def finalizeOtherProofWrap (P : FopParams F) (gen : F) (domainLog2 : ℕ)
    (vanishing : FVar F → CircuitM F c (FVar F)) (u : UnfinalizedProof F)
    (w : ProofWitness F) (prev : List (List (FVar F))) : CircuitM F c (FopOutput F) := do
  let endoVar : FVar F := .const P.endoLam
  let zeta ← EndoScalar.toField 8 u.zeta.val endoVar
  let gamma ← sealVar u.gamma.val
  let beta ← sealVar u.beta.val
  let alpha ← EndoScalar.toField 8 u.alpha.val endoVar
  let perm ← sealVar u.perm
  let _ ← sealVar u.zetaToDomainSize
  let _ ← sealVar u.zetaToSrsLength
  finalizeOtherProofCore P wrapShiftOps false (challengeDigest P.sponge prev) (.const gen)
    domainLog2 vanishing (prev.map fun _ => true_) u w prev zeta alpha beta gamma perm

end Pickles
