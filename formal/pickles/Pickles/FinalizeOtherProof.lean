import Pickles.FtEval0
import Pickles.IPA
import Pickles.CombinedInnerProduct
import Pickles.PermScalar
import Pickles.FrSponge
import Pickles.Domain
import Snarky.Types.Shifted
import Pickles.Statement
import Pickles.Prechallenge
import Pickles.Chunks

set_option mvcgen.warning false

/-!
# Finalizing the other proof

Port of `packages/pickles/src/Pickles/Step/FinalizeOtherProof.purs` and
`packages/pickles/src/Pickles/Wrap/FinalizeOtherProof.purs` (after OCaml `step_verifier.ml`,
`wrap_verifier.ml`): the circuit that checks the scalar-side values a proof defers to the
other field. `kimchiVerify` computes those values itself; the
group circuit cannot, so it takes them as claims from the public input and this circuit
recomputes each from the evaluations and compares.

## Main definitions

* `finalizeOtherProofCore`: the shared body from the expanded challenges on, at `nc` chunks
  per evaluation (`ChunkedEvals`): `ξ`, the combined inner product, `b` and the permutation
  scalar recomputed from the evaluations (`ftEval0Circuit` with the public chunks folded in),
  each checked against its claim, and the four checks combined.
* `finalizeOtherProofStep`, `finalizeOtherProofWrap`: each side's prelude — the challenge
  expansions in the side's order, the wrap side's seals, the step side's known-domain
  selection — and the side's shifted-value conventions (`FopShiftOps`, at the side's
  `Type1`/`Type2` claims). The claims arrive as an `UnfinalizedProof` of `Pickles.Statement`,
  the step statement's per-predecessor record.
* `FopShiftOps.Reading`: how a side's shift ops read under a valuation — the claim
  reading, its decode, and the two laws — one value per side (`stepShiftOps.reading`,
  `wrapShiftOps.reading`); `finalizeOtherProofCore_spec` takes one.
* `FopChecks`, `FopReads`, `FopReadsWire`: the readings the soundness theorems conclude —
  the three claim checks at given effective challenges; the exact reading of the whole
  circuit, its `ξ`, `r` as 128-bit splits of the wire verifier's `frSqueezes` below the
  modulus; and the deployed-field form, `ξ`, `r` the verifier's `frPrechallenges`.

## Implementation notes

The circuit and its readings are polymorphic in the chunk count: each column's chunks read
as `combineAt` at the evaluation points raised to `2^k` (`combineEvals`, the chunk combination
`KimchiProof.linEvals` performs), the public chunks as `combineAt` at `ζ^(2^srs)`, and the
batch as every chunk's row (`chunkRows`). `zkRows` is a parameter throughout.
Known-domains mode only; the side-loaded path is not modelled.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Pickles.Linearization
open scoped Kimchi

variable {F c : Type} [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c]
  {k : ℕ}

/-- The side-independent parameters: the fr-sponge, the scalar endomorphism `λ` the 128-bit
expansions use, the linearization's endomorphism coefficient, MDS matrix and token stream, the
coset shifts, the SRS length's `log2` and the zero-knowledge row count. -/
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
  /-- `log2` of the SRS length. -/
  srsLengthLog2 : ℕ
  /-- The number of zero-knowledge rows. -/
  zkRows : ℕ

/-- The side's shifted-value conventions: the decode of a claim, and the comparison of a
claim with a computed scalar. -/
structure FopShiftOps (F c sf : Type) where
  /-- The decode of a shifted claim. -/
  unshift : sf → FVar F
  /-- The comparison of a shifted claim with a computed scalar. -/
  shiftedEqual : sf → FVar F → CircuitM F c (BoolVar F)

/-- The result: the four checks and their conjunction, the raw and the expanded
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

/-- The linearization's view of the evaluations, over variables or values (the one-chunk
`KimchiProof.linEvals`): the `ζ` column of each, and `ζω` of the witness and `z`. -/
def linEvals {α : Type} (e : ProofEvaluations α) : Kimchi.Protocol.Linearization.Evals α where
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

/-- The evaluation rows of a batch in combination order: `z`, the six selectors, the 15
witness columns, the 15 coefficients, the six `σ`. -/
def evalRows {α : Type} (e : ProofEvaluations α) : List (PointEvaluations α) :=
  e.z :: [e.genericSelector, e.poseidonSelector, e.completeAddSelector, e.mulSelector,
    e.emulSelector, e.endomulScalarSelector] ++ e.w.toList ++ e.coefficients.toList ++ e.s.toList

/-- The three plonk comparisons: each computed scalar — the permutation scalar, `ζ^(2^srs)` and
`ζⁿ` at the call site — against its shifted claim by `shiftedEqual`, and the conjunction. -/
def plonkScalarsEqual {sf : Type} (ops : FopShiftOps F c sf) (perm zetaToSrs zetaToDomain : sf)
    (actualPerm actualZetaToSrs actualZetaToDomain : FVar F) : CircuitM F c (BoolVar F) := do
  let permOk ← ops.shiftedEqual perm actualPerm
  let zetaToSrsOk ← ops.shiftedEqual zetaToSrs actualZetaToSrs
  let zetaToDomainOk ← ops.shiftedEqual zetaToDomain actualZetaToDomain
  Snarky.all [permOk, zetaToSrsOk, zetaToDomainOk]

/-- The 43 columns' chunks at one point, in `evalRows` order, each column's chunks in order. -/
def evalFields {nc : ℕ} (proj : PointEvaluations (Vector (FVar F) nc) → Vector (FVar F) nc)
    (e : ProofEvaluations (Vector (FVar F) nc)) : List (FVar F) :=
  (evalRows e).flatMap fun col => (proj col).toList

/-- `buildEvalList` over chunked evaluations: the public chunks in place of the public
value. -/
def buildEvalListChunked (sgEvals : List (BoolVar F × FVar F)) (publicInput : List (FVar F))
    (ftEval : FVar F) (evals : List (FVar F)) : List (BoolVar F × FVar F) :=
  sgEvals ++ publicInput.map (true_, ·) ++ (true_, ftEval) :: evals.map (true_, ·)

/-- The shared body from the expanded challenges on, at `nc` chunks per evaluation: it
recomputes `ξ` from the fr-sponge over every chunk, the combined inner product over every
chunk, `b` and the permutation scalar, compares each with its claim (the shifted claims through
`ops`, the plonk ones by `plonkScalarsEqual`), and returns the four bits and their
conjunction. Each column's chunks are recombined at the `ζ^(2^k)` rows (`collapseEvals`). -/
def finalizeOtherProofCore {sf : Type} {nc : ℕ} (P : FopParams F) (ops : FopShiftOps F c sf)
    (xiConstrainLowBits : Bool) (digest : CircuitM F c (FVar F)) (gen : FVar F)
    (pow2Log2 : ℕ) (vanishing : FVar F → CircuitM F c (FVar F)) (mask : List (BoolVar F))
    (u : UnfinalizedProof k (FVar F) (BoolVar F) sf) (w : ChunkedEvals nc (FVar F))
    (prev : List (List (FVar F)))
    (zeta alpha beta gamma : FVar F) (perm zetaToSrs zetaToDomain : sf) :
    CircuitM F c (FopOutput F) := do
  let endoVar : FVar F := .const P.endoLam
  let zetaw ← mul gen zeta
  let sgZetaw ← challengePolyEvals zetaw prev
  let sgZeta ← challengePolyEvals zeta prev
  let (xiActual, rActual) ← squeezeXiR P.sponge u.spongeDigestBeforeEvaluations digest
    w.ftEval1 w.pub w.evals endoVar xiConstrainLowBits
  let xiCorrect ← equals xiActual.val u.deferredValues.xi.val
  let xi ← EndoScalar.toField 8 u.deferredValues.xi.val endoVar
  let r ← EndoScalar.toField 8 rActual.val endoVar
  let zetaPow ← pow2PowSquare zeta pow2Log2
  let zetaOmegaPow ← pow2PowSquare zetaw pow2Log2
  let collapsed ← collapseEvals zetaPow zetaOmegaPow w.evals
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
  let (pEval0, zetaToSrsHere) ← publicFold P.srsLengthLog2 zeta w.pub.zeta.toList
  let evals := linEvals collapsed
  let inp : Inputs F :=
    { evals := evals, alphaPows := alphaPows, beta := beta, gamma := gamma,
      jointCombiner := .const 1, vanishes := .const 1 }
  let ext : PermInputs F :=
    { zeta := zeta, pubEval := pEval0, zkPoly := zkPoly, zetaToNMinus1 := zetaToNMinus1,
      omegaZk := omegas.omegaToZk, shifts := P.shifts }
  let ftEval0 ← ftEval0Circuit P.endo P.mds P.toks (fun _ => false) ulb inp ext
  let actualCip ← combinedInnerProduct xi r
    (buildEvalListChunked (mask.zip sgZeta) w.pub.zeta.toList ftEval0
      (evalFields (·.zeta) w.evals))
    (buildEvalListChunked (mask.zip sgZetaw) w.pub.zetaOmega.toList w.ftEval1
      (evalFields (·.zetaOmega) w.evals))
  let cipCorrect ← equals (ops.unshift u.deferredValues.combinedInnerProduct) actualCip
  let expanded ← computeChallenges endoVar
    (u.deferredValues.bulletproofChallenges.toList.map (·.val))
  let bCorrect ← bCorrectCircuit expanded zeta zetaw r (ops.unshift u.deferredValues.b)
  let actualPerm ← permScalarCircuit (fun i => evals.w ⟨i, by omega⟩) evals.s evals.zOmega
    beta gamma zkPoly (alphaPows 21)
  let actualZetaToSrs ← zetaToSrsOr P.srsLengthLog2 zeta zetaToSrsHere
  let plonkOk ← plonkScalarsEqual ops perm zetaToSrs zetaToDomain actualPerm actualZetaToSrs
    (CVar.add_ zetaToNMinus1 (.const 1))
  let finalized ← Snarky.all [xiCorrect, bCorrect, cipCorrect, plonkOk]
  pure ⟨finalized, xiCorrect, bCorrect, cipCorrect, plonkOk,
    u.deferredValues.bulletproofChallenges.toList, expanded⟩

/-- A known domain the previous proof may have: its `log2` and generator. -/
structure KnownDomain (F : Type) where
  /-- `log2` of the domain size. -/
  log2 : ℕ
  /-- The domain generator `ω`. -/
  generator : F
deriving DecidableEq

/-- The step side's shifted-value conventions: Type1 claims, compared by encoding the
computed scalar. -/
def stepShiftOps : FopShiftOps F c (Type1 (FVar F)) where
  unshift x := Type1.fromShiftedCircuit 255 x
  shiftedEqual claimed actual := equals claimed.val (Type1.ofFieldCircuit 255 actual)

/-- The wrap side's shifted-value conventions: Type2 claims, compared by decoding the
claim. -/
def wrapShiftOps : FopShiftOps F c (Type2 (FVar F)) where
  unshift x := Type2.fromShiftedCircuit 255 x
  shiftedEqual claimed actual := equals (Type2.fromShiftedCircuit 255 claimed) actual

/-- The step side, known-domains mode: `ζ` then `α` expanded, the generator mask-selected
among `domains` by the runtime `domainLog2Var`, then `finalizeOtherProofCore` with the masked
challenge digest, the `ξ` low half constrained, the `ζ^(2^srs)` rows and the known-domain
vanishing polynomial. -/
def finalizeOtherProofStep {nc : ℕ} (P : FopParams F) (domains : List (KnownDomain F))
    (u : UnfinalizedProof k (FVar F) (BoolVar F) (Type1 (FVar F))) (w : ChunkedEvals nc (FVar F))
    (mask : List (BoolVar F))
    (prev : List (List (FVar F))) (domainLog2Var : FVar F) : CircuitM F c (FopOutput F) := do
  let endoVar : FVar F := .const P.endoLam
  let pl := u.deferredValues.plonk
  let zeta ← EndoScalar.toField 8 pl.zeta.val endoVar
  let alpha ← EndoScalar.toField 8 pl.alpha.val endoVar
  let log2s := domains.map (·.log2)
  let whiches ← knownDomainWhiches domainLog2Var log2s
  let gen ← Pseudo.choose whiches domains fun d => .const d.generator
  let maxLog2 := log2s.foldr max 0
  finalizeOtherProofCore P stepShiftOps true (maskedChallengeDigest P.sponge mask prev)
    gen P.srsLengthLog2 (knownDomainVanishingPolynomial whiches log2s maxLog2) mask u w prev
    zeta alpha pl.beta.val pl.gamma.val pl.perm pl.zetaToSrsLength pl.zetaToDomainSize

/-- The wrap side: `ζ`, `γ`, `β`, `α` in that order with `γ`, `β` sealed, the three shifted
plonk claims sealed, then `finalizeOtherProofCore` at the constant generator with the plain
challenge digest, the `ξ` low half constrained, the `ζ^(2^srs)` rows and the caller's
vanishing polynomial. -/
def finalizeOtherProofWrap {nc : ℕ} (P : FopParams F) (gen : F)
    (vanishing : FVar F → CircuitM F c (FVar F))
    (u : UnfinalizedProof k (FVar F) (BoolVar F) (Type2 (FVar F)))
    (w : ChunkedEvals nc (FVar F)) (prev : List (List (FVar F))) :
    CircuitM F c (FopOutput F) := do
  let endoVar : FVar F := .const P.endoLam
  let pl := u.deferredValues.plonk
  let zeta ← EndoScalar.toField 8 pl.zeta.val endoVar
  let gamma ← sealVar pl.gamma.val
  let beta ← sealVar pl.beta.val
  let alpha ← EndoScalar.toField 8 pl.alpha.val endoVar
  let perm ← sealVar pl.perm.val
  let zetaToDomain ← sealVar pl.zetaToDomainSize.val
  let zetaToSrs ← sealVar pl.zetaToSrsLength.val
  finalizeOtherProofCore P wrapShiftOps true (challengeDigest P.sponge prev) (.const gen)
    P.srsLengthLog2 vanishing (prev.map fun _ => true_) u w prev zeta alpha beta gamma
    ⟨perm⟩
    ⟨zetaToSrs⟩ ⟨zetaToDomain⟩

/-! ## The value side -/

/-- The kept challenge-polynomial rows: the `j`-th previous proof's `(b_j(ζ), b_j(ζω))` where
its mask bit is set. -/
def sgRows (ms : List Bool) (a b : List F) : List (PointEvaluations F) :=
  ((ms.zip (a.zip b)).filter (·.1)).map fun e => ⟨e.2.1, e.2.2⟩

omit [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- The linearization view is natural: reading the variables' view is the readings' view. -/
private theorem map_linEvals (V : Valuation F) (e : ProofEvaluations (FVar F)) :
    (linEvals e).map (·.val V) = linEvals (e.map (·.val V)) := by
  simp [linEvals, Kimchi.Protocol.Linearization.Evals.map, ProofEvaluations.map,
    PointEvaluations.map]

omit [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- The kept entries of the two masked zips are the two columns of the kept rows. -/
private theorem keptEvals_zip :
    ∀ (ms : List Bool) (a b : List F), a.length = b.length →
      keptEvals (ms.zip a) = (sgRows ms a b).map (·.zeta) ∧
      keptEvals (ms.zip b) = (sgRows ms a b).map (·.zetaOmega)
  | [], _, _, _ => by simp [keptEvals, sgRows]
  | _ :: _, [], [], _ => by simp [keptEvals, sgRows]
  | m :: ms, x :: a, y :: b, h => by
    have := keptEvals_zip ms a b (by simpa using h)
    cases m <;> simp [keptEvals, sgRows] at this ⊢ <;> exact this

omit [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- `sgRows` over two images of one list of challenge lists is the mask-kept challenge lists
under both maps. -/
theorem sgRows_kept (f g : List F → F) :
    ∀ (ms : List Bool) (cvs : List (List F)),
      sgRows ms (cvs.map f) (cvs.map g)
        = (List.zipWith (fun m cv => if m then [cv] else []) ms cvs).flatten.map
            fun cv => (⟨f cv, g cv⟩ : PointEvaluations F)
  | [], _ => by simp [sgRows]
  | _ :: _, [] => by simp [sgRows]
  | m :: ms, cv :: cvs => by
    have ih := sgRows_kept f g ms cvs
    cases m <;> simp [sgRows] at ih ⊢ <;> exact ih

omit [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- Zips read entrywise. -/
private theorem forall₂_zip {V : Valuation F} :
    ∀ {a : List (BoolVar F)} {as : List Bool} {b : List (FVar F)} {bs : List F},
      List.Forall₂ (CircuitType.Reads V) a as → List.Forall₂ (CircuitType.Reads V) b bs →
      List.Forall₂ (CircuitType.Reads V) (a.zip b) (as.zip bs)
  | [], [], _, _, .nil, _ => .nil
  | _ :: _, _ :: _, [], [], _, .nil => .nil
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons ha hrest, .cons hb hrest' =>
    .cons (CircuitType.reads_prod.mpr ⟨ha, hb⟩) (forall₂_zip hrest hrest')

omit [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- Four values reading as indicators are bits. -/
private theorem four_bits {α : Type} (v : α → F) (b₁ b₂ b₃ b₄ : α) (p₁ p₂ p₃ p₄ : Prop)
    [Decidable p₁] [Decidable p₂] [Decidable p₃] [Decidable p₄]
    (h₁ : v b₁ = if p₁ then 1 else 0) (h₂ : v b₂ = if p₂ then 1 else 0)
    (h₃ : v b₃ = if p₃ then 1 else 0) (h₄ : v b₄ = if p₄ then 1 else 0) :
    ∀ b ∈ [b₁, b₂, b₃, b₄], v b = 0 ∨ v b = 1 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, h₁, h₂, h₃,
    h₄]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> split <;> simp

/-! ## Soundness -/

section FinalizedBit

variable {V : Valuation F}

open Std.Do in
/-- `all` of four bits reads as a bit: it is one equality test on their sum. -/
private theorem all4_bit (a b d e : BoolVar F) :
    ⦃⌜True⌝⦄ Snarky.all (c := Builder V (KimchiConstraint F)) [a, b, d, e]
    ⦃⇓ r _ => ⌜∃ bb : Bool, (↑r : CVar F).val V = bit bb⌝⦄ := by
  simp only [Snarky.all]
  mvcgen
  intro hr
  split_ifs at hr
  · exact ⟨true, by rw [hr]; rfl⟩
  · exact ⟨false, by rw [hr]; rfl⟩

open Std.Do in
/-- Under any valuation satisfying the emitted constraints, `finalized` reads as a bit: the
conjunction of four checks is one equality test on their sum. -/
theorem finalizeOtherProofCore_finalized_bit {sf : Type} {nc : ℕ} (P : FopParams F)
    (ops : FopShiftOps F (Builder V (KimchiConstraint F)) sf) (xiConstrainLowBits : Bool)
    (digest : CircuitM F (Builder V (KimchiConstraint F)) (FVar F)) (gen : FVar F)
    (pow2Log2 : ℕ) (vanishing : FVar F → CircuitM F (Builder V (KimchiConstraint F)) (FVar F))
    (mask : List (BoolVar F)) (u : UnfinalizedProof k (FVar F) (BoolVar F) sf)
    (w : ChunkedEvals nc (FVar F)) (prev : List (List (FVar F)))
    (zeta alpha beta gamma : FVar F) (perm zetaToSrs zetaToDomain : sf) :
    ⦃⌜True⌝⦄ finalizeOtherProofCore P ops xiConstrainLowBits digest gen pow2Log2 vanishing mask u w
      prev zeta alpha beta gamma perm zetaToSrs zetaToDomain
    ⦃⇓ o _ => ⌜∃ b : Bool, (↑o.finalized : CVar F).val V = bit b⌝⦄ := by
  simp only [finalizeOtherProofCore]
  have h1 := fun a b => builder_spec_true (mul (c := Builder V (KimchiConstraint F)) a b)
  have h2 := fun pt l =>
    builder_spec_true (challengePolyEvals (c := Builder V (KimchiConstraint F)) pt l)
  have h3 := fun a b d e1 pu ev en x => builder_spec_true
    (squeezeXiR (c := Builder V (KimchiConstraint F)) (nc := nc) a b d e1 pu ev en x)
  have h4 := fun n x e =>
    builder_spec_true (EndoScalar.toField (c := Builder V (KimchiConstraint F)) n x e)
  have h5 := fun x n => builder_spec_true (pow2PowSquare (c := Builder V (KimchiConstraint F)) x n)
  have h6 := fun a b e =>
    builder_spec_true (collapseEvals (c := Builder V (KimchiConstraint F)) (nc := nc) a b e)
  have h7 := fun a =>
    builder_spec_true (precomputeAlphaPowers (c := Builder V (KimchiConstraint F)) a)
  have h8 := fun g n => builder_spec_true (omegaPowers (c := Builder V (KimchiConstraint F)) g n)
  have h9 := fun z o => builder_spec_true (zkPolynomial (c := Builder V (KimchiConstraint F)) z o)
  have h10 := fun z => builder_spec_true (vanishing z)
  have h11 := fun n z l =>
    builder_spec_true (publicFold (c := Builder V (KimchiConstraint F)) n z l)
  have h12 := fun e m t fe ul i x =>
    builder_spec_true (ftEval0Circuit (c := Builder V (KimchiConstraint F)) e m t fe ul i x)
  have h13 := fun a b l1 l2 =>
    builder_spec_true (combinedInnerProduct (c := Builder V (KimchiConstraint F)) a b l1 l2)
  have h14 := fun e l =>
    builder_spec_true (computeChallenges (c := Builder V (KimchiConstraint F)) e l)
  have h15 := fun l a b c' d =>
    builder_spec_true (bCorrectCircuit (c := Builder V (KimchiConstraint F)) l a b c' d)
  have h16 := fun a b c' d e f g =>
    builder_spec_true (permScalarCircuit (c := Builder V (KimchiConstraint F)) a b c' d e f g)
  have h17 := fun n z o =>
    builder_spec_true (zetaToSrsOr (c := Builder V (KimchiConstraint F)) n z o)
  have h18 := fun a b d e f g => builder_spec_true (plonkScalarsEqual ops a b d e f g)
  have hall := fun a b d e => all4_bit (V := V) a b d e
  mvcgen -trivial [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, hall, -Snarky.all_spec, -Snarky.Kimchi.EndoScalar.toField_spec]
  rename_i _ _ h
  exact h

open Std.Do in
/-- Under any valuation satisfying the emitted constraints, the step side's `finalized` reads
as a bit (`finalizeOtherProofCore_finalized_bit`). -/
theorem finalizeOtherProofStep_finalized_bit {nc : ℕ} (P : FopParams F)
    (domains : List (KnownDomain F)) (u : UnfinalizedProof k (FVar F) (BoolVar F) (Type1 (FVar F)))
    (w : ChunkedEvals nc (FVar F)) (mask : List (BoolVar F)) (prev : List (List (FVar F)))
    (domainLog2Var : FVar F) :
    ⦃⌜True⌝⦄ finalizeOtherProofStep (c := Builder V (KimchiConstraint F))
      P domains u w mask prev domainLog2Var
    ⦃⇓ o _ => ⌜∃ b : Bool, (↑o.finalized : CVar F).val V = bit b⌝⦄ := by
  simp only [finalizeOtherProofStep]
  have h1 := fun n x e =>
    builder_spec_true (EndoScalar.toField (c := Builder V (KimchiConstraint F)) n x e)
  have h2 := fun x l =>
    builder_spec_true (knownDomainWhiches (c := Builder V (KimchiConstraint F)) x l)
  have h3 := fun ws (l : List (KnownDomain F)) f =>
    builder_spec_true (Pseudo.choose (c := Builder V (KimchiConstraint F)) ws l f)
  have hcore := fun (g : FVar F)
      (van : FVar F → CircuitM F (Builder V (KimchiConstraint F)) (FVar F)) zeta alpha =>
    finalizeOtherProofCore_finalized_bit (V := V) P stepShiftOps true
      (maskedChallengeDigest P.sponge mask prev) g P.srsLengthLog2 van mask u w prev zeta alpha
      u.deferredValues.plonk.beta.val u.deferredValues.plonk.gamma.val
      u.deferredValues.plonk.perm u.deferredValues.plonk.zetaToSrsLength
      u.deferredValues.plonk.zetaToDomainSize
  mvcgen -trivial [h1, h2, h3, hcore, -Snarky.Kimchi.EndoScalar.toField_spec]

end FinalizedBit

open Kimchi.Protocol.Linearization Bulletproof Classical in
/-- The readings of the claim checks at effective challenges `ξ`, `r` and challenge readings
`cs`: each of `cipCorrect`, `bCorrect`, `plonkOk` reads as the indicator that the decoded claims
equal `combinedInnerProduct` over the read batch, `combinedB`, and `permScalar`, `ζ^(2^srs)`,
`ζⁿ`; `finalized` reads as the conjunction of the four bits; the expanded challenges read as
`cs`. The evaluations are recombined at `ζ^(2^srs)` and `(ζω)^(2^srs)` (`combineEvals`), and the
batch is the mask-kept challenge-polynomial rows (`sgRows`), every public chunk's row,
`(ft₀, ft(ζω))` with `ft₀` the `ftEval0` value, and every evaluation chunk's row. -/
def FopChecks {nc : ℕ} (P : FopParams F) (n : ℕ) (ω : F) (ms : List Bool) (cvs : List (List F))
    (w : ChunkedEvals nc (FVar F)) (ζ α β γ permV zetaMV zetaNV cipV bV : F) (unshiftV : F → F)
    (V : Valuation F) (o : FopOutput F) (ξ r : F) (cs : List F) : Prop :=
  let ev := w.evals.map fun v => v.map (·.val V)
  let pv := w.pub.map fun v => v.map (·.val V)
  let e := combineEvals (ζ ^ 2 ^ P.srsLengthLog2) ((ζ * ω) ^ 2 ^ P.srsLengthLog2) ev
  let ft₀ := ftEval0 n P.zkRows ω P.shifts P.endo P.mds α β γ ζ
    (combineAt (ζ ^ 2 ^ P.srsLengthLog2) pv.zeta.toArray) (linEvals e)
  let rows := sgRows ms (cvs.map fun cv => bPoly (fun i : Fin cv.length => cv.get i) ζ)
      (cvs.map fun cv => bPoly (fun i : Fin cv.length => cv.get i) (ζ * ω))
    ++ chunkRows pv ++ ⟨ft₀, w.ftEval1.val V⟩ :: (evalRows ev).flatMap chunkRows
  let cipOk := unshiftV cipV = Bulletproof.combinedInnerProduct ξ r
    (fun (i : Fin rows.length) (j : Fin evalPts) => ((rows.get i).toVector)[j])
  let bOk := unshiftV bV = combinedB (fun i : Fin cs.length => cs.get i) r ![ζ, ζ * ω]
  let permOk := unshiftV permV = permScalar β γ α (zkpmEval n P.zkRows ω ζ) (linEvals e)
  let zetaMOk := unshiftV zetaMV = ζ ^ 2 ^ P.srsLengthLog2
  let zetaNOk := unshiftV zetaNV = ζ ^ n
  (↑o.cipCorrect : CVar F).val V = (if cipOk then 1 else 0) ∧
  (↑o.bCorrect : CVar F).val V = (if bOk then 1 else 0) ∧
  (↑o.plonkOk : CVar F).val V = (if permOk ∧ zetaMOk ∧ zetaNOk then 1 else 0) ∧
  (↑o.finalized : CVar F).val V
    = (if (↑o.xiCorrect : CVar F).val V = 1 ∧ (↑o.bCorrect : CVar F).val V = 1 ∧
        (↑o.cipCorrect : CVar F).val V = 1 ∧ (↑o.plonkOk : CVar F).val V = 1 then 1 else 0) ∧
  List.Forall₂ (CircuitType.Reads V) o.expandedChallenges cs

open Kimchi.Protocol.Linearization Bulletproof Poseidon.FqSponge Classical in
/-- The exact reading of `finalizeOtherProofCore`'s outputs: with `(x₁, x₂)` the wire
verifier's two raw fr-sponge squeezes (`frSqueezes` of `frTranscript`), there are the
prechallenge `ξ₀` the `ξ` claim reads as, the recomputed low half `ξ'` of `x₁`, a prechallenge
`r'` splitting `x₂` below the modulus and the prechallenges `ĉ` of the challenge claims, such
that `xiCorrect` reads `[ξ' = ξ₀]` and `FopChecks` holds at `endoExpand` of `ξ₀`, `r'` and each `ĉ`.
`ξ'` is a prechallenge under `xiConstrainLowBits`, and any reading of it below `2¹²⁸` splits `x₁`
below the modulus. `FopReads.wire` restates this against the verifier's prechallenges. -/
def FopReads {sf : Type} {nc : ℕ} (P : FopParams F) (xiConstrainLowBits : Bool) (n : ℕ)
    (ω dv : F) (ms : List Bool) (cvs : List (List F))
    (u : UnfinalizedProof k (FVar F) (BoolVar F) sf) (w : ChunkedEvals nc (FVar F))
    (ζ α β γ permV zetaMV zetaNV cipV bV : F) (unshiftV : F → F) (V : Valuation F)
    (o : FopOutput F) : Prop :=
    let sq := frSqueezes P.sponge
      (frTranscript (u.spongeDigestBeforeEvaluations.val V) dv (w.ftEval1.val V)
        (w.pub.map fun v => v.map (·.val V)) (w.evals.map fun v => v.map (·.val V)))
    let x₁ := sq.1
    let x₂ := sq.2
    ∃ (ξ₀ r' : Prechallenge) (ξ' : F) (ĉ : List Prechallenge),
      Reads128 V u.deferredValues.xi ξ₀ ∧
      (xiConstrainLowBits = true → ∃ m : Prechallenge, ξ' = m.val) ∧
      (∀ lo : ℕ, lo < 2 ^ 128 → ξ' = lo →
        ∃ hi : ℕ, hi < 2 ^ 128 ∧ x₁ = (lo : F) + 2 ^ 128 * (hi : F) ∧
          lo + 2 ^ 128 * hi < fieldModulus F) ∧
      (∃ hi : ℕ, hi < 2 ^ 128 ∧ x₂ = (r'.val : F) + 2 ^ 128 * (hi : F) ∧
          r'.val + 2 ^ 128 * hi < fieldModulus F) ∧
      List.Forall₂ (Reads128 V) u.deferredValues.bulletproofChallenges.toList ĉ ∧
      (↑o.xiCorrect : CVar F).val V = (if ξ' = (ξ₀.val : F) then 1 else 0) ∧
      FopChecks P n ω ms cvs w ζ α β γ permV zetaMV zetaNV cipV bV unshiftV V o
        (endoExpand P.endoLam ξ₀.val)
        (endoExpand P.endoLam r'.val) (ĉ.map fun c => endoExpand P.endoLam c.val)

open Kimchi.Protocol.Linearization Poseidon.FqSponge in
/-- `FopReads` at a prime field, against the verifier's two prechallenges `pre` (`frPrechallenges`,
`frOracles`' own by `frOracles_eq_frPrechallenges`): the `r` the checks use is `pre.2`;
`xiCorrect` is a bit, and reading `1` it makes the `ξ` claim `pre.1`; under
`xiConstrainLowBits`, conversely, a `ξ` claim equal to `pre.1` reads `xiCorrect = 1`; and
`FopChecks` holds at the endo-expansions of the `ξ` claim, of `r` and of the challenge claims.
Without the constraint the recomputed low half may sit at or above `2¹²⁸`, so a claim equal to
`pre.1` can read `xiCorrect = 0`. -/
def FopReadsWire {p : ℕ} [Fact p.Prime] {sf : Type} {nc : ℕ} (P : FopParams (ZMod p))
    (xiConstrainLowBits : Bool) (n : ℕ) (ω dv : ZMod p) (ms : List Bool)
    (cvs : List (List (ZMod p))) (u : UnfinalizedProof k (FVar (ZMod p)) (BoolVar (ZMod p)) sf)
    (w : ChunkedEvals nc (FVar (ZMod p)))
    (ζ α β γ permV zetaMV zetaNV cipV bV : ZMod p) (unshiftV : ZMod p → ZMod p)
    (V : Valuation (ZMod p))
    (o : FopOutput (ZMod p)) : Prop :=
  let pre := frPrechallenges P.sponge
    (frTranscript (u.spongeDigestBeforeEvaluations.val V) dv (w.ftEval1.val V)
      (w.pub.map fun v => v.map (·.val V)) (w.evals.map fun v => v.map (·.val V)))
  ∃ (ξ₀ r' : Prechallenge) (ĉ : List Prechallenge),
    Reads128 V u.deferredValues.xi ξ₀ ∧ r'.val = pre.2 ∧
    ((↑o.xiCorrect : CVar (ZMod p)).val V = 0 ∨ (↑o.xiCorrect : CVar (ZMod p)).val V = 1) ∧
    ((↑o.xiCorrect : CVar (ZMod p)).val V = 1 → ξ₀.val = pre.1) ∧
    (xiConstrainLowBits = true → ξ₀.val = pre.1 → (↑o.xiCorrect : CVar (ZMod p)).val V = 1) ∧
    List.Forall₂ (Reads128 V) u.deferredValues.bulletproofChallenges.toList ĉ ∧
    FopChecks P n ω ms cvs w ζ α β γ permV zetaMV zetaNV cipV bV unshiftV V o
      (endoExpand P.endoLam ξ₀.val)
      (endoExpand P.endoLam r'.val) (ĉ.map fun c => endoExpand P.endoLam c.val)

/-- At a prime field, the exact reading is the wire reading: the splits of the verifier's raw
squeezes below the modulus are its prechallenges (`low128_of_split`), the `ξ` one once
`xiCorrect` identifies it with the 128-bit claim — and, under the low-half constraint, the
recomputed `ξ'` is that prechallenge outright, so a claim equal to it reads `xiCorrect = 1`. -/
theorem FopReads.wire {p : ℕ} [Fact p.Prime] {sf : Type} {nc : ℕ}
    {P : FopParams (ZMod p)} {xiConstrainLowBits : Bool} {n : ℕ} {ω dv : ZMod p} {ms : List Bool}
    {cvs : List (List (ZMod p))} {u : UnfinalizedProof k (FVar (ZMod p)) (BoolVar (ZMod p)) sf}
    {w : ChunkedEvals nc (FVar (ZMod p))}
    {ζ α β γ permV zetaMV zetaNV cipV bV : ZMod p} {unshiftV : ZMod p → ZMod p}
    {V : Valuation (ZMod p)}
    {o : FopOutput (ZMod p)}
    (h : FopReads P xiConstrainLowBits n ω dv ms cvs u w ζ α β γ permV zetaMV zetaNV cipV bV
      unshiftV V o) :
    FopReadsWire P xiConstrainLowBits n ω dv ms cvs u w ζ α β γ permV zetaMV zetaNV cipV bV
      unshiftV V o := by
  obtain ⟨ξ₀, r', ξ', ĉ, hxival, hcon, hx1, ⟨h₂, -, hx2, hlt2⟩, hĉ, hxiC, hchecks⟩ := h
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  refine ⟨ξ₀, r', ĉ, hxival, (low128_of_split _ r'.2 hx2 (fieldModulus_zmod p ▸ hlt2)).symm,
    ?_, ?_, ?_, hĉ, hchecks⟩
  · rw [hxiC]
    split <;> simp
  · intro hone
    rw [hxiC] at hone
    split at hone
    · rename_i heq
      obtain ⟨h₁, -, hx, hlt⟩ := hx1 ξ₀.val ξ₀.2 heq
      exact (low128_of_split _ ξ₀.2 hx (fieldModulus_zmod p ▸ hlt)).symm
    · exact absurd hone zero_ne_one
  · -- under the constraint the recomputed low half is the prechallenge itself
    intro hflag hξ
    obtain ⟨m, hm⟩ := hcon hflag
    obtain ⟨h₁, -, hx, hlt⟩ := hx1 m.val m.2 hm
    have hpre : m.val = _ := (low128_of_split _ m.2 hx (fieldModulus_zmod p ▸ hlt)).symm
    rw [hxiC, if_pos]
    rw [hm, hξ]
    exact congrArg Nat.cast hpre

open Kimchi.Protocol.Linearization in
/-- `ftEval0Circuit`'s reading at the domain size `n`, generator `ω` and the parameters'
linearization (`ftEval0Circuit_spec_fp`/`_fq` at the deployed fields): with the α-table
reading as the powers of `α` and the permutation inputs reading as `ζ`, `zkpmEval`, `ζⁿ − 1`
and `ω^(n − zkRows)`, the output reads as `ftEval0`. -/
def FtEval0Hyp (V : Valuation F) (P : FopParams F) (n : ℕ) (ω : F) : Prop :=
  ∀ (ulb : Bool → Int → CircuitM F (Builder V (KimchiConstraint F)) (FVar F))
    (inp : Inputs F) (ext : PermInputs F) (α ζ : F),
    (∀ k ≤ 70, (inp.alphaPows k).val V = α ^ k) → ext.zeta.val V = ζ →
    ext.zkPoly.val V = zkpmEval n P.zkRows ω ζ → ext.zetaToNMinus1.val V = ζ ^ n - 1 →
    ext.omegaZk.val V = ω ^ (n - P.zkRows) →
    ⦃⌜True⌝⦄ ftEval0Circuit (c := Builder V (KimchiConstraint F)) P.endo P.mds P.toks
      (fun _ => false) ulb inp ext
    ⦃⇓ a _ => ⌜a.val V = ftEval0 n P.zkRows ω ext.shifts P.endo P.mds α (inp.beta.val V)
      (inp.gamma.val V) ζ (ext.pubEval.val V) (inp.evals.map (·.val V))⌝⦄

omit [ToNat F] in
/-- How a side's shift ops read under `V` (the proof-side companion of `FopShiftOps`, one
value per side: `stepShiftOps.reading`, `wrapShiftOps.reading`): a claim reads as `read x`,
its circuit decode as `unshiftV` of that reading, and the comparison of a claim with a
scalar as the equality of the decode with the scalar's reading. -/
structure FopShiftOps.Reading {V : Valuation F} {sf : Type}
    (ops : FopShiftOps F (Builder V (KimchiConstraint F)) sf) where
  /-- The reading of a shifted claim. -/
  read : sf → F
  /-- The decode of a reading. -/
  unshiftV : F → F
  /-- The circuit decode reads as the decode of the reading. -/
  unshift : ∀ x, (ops.unshift x).val V = unshiftV (read x)
  /-- The comparison reads as the decoded claim against the scalar. -/
  cmp : ∀ (a : sf) (b : FVar F), ⦃⌜True⌝⦄ ops.shiftedEqual a b
    ⦃⇓ r _ => ⌜(↑r : CVar F).val V = if unshiftV (read a) = b.val V then 1 else 0⌝⦄

open Classical in
/-- `plonkScalarsEqual` reads `1` exactly when each claim's decode is the scalar beside it. -/
theorem plonkScalarsEqual_spec {V : Valuation F} (hinj : CastInj128 F) {sf : Type}
    (ops : FopShiftOps F (Builder V (KimchiConstraint F)) sf) (R : ops.Reading)
    (perm zetaToSrs zetaToDomain : sf) (actualPerm actualZetaToSrs actualZetaToDomain : FVar F) :
    ⦃⌜True⌝⦄ plonkScalarsEqual ops perm zetaToSrs zetaToDomain actualPerm actualZetaToSrs
      actualZetaToDomain
    ⦃⇓ r _ => ⌜(↑r : CVar F).val V =
      if R.unshiftV (R.read perm) = actualPerm.val V ∧
          R.unshiftV (R.read zetaToSrs) = actualZetaToSrs.val V ∧
          R.unshiftV (R.read zetaToDomain) = actualZetaToDomain.val V then 1 else 0⌝⦄ := by
  simp only [plonkScalarsEqual]
  have hcmp := R.cmp
  have hall := Snarky.all_spec (V := V) (c := KimchiConstraint F)
  mvcgen [hcmp, hall]
  case vc2 =>
    intro _ _ j k hj hk hjk
    exact hinj j k (by simp at hj; omega) (by simp at hk; omega) hjk
  rename_i _ p _ hp zs _ hzs zd _ hzd r _
  intro hr
  have hbits : ∀ b ∈ [p, zs, zd], (↑b : CVar F).val V = 0 ∨ (↑b : CVar F).val V = 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, hp, hzs,
      hzd]
    refine ⟨?_, ?_, ?_⟩ <;> split <;> simp
  rw [hr hbits]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, hp, hzs, hzd]
  by_cases h1 : R.unshiftV (R.read perm) = actualPerm.val V <;>
    by_cases h2 : R.unshiftV (R.read zetaToSrs) = actualZetaToSrs.val V <;>
    by_cases h3 : R.unshiftV (R.read zetaToDomain) = actualZetaToDomain.val V <;> simp [h1, h2, h3]

/-! ### The chunked batch -/

omit [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- The kept entries of a chunked batch: the kept masked entries, the public chunks, the `ft`
entry, and every evaluation chunk. -/
private theorem keptEvals_batch (sg : List (Bool × F)) (ps : List F) (f : F)
    (ev : List F) :
    keptEvals (sg ++ ps.map (true, ·) ++ (true, f) :: ev.map (true, ·))
      = keptEvals sg ++ ps ++ f :: ev := by
  simp [keptEvals, List.filter_append, List.filter_map, Function.comp_def]

omit [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- A chunked batch reads entrywise. -/
private theorem forall₂_buildEvalList {V : Valuation F} {mask : List (BoolVar F)}
    {ms : List Bool} {sg : List (FVar F)} {sgv : List F}
    (hm : List.Forall₂ (CircuitType.Reads V) mask ms)
    (hsg : List.Forall₂ (CircuitType.Reads V) sg sgv) (ps : List (FVar F)) (f : FVar F)
    (ev : List (FVar F)) :
    List.Forall₂ (CircuitType.Reads V) (buildEvalListChunked (mask.zip sg) ps f ev)
      ((ms.zip sgv) ++ (ps.map (·.val V)).map (true, ·) ++ (true, f.val V)
        :: (ev.map (·.val V)).map (true, ·)) := by
  have htrue : CircuitType.Reads V (true_ : BoolVar F) true :=
    CircuitType.reads_boolVar.mpr (by simp [true_, bit])
  have hall : ∀ l : List (FVar F), List.Forall₂ (CircuitType.Reads V) (l.map (true_, ·))
      ((l.map (·.val V)).map (true, ·)) := fun l => by
    rw [List.map_map, List.forall₂_map_right_iff, List.forall₂_map_left_iff]
    exact List.forall₂_same.mpr fun x _ =>
      CircuitType.reads_prod.mpr ⟨htrue, CircuitType.reads_fvar.mpr rfl⟩
  refine List.rel_append (List.rel_append (forall₂_zip hm hsg) (hall ps)) (.cons ?_ (hall ev))
  exact CircuitType.reads_prod.mpr ⟨htrue, CircuitType.reads_fvar.mpr rfl⟩

omit [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- A chunked batch's last entry is an always-kept entry. -/
private theorem getLast_batch (sg : List (Bool × F)) (ps : List F) (f : F)
    (ev : List F) :
    ∀ x ∈ (sg ++ ps.map (true, ·) ++ (true, f) :: ev.map (true, ·)).getLast?, x.1 = true := by
  intro x hx
  rw [List.getLast?_append, List.getLast?_cons, Option.some_or, List.getLast?_map,
    Option.mem_def, Option.some.injEq] at hx
  subst hx
  cases ev.getLast? <;> simp

omit [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- The chunked evaluation fields read as the chunks of the readings' rows. -/
private theorem map_evalFields {nc : ℕ} (V : Valuation F)
    (e : ProofEvaluations (Vector (FVar F) nc))
    (proj : ∀ {α : Type}, PointEvaluations (Vector α nc) → Vector α nc)
    (hproj : ∀ p : PointEvaluations (Vector (FVar F) nc),
      (proj p).map (·.val V) = proj (p.map fun v => v.map (·.val V))) :
    (evalFields proj e).map (·.val V)
      = (evalRows (e.map fun v => v.map (·.val V))).flatMap fun col => (proj col).toList := by
  simp [evalFields, evalRows, ProofEvaluations.map, Vector.toList_map, List.map_flatMap,
    List.flatMap_map, Function.comp_def, ← hproj]

omit [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- A column's rows, projected to a point, are that point's chunks. -/
theorem chunkRows_map {α : Type} {nc : ℕ} (e : PointEvaluations (Vector α nc)) :
    (chunkRows e).map (·.zeta) = e.zeta.toList ∧
      (chunkRows e).map (·.zetaOmega) = e.zetaOmega.toList := by
  constructor <;>
  · apply List.ext_getElem (by simp [chunkRows])
    intro i h₁ h₂
    simp [chunkRows, Vector.toList_zipWith]

open Kimchi.Protocol.Linearization Bulletproof Poseidon.FqSponge Classical in
/-- Under any valuation satisfying the emitted constraints, the generator reads non-zero and the
outputs read as `FopReads`, with `ω` the generator's reading (of order dividing `n` by `hω`),
the mask and the previous challenges reading as `ms` and `cvs`, the digest as `dv`, and the
shifted claims through the side's reading `R`. The side condition `hpow` fixes the point the
evaluation chunks recombine at: one chunk, or the `ζ^(2^srs)` rows. -/
theorem finalizeOtherProofCore_spec {V : Valuation F} (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hinj : CastInj128 F) (hsw : SplitWidth F)
    (P : FopParams F) (hsize : P.sponge.roundConstants.size = Poseidon.fullRounds)
    (h3zk : 3 ≤ P.zkRows) (n : ℕ) (hzk : P.zkRows ≤ n)
    {sf : Type} (ops : FopShiftOps F (Builder V (KimchiConstraint F)) sf) (R : ops.Reading)
    (u : UnfinalizedProof k (FVar F) (BoolVar F) sf) (perm zetaToSrs zetaToDomain : sf)
    (xiConstrainLowBits : Bool)
    (digest : CircuitM F (Builder V (KimchiConstraint F)) (FVar F))
    (dv : F) (hd : ⦃⌜True⌝⦄ digest ⦃⇓ d _ => ⌜d.val V = dv⌝⦄)
    (gen : FVar F) (hω : gen.val V ≠ 0 → gen.val V ^ n = 1) (pow2Log2 : ℕ)
    (vanishing : FVar F → CircuitM F (Builder V (KimchiConstraint F)) (FVar F))
    (hvan : gen.val V ≠ 0 → ∀ z, ⦃⌜True⌝⦄ vanishing z ⦃⇓ v _ => ⌜v.val V = z.val V ^ n - 1⌝⦄)
    (mask : List (BoolVar F)) (ms : List Bool) (hm : List.Forall₂ (CircuitType.Reads V) mask ms)
    {nc : ℕ} (w : ChunkedEvals nc (FVar F)) (hpow : nc = 1 ∨ pow2Log2 = P.srsLengthLog2)
    (prev : List (List (FVar F)))
    (cvs : List (List F)) (hprev : List.Forall₂ (List.Forall₂ (CircuitType.Reads V)) prev cvs)
    (zeta alpha beta gamma : FVar F) (hft : FtEval0Hyp V P n (gen.val V)) :
    ⦃⌜True⌝⦄ finalizeOtherProofCore (c := Builder V (KimchiConstraint F)) P ops
      xiConstrainLowBits digest gen pow2Log2 vanishing mask u w prev zeta alpha beta gamma perm
      zetaToSrs zetaToDomain
    ⦃⇓ o _ => ⌜gen.val V ≠ 0 ∧ FopReads P xiConstrainLowBits n (gen.val V) dv ms cvs u w
      (zeta.val V) (alpha.val V) (beta.val V) (gamma.val V) (R.read perm) (R.read zetaToSrs)
      (R.read zetaToDomain) (R.read u.deferredValues.combinedInnerProduct)
      (R.read u.deferredValues.b) R.unshiftV
      V o⌝⦄ := by
  simp only [finalizeOtherProofCore]
  have hcmp := plonkScalarsEqual_spec (V := V) hinj ops R perm zetaToSrs zetaToDomain
  have hsg := fun pt => challengePolyEvals_spec (V := V) (c := KimchiConstraint F) pt prev cvs hprev
  have htf := EndoScalar.toField_spec (V := V) h2 h3
  have hop := fun g => omegaPowers_spec (V := V) (c := KimchiConstraint F) g P.zkRows h3zk
  have hcip := fun (ξ r : FVar F) (ez ew : List (BoolVar F × FVar F)) =>
    builder_spec_forall (combinedInnerProduct (c := Builder V (KimchiConstraint F)) ξ r ez ew)
      (fun p : List (Bool × F) × List (Bool × F) × List (PointEvaluations F) =>
        List.Forall₂ (CircuitType.Reads V) ez p.1 ∧ List.Forall₂ (CircuitType.Reads V) ew p.2.1 ∧
        (∀ x ∈ p.1.getLast?, x.1 = true) ∧ (∀ x ∈ p.2.1.getLast?, x.1 = true) ∧
        keptEvals p.1 = p.2.2.map (·.zeta) ∧ keptEvals p.2.1 = p.2.2.map (·.zetaOmega))
      (fun p a => a.val V = Bulletproof.combinedInnerProduct (ξ.val V) (r.val V)
        (fun (i : Fin p.2.2.length) (j : Fin evalPts) => ((p.2.2.get i).toVector)[j]))
      (fun p hp => combinedInnerProduct_spec_cip ξ r ez ew p.1 p.2.1 hp.1 hp.2.1 hp.2.2.1
        hp.2.2.2.1 p.2.2 hp.2.2.2.2.1 hp.2.2.2.2.2)
  have hcc := computeChallenges_spec (V := V) h2 h3 (.const P.endoLam)
  have hbc := fun (chals : List (FVar F)) (zeta zetaOmega evalscale expectedB : FVar F) =>
    builder_spec_forall
      (bCorrectCircuit (c := Builder V (KimchiConstraint F)) chals zeta zetaOmega evalscale
        expectedB)
      (fun cs : List F => List.Forall₂ (CircuitType.Reads V) chals cs)
      (fun cs b => (↑b : CVar F).val V = if expectedB.val V
        = combinedB (fun i : Fin cs.length => cs.get i) (evalscale.val V)
            ![zeta.val V, zetaOmega.val V] then 1 else 0)
      (fun cs hc => bCorrectCircuit_spec chals zeta zetaOmega evalscale expectedB cs hc)
  have hps := fun (w s : Fin sigmaRows → FVar F) (zO b g zk a21 : FVar F) =>
    builder_spec_forall
      (permScalarCircuit (c := Builder V (KimchiConstraint F)) w s zO b g zk a21)
      (fun p : Evals F × F × F => (∀ i, (w i).val V = p.1.w (Kimchi.sigmaCol i)) ∧
        (∀ i, (s i).val V = p.1.s i) ∧ zO.val V = p.1.zOmega ∧ zk.val V = p.2.2 ∧
        a21.val V = p.2.1 ^ 21)
      (fun p a => a.val V = permScalar (b.val V) (g.val V) p.2.1 p.2.2 p.1)
      (fun p hp => permScalarCircuit_spec w s zO b g zk a21 p.1 p.2.1 p.2.2 hp.1 hp.2.1
        hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2)
  have hall := Snarky.all_spec (V := V) (c := KimchiConstraint F)
  have hft' := fun ulb inp ext => hft ulb inp ext (alpha.val V) (zeta.val V)
  clear hft
  have hvan' := fun z => builder_spec_forall (vanishing z) (fun _ : Unit => gen.val V ≠ 0)
    (fun _ v => v.val V = z.val V ^ n - 1) (fun _ h => hvan h z)
  clear hvan
  have hsq := squeezeXiR_spec (V := V) h2 h3 hsw P.sponge hsize u.spongeDigestBeforeEvaluations
    digest dv hd w.ftEval1 w.pub w.evals (.const P.endoLam) xiConstrainLowBits
  -- `hsq` is a fully applied triple over a concrete circuit: a tactic that unifies against
  -- the context (`contradiction` in `mvcgen`'s trivial pass, `assumption`) unfolds its `wp` at
  -- great cost, so the trivial pass is skipped and its four `2 ≠ 0`/`3 ≠ 0` conditions
  -- closed by tag once `hsq` is cleared
  have hcol := collapseEvals_spec (V := V) (c := KimchiConstraint F) (nc := nc)
  have hpf := publicFold_spec (V := V) (c := KimchiConstraint F) P.srsLengthLog2 zeta
  have hzs := fun o => builder_spec_forall
    (zetaToSrsOr (c := Builder V (KimchiConstraint F)) P.srsLengthLog2 zeta o)
    (fun _ : Unit => ∀ z ∈ o, z.val V = zeta.val V ^ 2 ^ P.srsLengthLog2)
    (fun _ r => r.val V = zeta.val V ^ 2 ^ P.srsLengthLog2)
    (fun _ h => zetaToSrsOr_spec P.srsLengthLog2 zeta o h)
  mvcgen -trivial [hsg, hsq, htf, pow2PowSquare_spec, hcol, precomputeAlphaPowers_spec, hop,
    zkPolynomial_spec, hvan', hpf, hft', hcip, hcc, hbc, hps, hzs, hcmp, hall]
  clear hsq
  case h2 => exact h2
  case h2 => exact h2
  case h3 => exact h3
  case h3 => exact h3
  -- the `FtEval0Hyp` premises and the characteristic bound of `all`, in whatever order they come
  all_goals try (first
    | exact ‹_ ∧ ∀ k ≤ 70, _›.2
    | rfl
    | (rename_i _ _ hom _ _ _ _ _ hz1 _ _ _
       exact hz1 () hom.1)
    | (rename_i om _ hom zkp _ hzkp _ _ _ _ _ _
       rw [hzkp]
       obtain ⟨hne, ho1, ho2, ho3⟩ := hom
       rw [ho1, ho2, ho3]
       exact zkPolynomial_eq_zkpmEval n P.zkRows _ _ (hω hne) hzk (by omega))
    | (rename_i om _ hom _ _ _ _ _ _ _ _ _
       obtain ⟨hne, -, -, ho3⟩ := hom
       rw [ho3]
       exact inv_pow_eq_pow_sub n P.zkRows _ (hω hne) hzk)
    | (intro j k hj hk hjk
       exact hinj j k (by simp at hj; omega) (by simp at hk; omega) hjk))
  rename_i _ zetaw _ hzw sgw _ hsgw sgz _ hsgz xr _ hsq' xiC _ hxiC xi _ hxi rr _ hr zP _ hzP
    zOP _ hzOP coll _ hcoll pows _ hpows om _ hom zkp _ hzkp z1 _ hz1 pf _ hpf ft0 _ hft0
    cipA _ cipC _ hcipC expd _ hexp bC _ hbC permA _ zM _ hzM plonkC _ hplonk fin _ hfin hcipA
    hpermA
  have hc : (CVar.const P.endoLam : CVar F).val V = P.endoLam := rfl
  rw [hc] at hxi hr hexp
  rw [mul_comm] at hzw
  obtain ⟨hx1, hx2, hlo, ⟨r'n, hrval⟩⟩ := hsq'
  obtain ⟨ξ₀, hξ₀, hxival, hxi'⟩ := hxi
  obtain ⟨m, hm', hrval', hr'⟩ := hr
  have hmr : m = r'n.val := hinj m r'n.val hm' r'n.property (by rw [← hrval', hrval])
  subst hmr
  obtain ⟨ns, hns, hexpd⟩ := hexp
  -- the recombination, at the verifier's `ζ^(2^srs)`: the side condition picks the point
  have hE : combineEvals (zP.val V) (zOP.val V) (w.evals.map fun v => v.map (·.val V))
      = combineEvals (zeta.val V ^ 2 ^ P.srsLengthLog2)
          ((zeta.val V * gen.val V) ^ 2 ^ P.srsLengthLog2)
          (w.evals.map fun v => v.map (·.val V)) := by
    rcases hpow with h1 | hp
    · subst h1
      rw [combineEvals_one, combineEvals_one]
    · rw [hzP, hzOP, hzw, hp]
  have hL : (linEvals coll).map (·.val V)
      = linEvals (combineEvals (zeta.val V ^ 2 ^ P.srsLengthLog2)
          ((zeta.val V * gen.val V) ^ 2 ^ P.srsLengthLog2)
          (w.evals.map fun v => v.map (·.val V))) := by
    rw [map_linEvals, hcoll, hE]
  have hp0 : pf.1.val V = combineAt (zeta.val V ^ 2 ^ P.srsLengthLog2)
      (w.pub.map fun (v : Vector (FVar F) nc) => v.map (·.val V)).zeta.toArray := by
    rw [hpf.1]
    simp [PointEvaluations.map, Vector.toList, ← Array.toList_map]
  -- the read batch: every public chunk's row, `ft`, every evaluation chunk's row
  have hlen : (cvs.map fun cv => bPoly (fun i : Fin cv.length => cv.get i) (zeta.val V)).length
      = (cvs.map fun cv =>
          bPoly (fun i : Fin cv.length => cv.get i) (zeta.val V * gen.val V)).length := by
    simp
  rw [hzw] at hsgw
  have hcipv := hcipA ⟨_, _, sgRows ms
      (cvs.map fun cv => bPoly (fun i : Fin cv.length => cv.get i) (zeta.val V))
      (cvs.map fun cv => bPoly (fun i : Fin cv.length => cv.get i) (zeta.val V * gen.val V))
      ++ chunkRows (w.pub.map fun v => v.map (·.val V))
      ++ ⟨ft0.val V, w.ftEval1.val V⟩
      :: (evalRows (w.evals.map fun v => v.map (·.val V))).flatMap chunkRows⟩
    (forall₂_buildEvalList hm hsgz _ _ _) (forall₂_buildEvalList hm hsgw _ _ _)
    (getLast_batch _ _ _ _) (getLast_batch _ _ _ _)
    (by rw [keptEvals_batch, (keptEvals_zip _ _ _ hlen).1,
          map_evalFields V _ (·.zeta) fun _ => rfl]
        simp [List.map_flatMap, (chunkRows_map _).1, PointEvaluations.map, Vector.toList_map])
    (by rw [keptEvals_batch, (keptEvals_zip _ _ _ hlen).2,
          map_evalFields V _ (·.zetaOmega) fun _ => rfl]
        simp [List.map_flatMap, (chunkRows_map _).2, PointEvaluations.map, Vector.toList_map])
  dsimp only at hcipv
  -- `b`
  have hbv := hbC _ hexpd
  -- the permutation scalar, at the recombined evaluations
  have hpv := hpermA ⟨linEvals (combineEvals (zeta.val V ^ 2 ^ P.srsLengthLog2)
        ((zeta.val V * gen.val V) ^ 2 ^ P.srsLengthLog2)
        (w.evals.map fun v => v.map (·.val V))), alpha.val V,
      zkpmEval n P.zkRows (gen.val V) (zeta.val V)⟩
    (fun i => by rw [← hL]; rfl)
    (fun i => by rw [← hL]; rfl)
    (by rw [← hL]; rfl)
    (by
      rw [hzkp]
      obtain ⟨hne, ho1, ho2, ho3⟩ := hom
      rw [ho1, ho2, ho3]
      exact zkPolynomial_eq_zkpmEval n P.zkRows _ _ (hω hne) hzk (by omega))
    (hpows.2 21 (by omega))
  -- the conjunction
  rw [hL, hp0] at hft0
  rw [hxival] at hxiC
  rw [R.unshift, hcipv, hxi', hr', hft0] at hcipC
  rw [R.unshift, hr', hzw] at hbv
  have hzN : (CVar.add_ z1 (CVar.const 1)).val V = zeta.val V ^ n := by
    simp [hz1 () hom.1]
  rw [hpv, hzM () hpf.2, hzN] at hplonk
  have hbool := four_bits (fun b : BoolVar F => (↑b : CVar F).val V) xiC bC cipC plonkC
    _ _ _ _ hxiC hbv hcipC hplonk
  constructor
  · exact hom.1
  dsimp only [FopReads, FopChecks]
  rw [hfin hbool]
  refine ⟨⟨ξ₀, hξ₀⟩, r'n, xr.1.val.val V, ns, hxival, hlo, hx1, hx2 _ r'n.2 hrval, ?_,
    hxiC, hcipC, hbv, hplonk, ?_, hexpd⟩
  · exact (List.forall₂_map_left_iff (f := fun x : SizedF 128 (FVar F) => x.val)).mp hns
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]

/-! ## The two sides -/

omit [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- A mask-select over readings: with the bits reading as `f` over the domains and each
domain's entry `g d` read by `r`, the sum of bit-times-entry is the sum over the domains. -/
private theorem zip_map_sum {V : Valuation F} {β : Type} (r : β → F) :
    ∀ (bits : List (BoolVar F)) (ds : List (KnownDomain F)) (f : KnownDomain F → F)
      (g : KnownDomain F → β),
      bits.map (fun b : BoolVar F => (↑b : CVar F).val V) = ds.map f →
      ((bits.zip (ds.map g)).map fun e => (↑e.1 : CVar F).val V * r e.2).sum
        = (ds.map fun d => f d * r (g d)).sum
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => nomatch h
  | _ :: _, [], _, _, h => nomatch h
  | b :: bits, d :: ds, f, g, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.map_cons, List.zip_cons_cons, List.sum_cons, h.1,
      zip_map_sum r bits ds f g h.2]

omit [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- With the `log2` values distinct and `L` one of them, the one-hot sum selects that
domain's entry. -/
private theorem onehot_sum (L : F) (c : KnownDomain F → F) :
    ∀ (ds : List (KnownDomain F)), (ds.map fun d => (d.log2 : F)).Nodup →
      ∀ d₀ ∈ ds, L = d₀.log2 →
      (ds.map fun d => (if L = (d.log2 : F) then (1 : F) else 0) * c d).sum = c d₀
  | [], _, _, h, _ => nomatch h
  | d :: ds, hnd, d₀, hd₀, hL => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hd₀ with rfl | hd₀'
    · have hzero :
          (ds.map fun d' => (if L = (d'.log2 : F) then (1 : F) else 0) * c d').sum = 0 := by
        rw [List.sum_eq_zero]
        intro x hx
        obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hx
        have : L ≠ d'.log2 := fun h => hnd.1 (List.mem_map.mpr ⟨d', hd', by rw [← h, hL]⟩)
        rw [if_neg this, zero_mul]
      rw [List.map_cons, List.sum_cons, if_pos hL, one_mul, hzero, add_zero]
    · have hne : L ≠ d.log2 := fun h => hnd.1 (List.mem_map.mpr ⟨d₀, hd₀', by rw [← hL, h]⟩)
      rw [List.map_cons, List.sum_cons, if_neg hne, zero_mul, zero_add]
      exact onehot_sum L c ds hnd.2 d₀ hd₀' hL

omit [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- With `L` none of the `log2` values, the one-hot sum is `0`. -/
private theorem onehot_sum_none (L : F) (c : KnownDomain F → F) (ds : List (KnownDomain F))
    (h : ∀ d ∈ ds, L ≠ d.log2) :
    (ds.map fun d => (if L = (d.log2 : F) then (1 : F) else 0) * c d).sum = 0 := by
  rw [List.sum_eq_zero]
  intro x hx
  obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hx
  rw [if_neg (h d' hd'), zero_mul]

omit [ToNat F] [KimchiSystem F c] in
/-- The step side's comparison reads as the decoded claim against the scalar. -/
private theorem stepShiftOps_cmp [ConstraintHolds F c] [LawfulBasicSystem F c] {V : Valuation F}
    (h2 : (2 : F) ≠ 0) (a : Type1 (FVar F)) (b : FVar F) :
    ⦃⌜True⌝⦄ (stepShiftOps (F := F) (c := Builder V c)).shiftedEqual a b
    ⦃⇓ r _ => ⌜(↑r : CVar F).val V
      = if Type1.fromShifted 255 ⟨a.val.val V⟩ = b.val V then 1 else 0⌝⦄ := by
  simp only [stepShiftOps]
  mvcgen
  intro h
  rw [h, Type1.val_ofFieldCircuit]
  by_cases hab : Type1.fromShifted 255 ⟨a.val.val V⟩ = b.val V
  · rw [if_pos hab, if_pos]
    rw [← hab]
    exact (Pasta.Shifted.shiftType1_unshiftType1 h2 255 (a.val.val V)).symm
  · rw [if_neg hab, if_neg]
    intro h'
    apply hab
    rw [h']
    exact Pasta.Shifted.unshiftType1_shiftType1 h2 255 (b.val V)

omit [ToNat F] [KimchiSystem F c] in
/-- The wrap side's comparison reads as the decoded claim against the scalar. -/
private theorem wrapShiftOps_cmp [ConstraintHolds F c] [LawfulBasicSystem F c] {V : Valuation F}
    (a : Type2 (FVar F)) (b : FVar F) :
    ⦃⌜True⌝⦄ (wrapShiftOps (F := F) (c := Builder V c)).shiftedEqual a b
    ⦃⇓ r _ => ⌜(↑r : CVar F).val V
      = if Type2.fromShifted 255 ⟨a.val.val V⟩ = b.val V then 1 else 0⌝⦄ := by
  simp only [wrapShiftOps]
  mvcgen
  intro h
  rw [h, Type2.val_fromShiftedCircuit]

omit [ToNat F] in
/-- The step side's reading: a Type1 claim reads as its representative, decoded by
`Type1.fromShifted 255`. -/
def stepShiftOps.reading {V : Valuation F} (h2 : (2 : F) ≠ 0) :
    (stepShiftOps (F := F) (c := Builder V (KimchiConstraint F))).Reading where
  read x := x.val.val V
  unshiftV x := Type1.fromShifted 255 ⟨x⟩
  unshift x := Type1.val_fromShiftedCircuit 255 x V
  cmp a b := stepShiftOps_cmp h2 a b

omit [ToNat F] in
/-- The wrap side's reading: a Type2 claim reads as its representative, decoded by
`Type2.fromShifted 255`. -/
def wrapShiftOps.reading {V : Valuation F} :
    (wrapShiftOps (F := F) (c := Builder V (KimchiConstraint F))).Reading where
  read x := x.val.val V
  unshiftV x := Type2.fromShifted 255 ⟨x⟩
  unshift x := Type2.val_fromShiftedCircuit 255 x V
  cmp a b := wrapShiftOps_cmp a b

open Kimchi.Protocol.Linearization Poseidon.FqSponge in
/-- The step side: under any valuation satisfying the emitted constraints, the runtime
`domainLog2Var` reads as one of the known domains' — `d₀`, of size `n = 2^log2` and generator
`ω` — and with `â, ẑ < 2¹²⁸` the `α, ζ` claims, the outputs read as `FopReads` at `ζ = endoExpand
λ ẑ`, `α = endoExpand λ â`, `β, γ` the raw claims, the digest of the mask-kept previous
challenges, `ξ` constrained below `2¹²⁸`, and the Type1 decode of the shifted claims. -/
theorem finalizeOtherProofStep_spec {V : Valuation F} (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hinj : CastInj128 F) (hsw : SplitWidth F)
    (P : FopParams F) (hsize : P.sponge.roundConstants.size = Poseidon.fullRounds)
    (h3zk : 3 ≤ P.zkRows) (domains : List (KnownDomain F))
    (hnodup : (domains.map fun d => (d.log2 : F)).Nodup)
    (hdom : ∀ d ∈ domains, P.zkRows ≤ 2 ^ d.log2 ∧ d.generator ^ 2 ^ d.log2 = 1)
    (u : UnfinalizedProof k (FVar F) (BoolVar F) (Type1 (FVar F)))
    {nc : ℕ} (w : ChunkedEvals nc (FVar F)) (mask : List (BoolVar F))
    (ms : List Bool) (hm : List.Forall₂ (CircuitType.Reads V) mask ms)
    (prev : List (List (FVar F)))
    (cvs : List (List F)) (hprev : List.Forall₂ (List.Forall₂ (CircuitType.Reads V)) prev cvs)
    (hprevlen : prev.flatten.length < 2 ^ 128) (domainLog2Var : FVar F)
    (hft : ∀ (n : ℕ) (ω : F), FtEval0Hyp V P n ω) :
    ⦃⌜True⌝⦄ finalizeOtherProofStep (c := Builder V (KimchiConstraint F)) P domains u w mask
      prev domainLog2Var
    ⦃⇓ o _ => ⌜∃ d₀, d₀ ∈ domains ∧ domainLog2Var.val V = (d₀.log2 : F) ∧
      ∃ a₀ z₀ : Prechallenge,
      Reads128 V u.deferredValues.plonk.alpha a₀ ∧ Reads128 V u.deferredValues.plonk.zeta z₀ ∧
      FopReads P true (2 ^ d₀.log2) d₀.generator
        (Poseidon.squeeze P.sponge (Poseidon.absorb P.sponge Poseidon.init
          (List.zipWith (fun m cs => if m then cs.map (·.val V) else []) ms prev).flatten)).1
        ms cvs u w (endoExpand P.endoLam z₀.val) (endoExpand P.endoLam a₀.val)
        (u.deferredValues.plonk.beta.val.val V) (u.deferredValues.plonk.gamma.val.val V)
        (u.deferredValues.plonk.perm.val.val V)
        (u.deferredValues.plonk.zetaToSrsLength.val.val V)
        (u.deferredValues.plonk.zetaToDomainSize.val.val V)
        (u.deferredValues.combinedInnerProduct.val.val V)
        (u.deferredValues.b.val.val V) (fun x => Type1.fromShifted 255 ⟨x⟩) V o⌝⦄ := by
  simp only [finalizeOtherProofStep]
  have htf := EndoScalar.toField_spec (V := V) h2 h3
  have hwh := knownDomainWhiches_spec (V := V) (c := KimchiConstraint F) domainLog2Var
    (domains.map (·.log2))
  have hmask := fun bits (xs : List (KnownDomain F)) f =>
    Pseudo.choose_spec (V := V) (c := KimchiConstraint F) bits xs f
  have hall3 : ∀ j k : ℕ, j ≤ 3 → k ≤ 3 → (j : F) = k → j = k := fun j k hj hk h =>
    hinj j k (by omega) (by omega) h
  have hchar : ∀ k : ℕ, k ≤ prev.flatten.length → (k : F) = 0 → k = 0 := fun k hk h =>
    hinj k 0 (by omega) (by omega) (by simpa using h)
  have hd := maskedChallengeDigest_spec (V := V) P.sponge hsize hall3 mask prev ms hm hchar
  have hcore := fun (gen : FVar F) (whiches : List (BoolVar F)) (zeta alpha : FVar F) =>
    builder_spec_forall
      (finalizeOtherProofCore (c := Builder V (KimchiConstraint F)) P stepShiftOps true
        (maskedChallengeDigest P.sponge mask prev) gen P.srsLengthLog2
        (knownDomainVanishingPolynomial whiches (domains.map (·.log2))
          ((domains.map (·.log2)).foldr max 0))
        mask u w prev zeta alpha u.deferredValues.plonk.beta.val u.deferredValues.plonk.gamma.val
        u.deferredValues.plonk.perm u.deferredValues.plonk.zetaToSrsLength
        u.deferredValues.plonk.zetaToDomainSize)
      (fun n : ℕ => P.zkRows ≤ n ∧ (gen.val V ≠ 0 → gen.val V ^ n = 1) ∧
        (gen.val V ≠ 0 → ∀ z, ⦃⌜True⌝⦄ knownDomainVanishingPolynomial
          (c := Builder V (KimchiConstraint F)) whiches (domains.map (·.log2))
          ((domains.map (·.log2)).foldr max 0) z ⦃⇓ v _ => ⌜v.val V = z.val V ^ n - 1⌝⦄))
      (fun n o => gen.val V ≠ 0 ∧ FopReads P true n (gen.val V) _ ms cvs u w (zeta.val V)
        (alpha.val V) (u.deferredValues.plonk.beta.val.val V)
        (u.deferredValues.plonk.gamma.val.val V) (u.deferredValues.plonk.perm.val.val V)
        (u.deferredValues.plonk.zetaToSrsLength.val.val V)
        (u.deferredValues.plonk.zetaToDomainSize.val.val V)
        (u.deferredValues.combinedInnerProduct.val.val V) (u.deferredValues.b.val.val V)
        (fun x => Type1.fromShifted 255 ⟨x⟩) V o)
      (fun n hn => finalizeOtherProofCore_spec h2 h3 hinj hsw P hsize h3zk n hn.1 stepShiftOps
        (stepShiftOps.reading h2) u u.deferredValues.plonk.perm
        u.deferredValues.plonk.zetaToSrsLength u.deferredValues.plonk.zetaToDomainSize true _ _ hd
        gen hn.2.1 _ _
        hn.2.2 mask ms hm w (Or.inr rfl) prev cvs hprev zeta alpha _ _ (hft n (gen.val V)))
  -- `hd` is a fully applied triple over a concrete circuit (see `finalizeOtherProofCore_spec`)
  clear hd
  mvcgen [htf, hwh, hmask, hcore]
  rename_i _ zeta _ hz alpha _ ha whiches _ hwh' gen _ hgen _ _
  intro hcore'
  obtain ⟨z₀, hz₀, hzval, hz'⟩ := hz
  obtain ⟨a₀, ha₀, haval, ha'⟩ := ha
  have hc : (CVar.const P.endoLam : CVar F).val V = P.endoLam := rfl
  rw [hc] at hz' ha'
  have hbits : whiches.map (fun b : BoolVar F => (↑b : CVar F).val V)
      = domains.map fun d => if domainLog2Var.val V = (d.log2 : F) then (1 : F) else 0 := by
    rw [hwh', List.map_map]
    rfl
  have hgenv : gen.val V = (domains.map fun d =>
      (if domainLog2Var.val V = (d.log2 : F) then (1 : F) else 0) * d.generator).sum := by
    have hsum := zip_map_sum (V := V) (fun d : KnownDomain F => (CVar.const d.generator).val V)
      whiches domains _ id hbits
    rw [List.map_id] at hsum
    rw [hgen, hsum]
    rfl
  by_cases hmatch : ∃ d₀ ∈ domains, domainLog2Var.val V = (d₀.log2 : F)
  · obtain ⟨d₀, hd₀, hL⟩ := hmatch
    obtain ⟨hzk₀, hω₀⟩ := hdom d₀ hd₀
    have hgen₀ : gen.val V = d₀.generator := by
      rw [hgenv]
      exact onehot_sum _ _ domains hnodup d₀ hd₀ hL
    have hvan₀ : ∀ z, ⦃⌜True⌝⦄ knownDomainVanishingPolynomial (c := Builder V (KimchiConstraint F))
        whiches (domains.map (·.log2)) ((domains.map (·.log2)).foldr max 0) z
        ⦃⇓ v _ => ⌜v.val V = z.val V ^ 2 ^ d₀.log2 - 1⌝⦄ := by
      intro z
      refine builder_spec_imp _ _ _ (knownDomainVanishingPolynomial_spec whiches
        (domains.map (·.log2)) ((domains.map (·.log2)).foldr max 0) z
        fun _ hl => List.le_max_of_le' 0 hl le_rfl)
        fun v hv => ?_
      rw [hv, zip_map_sum (fun l => z.val V ^ 2 ^ l) whiches domains _ _ hbits,
        onehot_sum _ _ domains hnodup d₀ hd₀ hL]
    obtain ⟨-, hreads⟩ := hcore' (2 ^ d₀.log2) hzk₀ (fun _ => by rw [hgen₀]; exact hω₀)
      (fun _ => hvan₀)
    refine ⟨d₀, hd₀, hL, ⟨a₀, ha₀⟩, ⟨z₀, hz₀⟩, haval, hzval, ?_⟩
    rw [hgen₀, hz', ha'] at hreads
    exact hreads
  · exfalso
    push Not at hmatch
    have hgen0 : gen.val V = 0 := by
      rw [hgenv]
      exact onehot_sum_none _ _ domains hmatch
    obtain ⟨hne, -⟩ := hcore' P.zkRows le_rfl (fun h => absurd hgen0 h) (fun h => absurd hgen0 h)
    exact hne hgen0

open Kimchi.Protocol.Linearization Poseidon.FqSponge in
/-- The wrap side: under any valuation satisfying the emitted constraints, with the constant
generator `ω` of order dividing `n` and the caller's vanishing polynomial reading `ζⁿ − 1`, and
`â, ẑ < 2¹²⁸` the `α, ζ` claims, the outputs read as `FopReads` at `ζ = endoExpand λ ẑ`,
`α = endoExpand λ â`, `β, γ` the raw claims, the digest of all previous challenges, `ξ`'s low
half range-checked, and the Type2 decode of the shifted claims. -/
theorem finalizeOtherProofWrap_spec {V : Valuation F} (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hinj : CastInj128 F) (hsw : SplitWidth F)
    (P : FopParams F) (hsize : P.sponge.roundConstants.size = Poseidon.fullRounds)
    (h3zk : 3 ≤ P.zkRows) (gen : F) (n : ℕ) (hzk : P.zkRows ≤ n) (hω : gen ^ n = 1)
    (vanishing : FVar F → CircuitM F (Builder V (KimchiConstraint F)) (FVar F))
    (hvan : ∀ z, ⦃⌜True⌝⦄ vanishing z ⦃⇓ v _ => ⌜v.val V = z.val V ^ n - 1⌝⦄)
    (u : UnfinalizedProof k (FVar F) (BoolVar F) (Type2 (FVar F))) {nc : ℕ}
    (w : ChunkedEvals nc (FVar F)) (prev : List (List (FVar F)))
    (cvs : List (List F)) (hprev : List.Forall₂ (List.Forall₂ (CircuitType.Reads V)) prev cvs)
    (hft : FtEval0Hyp V P n gen) :
    ⦃⌜True⌝⦄ finalizeOtherProofWrap (c := Builder V (KimchiConstraint F)) P gen
      vanishing u w prev
    ⦃⇓ o _ => ⌜∃ a₀ z₀ : Prechallenge,
      Reads128 V u.deferredValues.plonk.alpha a₀ ∧ Reads128 V u.deferredValues.plonk.zeta z₀ ∧
      FopReads P true n gen
        (Poseidon.squeeze P.sponge (Poseidon.absorb P.sponge Poseidon.init
          (prev.flatten.map (·.val V)))).1
        (prev.map fun _ => true) cvs u w (endoExpand P.endoLam z₀.val)
        (endoExpand P.endoLam a₀.val)
        (u.deferredValues.plonk.beta.val.val V) (u.deferredValues.plonk.gamma.val.val V)
        (u.deferredValues.plonk.perm.val.val V)
        (u.deferredValues.plonk.zetaToSrsLength.val.val V)
        (u.deferredValues.plonk.zetaToDomainSize.val.val V)
        (u.deferredValues.combinedInnerProduct.val.val V)
        (u.deferredValues.b.val.val V) (fun x => Type2.fromShifted 255 ⟨x⟩) V o⌝⦄ := by
  simp only [finalizeOtherProofWrap]
  have htf := EndoScalar.toField_spec (V := V) h2 h3
  have hd := challengeDigest_spec (V := V) P.sponge hsize prev
  have hm : List.Forall₂ (CircuitType.Reads V) (prev.map fun _ => (true_ : BoolVar F))
      (prev.map fun _ => true) :=
    List.forall₂_map_right_iff.mpr (List.forall₂_map_left_iff.mpr
      (List.forall₂_same.mpr fun _ _ => CircuitType.reads_boolVar.mpr (by simp [true_, bit])))
  have hcore := fun (zeta alpha beta gamma perm zetaToSrs zetaToDomain : FVar F) =>
    finalizeOtherProofCore_spec h2 h3 hinj hsw P hsize h3zk n hzk wrapShiftOps
      wrapShiftOps.reading u ⟨perm⟩ ⟨zetaToSrs⟩ ⟨zetaToDomain⟩ true _ _ hd (.const gen)
      (fun _ => hω) P.srsLengthLog2
      vanishing (fun _ => hvan) _ _ hm w (Or.inr rfl) prev cvs hprev zeta alpha beta
      gamma hft
  -- `hd` is a fully applied triple over a concrete circuit (see `finalizeOtherProofCore_spec`)
  clear hd
  mvcgen [htf, hcore]
  rename_i _ zeta _ hz gamma _ hγ beta _ hβ alpha _ ha perm _ hperm zd _ hzd zs _ hzs _ _
  intro _ hreads
  obtain ⟨z₀, hz₀, hzval, hz'⟩ := hz
  obtain ⟨a₀, ha₀, haval, ha'⟩ := ha
  have hc : (CVar.const P.endoLam : CVar F).val V = P.endoLam := rfl
  rw [hc] at hz' ha'
  refine ⟨⟨a₀, ha₀⟩, ⟨z₀, hz₀⟩, haval, hzval, ?_⟩
  dsimp only [wrapShiftOps.reading] at hreads
  rw [hz', ha', hβ, hγ, hperm, hzs, hzd] at hreads
  exact hreads

open Poseidon.FqSponge in
/-- **The deployed read**, the shape both deployed specs conclude: the `α` and `ζ` claims read
as prechallenges, and the outputs read as `FopReadsWire` at their endo-expansions, with `β`,
`γ` and the three shifted claims taken from the unfinalized proof's own cells, the shifted ones
through the side's claim reading `read` (`FopShiftOps.Reading.read`). The parameters the two
sides differ in are arguments: the low-half flag, the domain `(n, ω)`, the recursion digest
`dv`, the predecessor mask `ms`, the reading and the shift decode. So is the eigenvalue
`endoLam` the claims expand at, `P.endoLam` at the deployed specs. -/
def FopVerifyReads {p : ℕ} [Fact p.Prime] {sf : Type} {nc : ℕ} (P : FopParams (ZMod p))
    (xiConstrainLowBits : Bool) (n : ℕ) (ω dv : ZMod p) (ms : List Bool)
    (cvs : List (List (ZMod p))) (u : UnfinalizedProof k (FVar (ZMod p)) (BoolVar (ZMod p)) sf)
    (w : ChunkedEvals nc (FVar (ZMod p))) (endoLam : ZMod p) (read : sf → ZMod p)
    (unshiftV : ZMod p → ZMod p) (V : Valuation (ZMod p)) (o : FopOutput (ZMod p)) : Prop :=
  ∃ a₀ z₀ : Prechallenge,
    Reads128 V u.deferredValues.plonk.alpha a₀ ∧ Reads128 V u.deferredValues.plonk.zeta z₀ ∧
    FopReadsWire P xiConstrainLowBits n ω dv ms cvs u w
      (endoExpand endoLam z₀.val) (endoExpand endoLam a₀.val)
      (u.deferredValues.plonk.beta.val.val V) (u.deferredValues.plonk.gamma.val.val V)
      (read u.deferredValues.plonk.perm) (read u.deferredValues.plonk.zetaToSrsLength)
      (read u.deferredValues.plonk.zetaToDomainSize)
      (read u.deferredValues.combinedInnerProduct)
      (read u.deferredValues.b) unshiftV V o

/-! ## The deployed fields -/

section Deployed

open Pickles.Reflect Kimchi.Protocol.Linearization Poseidon.FqSponge

/-- `finalizeOtherProofStep_spec` at the step field over the deployed `Fp` linearization
(`Pasta.pallasEndo`, `symMds`, `fpTokens`), its `FtEval0Hyp` hypothesis discharged by
`ftEval0Circuit_spec_fp`. -/
theorem finalizeOtherProofStep_spec_fp {V : Valuation Fp} (P : FopParams Fp)
    (hP : P.endo = Pasta.pallasEndo ∧ P.mds = symMds ∧ P.toks = fpTokens)
    (hsize : P.sponge.roundConstants.size = Poseidon.fullRounds)
    (h3zk : 3 ≤ P.zkRows) (domains : List (KnownDomain Fp))
    (hnodup : (domains.map fun d => (d.log2 : Fp)).Nodup)
    (hdom : ∀ d ∈ domains, P.zkRows ≤ 2 ^ d.log2 ∧ d.generator ^ 2 ^ d.log2 = 1)
    (u : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    {nc : ℕ} (w : ChunkedEvals nc (FVar Fp)) (mask : List (BoolVar Fp))
    (ms : List Bool)
    (hm : List.Forall₂ (CircuitType.Reads V) mask ms) (prev : List (List (FVar Fp)))
    (cvs : List (List Fp)) (hprev : List.Forall₂ (List.Forall₂ (CircuitType.Reads V)) prev cvs)
    (hprevlen : prev.flatten.length < 2 ^ 128) (domainLog2Var : FVar Fp) :
    ⦃⌜True⌝⦄ finalizeOtherProofStep (c := Builder V (KimchiConstraint Fp)) P domains u w mask
      prev domainLog2Var
    ⦃⇓ o _ => ⌜∃ d₀, d₀ ∈ domains ∧ domainLog2Var.val V = (d₀.log2 : Fp) ∧
      FopVerifyReads P true (2 ^ d₀.log2) d₀.generator
        (Poseidon.squeeze P.sponge (Poseidon.absorb P.sponge Poseidon.init
          (List.zipWith (fun m cs => if m then cs.map (·.val V) else []) ms prev).flatten)).1
        ms cvs u w P.endoLam (fun x => x.val.val V)
        (fun x => Type1.fromShifted 255 ⟨x⟩) V o⌝⦄ :=
  builder_spec_imp _ _ _
    (finalizeOtherProofStep_spec (by decide) (by decide) (castInj128_of_lt _ (by decide))
      (SplitWidth.zmod (by decide) (by decide)) P hsize
      h3zk domains hnodup hdom u w mask ms hm prev cvs hprev hprevlen domainLog2Var
      fun n ω ulb inp ext α ζ htab hζ hzk hz1 hω => by
        obtain ⟨he, hmds, ht⟩ := hP
        rw [he, hmds, ht]
        exact ftEval0Circuit_spec_fp ulb inp ext n P.zkRows ω ζ α
          (fun k hk => htab k (le_trans hk (by decide))) hζ hzk hz1 hω)
    fun _ ⟨d₀, hd₀, hL, a₀, z₀, haval, hzval, hr⟩ =>
      ⟨d₀, hd₀, hL, a₀, z₀, haval, hzval, hr.wire⟩

/-- `finalizeOtherProofWrap_spec` at the wrap field over the deployed `Fq` linearization
(`Pasta.vestaEndo`, `symMdsQ`, `fqTokens`), its `FtEval0Hyp` hypothesis discharged by
`ftEval0Circuit_spec_fq`. -/
theorem finalizeOtherProofWrap_spec_fq {V : Valuation Fq} (P : FopParams Fq)
    (hP : P.endo = Pasta.vestaEndo ∧ P.mds = symMdsQ ∧ P.toks = fqTokens)
    (hsize : P.sponge.roundConstants.size = Poseidon.fullRounds)
    (h3zk : 3 ≤ P.zkRows) (gen : Fq) (n : ℕ) (hzk : P.zkRows ≤ n) (hω : gen ^ n = 1)
    (vanishing : FVar Fq → CircuitM Fq (Builder V (KimchiConstraint Fq)) (FVar Fq))
    (hvan : ∀ z, ⦃⌜True⌝⦄ vanishing z ⦃⇓ v _ => ⌜v.val V = z.val V ^ n - 1⌝⦄)
    (u : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq))) {nc : ℕ}
    (w : ChunkedEvals nc (FVar Fq))
    (prev : List (List (FVar Fq)))
    (cvs : List (List Fq)) (hprev : List.Forall₂ (List.Forall₂ (CircuitType.Reads V)) prev cvs) :
    ⦃⌜True⌝⦄ finalizeOtherProofWrap (c := Builder V (KimchiConstraint Fq)) P gen
      vanishing u w prev
    ⦃⇓ o _ => ⌜FopVerifyReads P true n gen
      (Poseidon.squeeze P.sponge (Poseidon.absorb P.sponge Poseidon.init
        (prev.flatten.map (·.val V)))).1
      (prev.map fun _ => true) cvs u w P.endoLam (fun x => x.val.val V)
      (fun x => Type2.fromShifted 255 ⟨x⟩) V o⌝⦄ :=
  builder_spec_imp _ _ _
    (finalizeOtherProofWrap_spec (by decide) (by decide) (castInj128_of_lt _ (by decide))
      (SplitWidth.zmod (by decide) (by decide)) P hsize
      h3zk gen n hzk hω vanishing hvan u w prev cvs hprev
      fun ulb inp ext α ζ htab hζ hzk' hz1 hω' => by
        obtain ⟨he, hmds, ht⟩ := hP
        rw [he, hmds, ht]
        exact ftEval0Circuit_spec_fq ulb inp ext n P.zkRows gen ζ α
          (fun k hk => htab k (le_trans hk (by decide))) hζ hzk' hz1 hω')
    fun _ ⟨a₀, z₀, haval, hzval, hr⟩ =>
      ⟨a₀, z₀, haval, hzval, hr.wire⟩

end Deployed

/-! The gadgets are sealed after their reads: a consumer composes `finalizeOtherProofStep_spec`
and `finalizeOtherProofWrap_spec` (or their deployed-field forms), never the bodies. -/
attribute [irreducible] finalizeOtherProofCore finalizeOtherProofStep finalizeOtherProofWrap

end Pickles
