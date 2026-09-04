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
  let maxLog2 := log2s.foldr max 0
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

/-! ## The value side -/

open Kimchi.Protocol.Linearization in
/-- The one-chunk value of the evaluations (`KimchiProof.linEvals` at a single chunk): the
`ζ` column of each, and `ζω` of the witness and `z`. -/
def oneChunkEvals (e : ProofEvaluations F) : Evals F where
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

/-- The evaluation rows of a read batch in combination order: `z`, the six selectors, the
15 witness columns, the 15 coefficients, the six `σ`. -/
def evalRows (e : ProofEvaluations F) : List (PointEvaluations F) :=
  e.z :: [e.genericSelector, e.poseidonSelector, e.completeAddSelector, e.mulSelector,
    e.emulSelector, e.endomulScalarSelector] ++ e.w.toList ++ e.coefficients.toList ++ e.s.toList

/-- The kept challenge-polynomial rows: the `j`-th previous proof's `(b_j(ζ), b_j(ζω))` where
its mask bit is set. -/
def sgRows (ms : List Bool) (a b : List F) : List (PointEvaluations F) :=
  ((ms.zip (a.zip b)).filter (·.1)).map fun e => ⟨e.2.1, e.2.2⟩

omit [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- The circuit's linearization view reads as the one-chunk value. -/
private theorem map_linEvals (V : Valuation F) (e : ProofEvaluations (FVar F)) :
    (linEvals e).map (·.val V) = oneChunkEvals (e.map (·.val V)) := by
  simp [linEvals, oneChunkEvals, Kimchi.Protocol.Linearization.Evals.map,
    ProofEvaluations.map, PointEvaluations.map]

omit [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- The `ζ` column of the evaluation fields reads as the rows' `ζ` column. -/
private theorem map_evalFields_zeta (V : Valuation F) (e : ProofEvaluations (FVar F)) :
    (evalFields (·.zeta) e).map (·.val V) = (evalRows (e.map (·.val V))).map (·.zeta) := by
  simp [evalFields, evalRows, ProofEvaluations.map, PointEvaluations.map, Vector.toList_map,
    List.map_map, Function.comp_def]

omit [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- The `ζω` column of the evaluation fields reads as the rows' `ζω` column. -/
private theorem map_evalFields_zetaOmega (V : Valuation F) (e : ProofEvaluations (FVar F)) :
    (evalFields (·.zetaOmega) e).map (·.val V)
      = (evalRows (e.map (·.val V))).map (·.zetaOmega) := by
  simp [evalFields, evalRows, ProofEvaluations.map, PointEvaluations.map, Vector.toList_map,
    List.map_map, Function.comp_def]

omit [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- The kept entries of a masked zip are the `ζ` column of the kept rows. -/
private theorem keptEvals_zip_left :
    ∀ (ms : List Bool) (a b : List F), a.length = b.length →
      keptEvals (ms.zip a) = (sgRows ms a b).map (·.zeta)
  | [], _, _, _ => by simp [keptEvals, sgRows]
  | _ :: _, [], [], _ => by simp [keptEvals, sgRows]
  | m :: ms, x :: a, y :: b, h => by
    have := keptEvals_zip_left ms a b (by simpa using h)
    cases m <;> simp [keptEvals, sgRows] at this ⊢ <;> exact this

omit [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- The kept entries of a masked zip are the `ζω` column of the kept rows. -/
private theorem keptEvals_zip_right :
    ∀ (ms : List Bool) (a b : List F), a.length = b.length →
      keptEvals (ms.zip b) = (sgRows ms a b).map (·.zetaOmega)
  | [], _, _, _ => by simp [keptEvals, sgRows]
  | _ :: _, [], [], _ => by simp [keptEvals, sgRows]
  | m :: ms, x :: a, y :: b, h => by
    have := keptEvals_zip_right ms a b (by simpa using h)
    cases m <;> simp [keptEvals, sgRows] at this ⊢ <;> exact this

omit [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- The kept entries of a batch: the kept masked entries, the public and `ft` entries, and
every evaluation. -/
private theorem keptEvals_batch (sg : List (Bool × F)) (p f : F) (ev : List F) :
    keptEvals (sg ++ (true, p) :: (true, f) :: ev.map (true, ·))
      = keptEvals sg ++ p :: f :: ev := by
  simp [keptEvals, List.filter_append, List.filter_map, Function.comp_def]

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
/-- A batch reads entrywise: the masked entries, then the always-kept public, `ft` and
evaluation entries. -/
private theorem forall₂_buildEvalList {V : Valuation F} {mask : List (BoolVar F)}
    {ms : List Bool} {sg : List (FVar F)} {sgv : List F}
    (hm : List.Forall₂ (CircuitType.Reads V) mask ms)
    (hsg : List.Forall₂ (CircuitType.Reads V) sg sgv) (p f : FVar F) (ev : List (FVar F)) :
    List.Forall₂ (CircuitType.Reads V) (buildEvalList (mask.zip sg) p f ev)
      ((ms.zip sgv) ++ (true, p.val V) :: (true, f.val V) :: (ev.map (·.val V)).map (true, ·)) := by
  have htrue : CircuitType.Reads V (true_ : BoolVar F) true :=
    CircuitType.reads_boolVar.mpr (by simp [true_, bit])
  refine List.rel_append (forall₂_zip hm hsg) (.cons ?_ (.cons ?_ ?_))
  · exact CircuitType.reads_prod.mpr ⟨htrue, CircuitType.reads_fvar.mpr rfl⟩
  · exact CircuitType.reads_prod.mpr ⟨htrue, CircuitType.reads_fvar.mpr rfl⟩
  · rw [List.map_map, List.forall₂_map_right_iff, List.forall₂_map_left_iff]
    exact List.forall₂_same.mpr fun x _ =>
      CircuitType.reads_prod.mpr ⟨htrue, CircuitType.reads_fvar.mpr rfl⟩

omit [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- A batch's last entry is an always-kept evaluation. -/
private theorem getLast_batch (sg : List (Bool × F)) (p f : F) (ev : List F) :
    ∀ x ∈ (sg ++ (true, p) :: (true, f) :: ev.map (true, ·)).getLast?, x.1 = true := by
  intro x hx
  rw [List.getLast?_append, List.getLast?_cons_cons, List.getLast?_cons, Option.some_or,
    List.getLast?_map, Option.mem_def, Option.some.injEq] at hx
  subst hx
  cases ev.getLast? <;> simp

omit [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- Four bits read as the four conditions, so `all` of them reads as their conjunction. -/
private theorem all_four {α : Type} (v : α → F) (b₁ b₂ b₃ b₄ : α) (p₁ p₂ p₃ p₄ : Prop)
    [Decidable p₁] [Decidable p₂] [Decidable p₃] [Decidable p₄]
    (h₁ : v b₁ = if p₁ then 1 else 0) (h₂ : v b₂ = if p₂ then 1 else 0)
    (h₃ : v b₃ = if p₃ then 1 else 0) (h₄ : v b₄ = if p₄ then 1 else 0) :
    (∀ b ∈ [b₁, b₂, b₃, b₄], v b = 0 ∨ v b = 1) ∧
    ((if ∀ b ∈ [b₁, b₂, b₃, b₄], v b = 1 then (1 : F) else 0)
      = if p₁ ∧ p₂ ∧ p₃ ∧ p₄ then 1 else 0) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, h₁, h₂, h₃,
    h₄]
  by_cases q₁ : p₁ <;> by_cases q₂ : p₂ <;> by_cases q₃ : p₃ <;> by_cases q₄ : p₄ <;> simp [*]

/-! ## Soundness -/

open Kimchi.Protocol.Linearization Bulletproof Poseidon.FqSponge Classical in
/-- The reading of `finalize_other_proof`'s outputs (`finalizeOtherProofCore_spec`): with
`ζ, α, β, γ` the expanded challenges, `permV` the permutation claim's inner value, `dv` the
challenge digest, `ω` of order dividing `n`, the mask `ms`, the previous challenges `cvs`, and
the fr-sponge state `s = absorb(init, frTranscript d dv ft(ζω) pub e)` with
`(x₁, s₁) = squeeze s`, `x₂ = squeeze(s₁)₁`: there are `ξ₀ < 2¹²⁸` the `ξ` claim,
`ξ' + 2¹²⁸·h₁ = x₁` the recomputed low half (below `2¹²⁸` where constrained),
`r' + 2¹²⁸·h₂ = x₂` with `r' < 2¹²⁸`, and `ĉᵢ < 2¹²⁸` the challenge claims, such that with
`ξ = endoExpand λ ξ₀`, `r = endoExpand λ r'`, `ft₀ = ftEval0 n zkRows ω shifts endo mds α β γ ζ
pub(ζ) e` and the read batch `rows` (the kept `(b_j(ζ), b_j(ζω))` for `m_j = 1`, then
`(pub(ζ), pub(ζω))`, `(ft₀, ft(ζω))`, the evaluation rows) the bits read
`xiCorrect = [ξ' = ξ₀]`, `cipCorrect = [unshift(cip claim) = combinedInnerProduct ξ r rows]`,
`bCorrect = [unshift(b claim) = combinedB (endoExpand λ ĉ) r (ζ, ζω)]`,
`plonkOk = [unshift(permV) = permScalar β γ α (zkpmEval n zkRows ω ζ) e]`, `finalized` their
conjunction, and the expanded challenges read `endoExpand λ ĉᵢ`. -/
def FopReads (P : FopParams F) (xiConstrainLowBits : Bool) (n : ℕ) (ω dv : F) (ms : List Bool)
    (cvs : List (List F)) (u : UnfinalizedProof F) (w : ProofWitness F) (ζ α β γ permV : F)
    (unshiftV : F → F) (V : Valuation F) (o : FopOutput F) : Prop :=
      let e := w.evals.map (·.val V)
    let s := Poseidon.absorb P.sponge Poseidon.init
      (frTranscript (u.spongeDigestBeforeEvaluations.val V) dv (w.ftEval1.val V)
        (w.pub.map fun x => #v[x.val V]) (w.evals.map fun x => #v[x.val V]))
    let (x₁, s₁) := Poseidon.squeeze P.sponge s
    let x₂ := (Poseidon.squeeze P.sponge s₁).1
    let ft₀ := ftEval0 n P.zkRows ω P.shifts P.endo P.mds α β
      γ ζ (w.pub.zeta.val V) (oneChunkEvals e)
    ∃ (ξ₀ r' h₁ h₂ : ℕ) (ξ' : F) (ĉ : List ℕ),
      ξ₀ < 2 ^ 128 ∧ u.xi.val.val V = ξ₀ ∧ h₁ < 2 ^ 128 ∧ h₂ < 2 ^ 128 ∧ r' < 2 ^ 128 ∧
      (xiConstrainLowBits = true → ∃ m : ℕ, m < 2 ^ 128 ∧ ξ' = m) ∧
      x₁ = ξ' + 2 ^ 128 * h₁ ∧ x₂ = r' + 2 ^ 128 * h₂ ∧
      List.Forall₂ (fun (ch : SizedF 128 (FVar F)) (k : ℕ) => k < 2 ^ 128 ∧ ch.val.val V = k)
        u.bulletproofChallenges ĉ ∧
      let ξ := endoExpand P.endoLam ξ₀
      let r := endoExpand P.endoLam r'
      let rows := sgRows ms (cvs.map fun cv => bPoly (fun i : Fin cv.length => cv.get i) ζ)
          (cvs.map fun cv => bPoly (fun i : Fin cv.length => cv.get i) (ζ * ω))
        ++ ⟨w.pub.zeta.val V, w.pub.zetaOmega.val V⟩ :: ⟨ft₀, w.ftEval1.val V⟩ :: evalRows e
      let cipOk := unshiftV (u.combinedInnerProduct.val V) = Bulletproof.combinedInnerProduct ξ r
        (fun (i : Fin rows.length) (j : Fin evalPts) => ((rows.get i).toVector)[j])
      let cs := ĉ.map (endoExpand P.endoLam)
      let bOk := unshiftV (u.b.val V) = combinedB (fun i : Fin cs.length => cs.get i) r ![ζ, ζ * ω]
      let permOk := unshiftV permV
        = permScalar β γ α (zkpmEval n P.zkRows ω ζ)
            (oneChunkEvals e)
      (↑o.xiCorrect : CVar F).val V = (if ξ' = (ξ₀ : F) then 1 else 0) ∧
      (↑o.cipCorrect : CVar F).val V = (if cipOk then 1 else 0) ∧
      (↑o.bCorrect : CVar F).val V = (if bOk then 1 else 0) ∧
      (↑o.plonkOk : CVar F).val V = (if permOk then 1 else 0) ∧
      (↑o.finalized : CVar F).val V
        = (if ξ' = (ξ₀ : F) ∧ bOk ∧ cipOk ∧ permOk then 1 else 0) ∧
      List.Forall₂ (CircuitType.Reads V) o.expandedChallenges
        (ĉ.map (endoExpand P.endoLam))

set_option maxHeartbeats 4000000 in
open Kimchi.Protocol.Linearization Bulletproof Poseidon.FqSponge Classical in
/-- Under any valuation satisfying the emitted constraints, with `ω` the generator's reading
(non-zero by its `inv` row, and then of order dividing `n`), the mask reading as `m_j`, the
previous challenges as `c_j`, the evaluations as `e`, `ζ, α, β, γ` the expanded challenges
and the fr-sponge state `s = absorb(init, frTranscript d digest ft(ζω) pub e)` with
`(x₁, s₁) = squeeze s` and `x₂ = squeeze(s₁)₁`:

* `ξ̂ < 2¹²⁸` is the `ξ` claim, `ξ' + 2¹²⁸·h₁ = x₁` the recomputed low half (below `2¹²⁸` where
  constrained), `r' + 2¹²⁸·h₂ = x₂` with `r' < 2¹²⁸`, and `ĉᵢ < 2¹²⁸` the challenge claims;
* `ξ = endoExpand λ ξ̂`, `r = endoExpand λ r'`, `ft₀ = ftEval0 n zkRows ω shifts endo mds α β γ ζ
  pub(ζ) e`, and the read batch `rows` is the kept `(b_j(ζ), b_j(ζω))` for `m_j = 1`, then
  `(pub(ζ), pub(ζω))`, `(ft₀, ft(ζω))`, and the evaluation rows;

the check bits read as

* `xiCorrect = [ξ' = ξ̂]`,
* `cipCorrect = [unshift(cip claim) = combinedInnerProduct ξ r rows]`,
* `bCorrect = [unshift(b claim) = combinedB (endoExpand λ ĉ) r (ζ, ζω)]`,
* `plonkOk = [unshift(perm claim) = permScalar β γ α (zkpmEval n zkRows ω ζ) e]`,
* `finalized` as their conjunction,

and the expanded challenges read as `endoExpand λ ĉᵢ`. -/
theorem finalizeOtherProofCore_spec {V : Valuation F} (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hinj : ∀ a b : ℕ, a < 2 ^ 128 → b < 2 ^ 128 → (a : F) = b → a = b)
    (P : FopParams F) (hsize : P.sponge.roundConstants.size = Poseidon.fullRounds)
    (h3zk : 3 ≤ P.zkRows) (n : ℕ) (hzk : P.zkRows ≤ n)
    (ops : FopShiftOps F (Builder V (KimchiConstraint F))) (unshiftV : F → F)
    (hun : ∀ x, (ops.unshift x).val V = unshiftV (x.val V))
    (hcmp : ∀ a b, ⦃⌜True⌝⦄ ops.shiftedEqual a b
      ⦃⇓ r _ => ⌜(↑r : CVar F).val V = if unshiftV (a.val V) = b.val V then 1 else 0⌝⦄)
    (xiConstrainLowBits : Bool) (digest : CircuitM F (Builder V (KimchiConstraint F)) (FVar F))
    (dv : F) (hd : ⦃⌜True⌝⦄ digest ⦃⇓ d _ => ⌜d.val V = dv⌝⦄)
    (gen : FVar F) (hω : gen.val V ≠ 0 → gen.val V ^ n = 1) (pow2Log2 : ℕ)
    (vanishing : FVar F → CircuitM F (Builder V (KimchiConstraint F)) (FVar F))
    (hvan : gen.val V ≠ 0 → ∀ z, ⦃⌜True⌝⦄ vanishing z ⦃⇓ v _ => ⌜v.val V = z.val V ^ n - 1⌝⦄)
    (mask : List (BoolVar F)) (ms : List Bool) (hm : List.Forall₂ (CircuitType.Reads V) mask ms)
    (u : UnfinalizedProof F) (w : ProofWitness F) (prev : List (List (FVar F)))
    (cvs : List (List F)) (hprev : List.Forall₂ (List.Forall₂ (CircuitType.Reads V)) prev cvs)
    (zeta alpha beta gamma perm : FVar F)
    (hft : ∀ (ulb : Bool → Int → CircuitM F (Builder V (KimchiConstraint F)) (FVar F))
      (inp : Inputs F) (ext : PermInputs F) (α ζ : F),
      (∀ k ≤ 70, (inp.alphaPows k).val V = α ^ k) → ext.zeta.val V = ζ →
      ext.zkPoly.val V = zkpmEval n P.zkRows (gen.val V) ζ →
      ext.zetaToNMinus1.val V = ζ ^ n - 1 →
      ext.omegaZk.val V = gen.val V ^ (n - P.zkRows) →
      ⦃⌜True⌝⦄ ftEval0Circuit (c := Builder V (KimchiConstraint F)) P.endo P.mds P.toks
        (fun _ => false) ulb inp ext
      ⦃⇓ a _ => ⌜a.val V = ftEval0 n P.zkRows (gen.val V) ext.shifts P.endo P.mds α
        (inp.beta.val V) (inp.gamma.val V) ζ (ext.pubEval.val V)
        (inp.evals.map (·.val V))⌝⦄) :
    ⦃⌜True⌝⦄ finalizeOtherProofCore (c := Builder V (KimchiConstraint F)) P ops
      xiConstrainLowBits digest gen pow2Log2 vanishing mask u w prev zeta alpha beta gamma perm
    ⦃⇓ o _ => ⌜gen.val V ≠ 0 ∧ FopReads P xiConstrainLowBits n (gen.val V) dv ms cvs u w
      (zeta.val V) (alpha.val V) (beta.val V) (gamma.val V) (perm.val V) unshiftV V o⌝⦄ := by
  simp only [finalizeOtherProofCore]
  have hsg := fun pt => challengePolyEvals_spec (V := V) (c := KimchiConstraint F) pt prev cvs hprev
  have hsq := squeezeXiR_spec (V := V) h2 h3 P.sponge hsize u.spongeDigestBeforeEvaluations
    digest dv hd w.ftEval1 w.pub w.evals (.const P.endoLam) xiConstrainLowBits
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
  mvcgen [hsg, hsq, htf, pow2PowSquare_spec, precomputeAlphaPowers_spec, hop, zkPolynomial_spec,
    hvan', hft', hcip, hcc, hbc, hps, hcmp, hall]
  -- the `ft_eval0` premises and the characteristic bound of `all`, in whatever order they come
  all_goals try (first
    | exact ‹_ ∧ ∀ k ≤ 70, _›.2
    | rfl
    | (rename_i _ _ hom _ _ _ _ _ hz1
       exact hz1 () hom.1)
    | (rename_i om _ hom zkp _ hzkp _ _ _
       rw [hzkp]
       obtain ⟨hne, ho1, ho2, ho3⟩ := hom
       rw [ho1, ho2, ho3]
       exact zkPolynomial_eq_zkpmEval n P.zkRows _ _ (hω hne) hzk (by omega))
    | (rename_i om _ hom _ _ _ _ _ _
       obtain ⟨hne, -, -, ho3⟩ := hom
       rw [ho3]
       exact inv_pow_eq_pow_sub n P.zkRows _ (hω hne) hzk)
    | (intro j k hj hk hjk
       exact hinj j k (by simp at hj; omega) (by simp at hk; omega) hjk))
  rename_i _ zetaw _ hzw sgw _ hsgw sgz _ hsgz xr _ hsq' xiC _ hxiC xi _ hxi rr _ hr _ _ _ _ _ _
    pows _ hpows om _ hom zkp _ hzkp z1 _ hz1 ft0 _ hft0 cipA _ cipC _ hcipC expd _ hexp bC _ hbC
    permA _ _ _ _ plonkC _ hplonk fin _ hfin hcipA hpermA
  have hc : (CVar.const P.endoLam : CVar F).val V = P.endoLam := rfl
  rw [hc] at hxi hr hexp
  rw [mul_comm] at hzw
  obtain ⟨h₁, h₂, hh1, hh2, hx1, hx2, hlo, ⟨r'n, hr'n, hrval⟩⟩ := hsq'
  obtain ⟨ξ₀, hξ₀, hxival, hxi'⟩ := hxi
  obtain ⟨m, hm', hrval', hr'⟩ := hr
  have hmr : m = r'n := hinj m r'n hm' hr'n (by rw [← hrval', hrval])
  subst hmr
  obtain ⟨ns, hns, hexpd⟩ := hexp
  -- the read batch
  have hlen : (cvs.map fun cv => bPoly (fun i : Fin cv.length => cv.get i) (zeta.val V)).length
      = (cvs.map fun cv =>
          bPoly (fun i : Fin cv.length => cv.get i) (zeta.val V * gen.val V)).length := by
    simp
  rw [hzw] at hsgw
  have hcipv := hcipA ⟨_, _, sgRows ms
      (cvs.map fun cv => bPoly (fun i : Fin cv.length => cv.get i) (zeta.val V))
      (cvs.map fun cv => bPoly (fun i : Fin cv.length => cv.get i) (zeta.val V * gen.val V))
      ++ ⟨w.pub.zeta.val V, w.pub.zetaOmega.val V⟩
      :: ⟨ft0.val V, w.ftEval1.val V⟩ :: evalRows (w.evals.map (·.val V))⟩
    (forall₂_buildEvalList hm hsgz _ _ _) (forall₂_buildEvalList hm hsgw _ _ _)
    (getLast_batch _ _ _ _) (getLast_batch _ _ _ _)
    (by rw [keptEvals_batch, keptEvals_zip_left _ _ _ hlen, map_evalFields_zeta]; simp)
    (by rw [keptEvals_batch, keptEvals_zip_right _ _ _ hlen, map_evalFields_zetaOmega]; simp)
  dsimp only at hcipv
  rw [hrval'] at hx2
  -- `b`
  have hbv := hbC _ hexpd
  -- the permutation scalar
  have hpv := hpermA ⟨oneChunkEvals (w.evals.map (·.val V)), alpha.val V,
      zkpmEval n P.zkRows (gen.val V) (zeta.val V)⟩
    (fun i => by simp [linEvals, oneChunkEvals, ProofEvaluations.map, PointEvaluations.map,
      Kimchi.sigmaCol])
    (fun i => by simp [linEvals, oneChunkEvals, ProofEvaluations.map, PointEvaluations.map])
    (by simp [linEvals, oneChunkEvals, ProofEvaluations.map, PointEvaluations.map])
    (by
      rw [hzkp]
      obtain ⟨hne, ho1, ho2, ho3⟩ := hom
      rw [ho1, ho2, ho3]
      exact zkPolynomial_eq_zkpmEval n P.zkRows _ _ (hω hne) hzk (by omega))
    (hpows.2 21 (by omega))
  -- the conjunction
  rw [map_linEvals] at hft0
  rw [hxival] at hxiC
  rw [hun, hcipv, hxi', hr', hft0] at hcipC
  rw [hun, hr', hzw] at hbv
  rw [hpv] at hplonk
  obtain ⟨hbool, hall4⟩ := all_four (fun b : BoolVar F => (↑b : CVar F).val V) xiC bC cipC plonkC
    _ _ _ _ hxiC hbv hcipC hplonk
  refine ⟨hom.1, ?_⟩
  unfold FopReads
  rw [hfin hbool, hall4]
  refine ⟨ξ₀, m, h₁, h₂, xr.1.val.val V, ns, hξ₀, hxival, hh1, hh2, hm', hlo, hx1, hx2, ?_,
    hxiC, hcipC, hbv, hplonk, ?_, hexpd⟩
  · exact List.forall₂_map_left_iff.mp hns
  · dsimp only

/-! ## The two sides -/

omit [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- A mask-select over readings: with the bits reading as `f` over the domains, the sum of
bit-times-entry is the sum over the domains. -/
private theorem zip_map_sum {V : Valuation F} :
    ∀ (bits : List (BoolVar F)) (ds : List (KnownDomain F)) (f : KnownDomain F → F)
      (g : KnownDomain F → FVar F),
      bits.map (fun b : BoolVar F => (↑b : CVar F).val V) = ds.map f →
      ((bits.zip (ds.map g)).map fun e => (↑e.1 : CVar F).val V * e.2.val V).sum
        = (ds.map fun d => f d * (g d).val V).sum
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => nomatch h
  | _ :: _, [], _, _, h => nomatch h
  | b :: bits, d :: ds, f, g, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.map_cons, List.zip_cons_cons, List.sum_cons, h.1, zip_map_sum bits ds f g h.2]

omit [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- The same over the domains' `log2` entries. -/
private theorem zip_map_sum_log2 {V : Valuation F} (ζ : F) :
    ∀ (bits : List (BoolVar F)) (ds : List (KnownDomain F)) (f : KnownDomain F → F),
      bits.map (fun b : BoolVar F => (↑b : CVar F).val V) = ds.map f →
      ((bits.zip (ds.map (·.log2))).map fun e => (↑e.1 : CVar F).val V * ζ ^ (2 ^ e.2)).sum
        = (ds.map fun d => f d * ζ ^ (2 ^ d.log2)).sum
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | b :: bits, d :: ds, f, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.map_cons, List.zip_cons_cons, List.sum_cons, h.1,
      zip_map_sum_log2 ζ bits ds f h.2]

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

omit [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c] in
/-- Every entry is at most the running maximum. -/
private theorem le_foldr_max : ∀ (l : List ℕ) (a : ℕ), a ∈ l → a ≤ l.foldr max 0
  | [], _, h => nomatch h
  | x :: l, a, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_max_left _ _
    · exact le_trans (le_foldr_max l a h') (le_max_right _ _)

omit [ToNat F] [KimchiSystem F c] in
/-- The step side's comparison reads as the decoded claim against the scalar. -/
private theorem stepShiftOps_cmp [ConstraintHolds F c] [LawfulBasicSystem F c] {V : Valuation F}
    (h2 : (2 : F) ≠ 0) (a b : FVar F) :
    ⦃⌜True⌝⦄ (stepShiftOps (F := F) (c := Builder V c)).shiftedEqual a b
    ⦃⇓ r _ => ⌜(↑r : CVar F).val V
      = if Type1.fromShifted 255 ⟨a.val V⟩ = b.val V then 1 else 0⌝⦄ := by
  simp only [stepShiftOps]
  mvcgen
  intro h
  rw [h, Type1.val_ofFieldCircuit]
  by_cases hab : Type1.fromShifted 255 ⟨a.val V⟩ = b.val V
  · rw [if_pos hab, if_pos]
    rw [← hab]
    exact (Pasta.Shifted.shiftType1_unshiftType1 h2 255 (a.val V)).symm
  · rw [if_neg hab, if_neg]
    intro h'
    apply hab
    rw [h']
    exact Pasta.Shifted.unshiftType1_shiftType1 h2 255 (b.val V)

omit [ToNat F] [KimchiSystem F c] in
/-- The wrap side's comparison reads as the decoded claim against the scalar. -/
private theorem wrapShiftOps_cmp [ConstraintHolds F c] [LawfulBasicSystem F c] {V : Valuation F}
    (a b : FVar F) :
    ⦃⌜True⌝⦄ (wrapShiftOps (F := F) (c := Builder V c)).shiftedEqual a b
    ⦃⇓ r _ => ⌜(↑r : CVar F).val V
      = if Type2.fromShifted 255 ⟨a.val V⟩ = b.val V then 1 else 0⌝⦄ := by
  simp only [wrapShiftOps]
  mvcgen
  intro h
  rw [h, Type2.val_fromShiftedCircuit]

set_option maxHeartbeats 1000000 in
open Kimchi.Protocol.Linearization Poseidon.FqSponge in
/-- The step side: under any valuation satisfying the emitted constraints, the runtime
`domain_log2` reads as one of the known domains' — `d₀`, of size `n = 2^log2` and generator
`ω` — and with `â, ẑ < 2¹²⁸` the `α, ζ` claims, the outputs read as `FopReads` at `ζ = endoExpand
λ ẑ`, `α = endoExpand λ â`, `β, γ` the raw claims, the digest of the mask-kept previous
challenges, `ξ` constrained below `2¹²⁸`, and the Type1 decode of the shifted claims. -/
theorem finalizeOtherProofStep_spec {V : Valuation F} (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hinj : ∀ a b : ℕ, a < 2 ^ 128 → b < 2 ^ 128 → (a : F) = b → a = b)
    (P : FopParams F) (hsize : P.sponge.roundConstants.size = Poseidon.fullRounds)
    (h3zk : 3 ≤ P.zkRows) (domains : List (KnownDomain F))
    (hnodup : (domains.map fun d => (d.log2 : F)).Nodup)
    (hdom : ∀ d ∈ domains, P.zkRows ≤ 2 ^ d.log2 ∧ d.generator ^ 2 ^ d.log2 = 1)
    (u : UnfinalizedProof F) (w : ProofWitness F) (mask : List (BoolVar F)) (ms : List Bool)
    (hm : List.Forall₂ (CircuitType.Reads V) mask ms) (prev : List (List (FVar F)))
    (cvs : List (List F)) (hprev : List.Forall₂ (List.Forall₂ (CircuitType.Reads V)) prev cvs)
    (hprevlen : prev.flatten.length < 2 ^ 128) (domainLog2Var : FVar F)
    (hft : ∀ (n : ℕ) (ω : F)
      (ulb : Bool → Int → CircuitM F (Builder V (KimchiConstraint F)) (FVar F))
      (inp : Inputs F) (ext : PermInputs F) (α ζ : F),
      (∀ k ≤ 70, (inp.alphaPows k).val V = α ^ k) → ext.zeta.val V = ζ →
      ext.zkPoly.val V = zkpmEval n P.zkRows ω ζ → ext.zetaToNMinus1.val V = ζ ^ n - 1 →
      ext.omegaZk.val V = ω ^ (n - P.zkRows) →
      ⦃⌜True⌝⦄ ftEval0Circuit (c := Builder V (KimchiConstraint F)) P.endo P.mds P.toks
        (fun _ => false) ulb inp ext
      ⦃⇓ a _ => ⌜a.val V = ftEval0 n P.zkRows ω ext.shifts P.endo P.mds α (inp.beta.val V)
        (inp.gamma.val V) ζ (ext.pubEval.val V) (inp.evals.map (·.val V))⌝⦄) :
    ⦃⌜True⌝⦄ finalizeOtherProofStep (c := Builder V (KimchiConstraint F)) P domains u w mask
      prev domainLog2Var
    ⦃⇓ o _ => ⌜∃ d₀, d₀ ∈ domains ∧ domainLog2Var.val V = (d₀.log2 : F) ∧
      ∃ a₀ z₀ : ℕ, a₀ < 2 ^ 128 ∧ z₀ < 2 ^ 128 ∧ u.alpha.val.val V = a₀ ∧ u.zeta.val.val V = z₀ ∧
      FopReads P true (2 ^ d₀.log2) d₀.generator
        (Poseidon.squeeze P.sponge (Poseidon.absorb P.sponge Poseidon.init
          (List.zipWith (fun m cs => if m then cs.map (·.val V) else []) ms prev).flatten)).1
        ms cvs u w (endoExpand P.endoLam z₀) (endoExpand P.endoLam a₀) (u.beta.val.val V)
        (u.gamma.val.val V) (u.perm.val V) (fun x => Type1.fromShifted 255 ⟨x⟩) V o⌝⦄ := by
  simp only [finalizeOtherProofStep]
  have htf := EndoScalar.toField_spec (V := V) h2 h3
  have hwh := knownDomainWhiches_spec (V := V) (c := KimchiConstraint F) domainLog2Var
    (domains.map (·.log2))
  have hmask := fun bits xs => Pseudo.mask_spec (V := V) (c := KimchiConstraint F) bits xs
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
        mask u w prev zeta alpha u.beta.val u.gamma.val u.perm)
      (fun n : ℕ => P.zkRows ≤ n ∧ (gen.val V ≠ 0 → gen.val V ^ n = 1) ∧
        (gen.val V ≠ 0 → ∀ z, ⦃⌜True⌝⦄ knownDomainVanishingPolynomial
          (c := Builder V (KimchiConstraint F)) whiches (domains.map (·.log2))
          ((domains.map (·.log2)).foldr max 0) z ⦃⇓ v _ => ⌜v.val V = z.val V ^ n - 1⌝⦄))
      (fun n o => gen.val V ≠ 0 ∧ FopReads P true n (gen.val V) _ ms cvs u w (zeta.val V)
        (alpha.val V) (u.beta.val.val V) (u.gamma.val.val V) (u.perm.val V)
        (fun x => Type1.fromShifted 255 ⟨x⟩) V o)
      (fun n hn => finalizeOtherProofCore_spec h2 h3 hinj P hsize h3zk n hn.1 stepShiftOps
        (fun x => Type1.fromShifted 255 ⟨x⟩) (fun x => Type1.val_fromShiftedCircuit 255 ⟨x⟩ V)
        (stepShiftOps_cmp h2) true _ _ hd gen hn.2.1 _ _ hn.2.2 mask ms hm u w prev cvs hprev
        zeta alpha _ _ _ (fun ulb inp ext α ζ => hft n (gen.val V) ulb inp ext α ζ))
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
    rw [hgen, zip_map_sum whiches domains _ _ hbits]
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
        (domains.map (·.log2)) ((domains.map (·.log2)).foldr max 0) z (le_foldr_max _))
        fun v hv => ?_
      rw [hv, zip_map_sum_log2 (z.val V) whiches domains _ hbits,
        onehot_sum _ _ domains hnodup d₀ hd₀ hL]
    obtain ⟨-, hreads⟩ := hcore' (2 ^ d₀.log2) hzk₀ (fun _ => by rw [hgen₀]; exact hω₀)
      (fun _ => hvan₀)
    refine ⟨d₀, hd₀, hL, a₀, z₀, ha₀, hz₀, haval, hzval, ?_⟩
    rw [hgen₀, hz', ha'] at hreads
    exact hreads
  · exfalso
    push Not at hmatch
    have hgen0 : gen.val V = 0 := by
      rw [hgenv]
      exact onehot_sum_none _ _ domains hmatch
    obtain ⟨hne, -⟩ := hcore' P.zkRows le_rfl (fun h => absurd hgen0 h) (fun h => absurd hgen0 h)
    exact hne hgen0

set_option maxHeartbeats 1000000 in
open Kimchi.Protocol.Linearization Poseidon.FqSponge in
/-- The wrap side: under any valuation satisfying the emitted constraints, with the constant
generator `ω` of order dividing `n` and the caller's vanishing polynomial reading `ζⁿ − 1`, and
`â, ẑ < 2¹²⁸` the `α, ζ` claims, the outputs read as `FopReads` at `ζ = endoExpand λ ẑ`,
`α = endoExpand λ â`, `β, γ` the raw claims, the digest of all previous challenges, `ξ`
unconstrained, and the Type2 decode of the shifted claims. -/
theorem finalizeOtherProofWrap_spec {V : Valuation F} (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hinj : ∀ a b : ℕ, a < 2 ^ 128 → b < 2 ^ 128 → (a : F) = b → a = b)
    (P : FopParams F) (hsize : P.sponge.roundConstants.size = Poseidon.fullRounds)
    (h3zk : 3 ≤ P.zkRows) (gen : F) (n : ℕ) (hzk : P.zkRows ≤ n) (hω : gen ^ n = 1)
    (domainLog2 : ℕ) (vanishing : FVar F → CircuitM F (Builder V (KimchiConstraint F)) (FVar F))
    (hvan : ∀ z, ⦃⌜True⌝⦄ vanishing z ⦃⇓ v _ => ⌜v.val V = z.val V ^ n - 1⌝⦄)
    (u : UnfinalizedProof F) (w : ProofWitness F) (prev : List (List (FVar F)))
    (cvs : List (List F)) (hprev : List.Forall₂ (List.Forall₂ (CircuitType.Reads V)) prev cvs)
    (hft : ∀ (ulb : Bool → Int → CircuitM F (Builder V (KimchiConstraint F)) (FVar F))
      (inp : Inputs F) (ext : PermInputs F) (α ζ : F),
      (∀ k ≤ 70, (inp.alphaPows k).val V = α ^ k) → ext.zeta.val V = ζ →
      ext.zkPoly.val V = zkpmEval n P.zkRows gen ζ → ext.zetaToNMinus1.val V = ζ ^ n - 1 →
      ext.omegaZk.val V = gen ^ (n - P.zkRows) →
      ⦃⌜True⌝⦄ ftEval0Circuit (c := Builder V (KimchiConstraint F)) P.endo P.mds P.toks
        (fun _ => false) ulb inp ext
      ⦃⇓ a _ => ⌜a.val V = ftEval0 n P.zkRows gen ext.shifts P.endo P.mds α (inp.beta.val V)
        (inp.gamma.val V) ζ (ext.pubEval.val V) (inp.evals.map (·.val V))⌝⦄) :
    ⦃⌜True⌝⦄ finalizeOtherProofWrap (c := Builder V (KimchiConstraint F)) P gen domainLog2
      vanishing u w prev
    ⦃⇓ o _ => ⌜∃ a₀ z₀ : ℕ, a₀ < 2 ^ 128 ∧ z₀ < 2 ^ 128 ∧ u.alpha.val.val V = a₀ ∧
      u.zeta.val.val V = z₀ ∧
      FopReads P false n gen
        (Poseidon.squeeze P.sponge (Poseidon.absorb P.sponge Poseidon.init
          (prev.flatten.map (·.val V)))).1
        (prev.map fun _ => true) cvs u w (endoExpand P.endoLam z₀) (endoExpand P.endoLam a₀)
        (u.beta.val.val V) (u.gamma.val.val V) (u.perm.val V)
        (fun x => Type2.fromShifted 255 ⟨x⟩) V o⌝⦄ := by
  simp only [finalizeOtherProofWrap]
  have htf := EndoScalar.toField_spec (V := V) h2 h3
  have hd := challengeDigest_spec (V := V) P.sponge hsize prev
  have hm : List.Forall₂ (CircuitType.Reads V) (prev.map fun _ => (true_ : BoolVar F))
      (prev.map fun _ => true) :=
    List.forall₂_map_right_iff.mpr (List.forall₂_map_left_iff.mpr
      (List.forall₂_same.mpr fun _ _ => CircuitType.reads_boolVar.mpr (by simp [true_, bit])))
  have hcore := fun (zeta alpha beta gamma perm : FVar F) =>
    finalizeOtherProofCore_spec h2 h3 hinj P hsize h3zk n hzk wrapShiftOps
      (fun x => Type2.fromShifted 255 ⟨x⟩) (fun x => Type2.val_fromShiftedCircuit 255 ⟨x⟩ V)
      wrapShiftOps_cmp false _ _ hd (.const gen) (fun _ => hω) domainLog2 vanishing
      (fun _ => hvan) _ _ hm u w prev cvs hprev zeta alpha beta gamma perm hft
  mvcgen [htf, hcore]
  rename_i _ zeta _ hz gamma _ hγ beta _ hβ alpha _ ha perm _ hperm _ _ _ _ _ _ _ _
  intro _ hreads
  obtain ⟨z₀, hz₀, hzval, hz'⟩ := hz
  obtain ⟨a₀, ha₀, haval, ha'⟩ := ha
  have hc : (CVar.const P.endoLam : CVar F).val V = P.endoLam := rfl
  rw [hc] at hz' ha'
  refine ⟨a₀, z₀, ha₀, hz₀, haval, hzval, ?_⟩
  rw [hz', ha', hβ, hγ, hperm] at hreads
  exact hreads

end Pickles
