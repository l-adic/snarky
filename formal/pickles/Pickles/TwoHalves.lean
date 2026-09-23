import Pickles.Env
import Pickles.IncrementallyVerify
import Pickles.FinalizeOtherProof
import Pickles.Verify
import Kimchi.Columns
import Pickles.ListLemmas

/-!
# The two halves of one proof read as `kimchiVerify`

One kimchi proof `cp` of key `cvk` at public input `pub` is verified by two circuits over the
two fields of the cycle:

1. the **group half**, over the base field, in the circuit that receives the proof (for a
   step proof, the wrap circuit). It scales by the claimed `cip`, `b`, `ξ` and returns whether
   the opening's Schnorr equation holds at them;
2. the **scalar half**, over the scalar field, one circuit later (for a step proof, the next
   step circuit). It recomputes `cip`, `b`, `ξ`, the permutation scalar and the two `ζ` powers
   from the evaluations and returns whether the claims are honest.

This module composes them without running a circuit. From the two reads (`GroupHalf.Reads`,
`FopVerifyReads`) and the ties between the two circuits' cells (`HalvesTies`, `FopTies`), both
bits reading `1` is the wire's Schnorr equation at honest claims (`twoHalves_schnorr`); with
the deferred `SgOk` it is `kimchiVerify`'s acceptance at honest claims
(`twoHalves_kimchiVerify`).

## The arguments

* the **environment** `Env`: the SRS and the verifier key with their invariants;
* the **proof**: `cp` and `pub`, the wire objects `kimchiVerify` judges;
* the two **halves**, `GroupHalf` and `ScalarHalf`: each a valuation, a side (the
  curve-dependent decodes and constants) and the cells its circuit is given. A half holds
  inputs only; the bit its circuit produces is an argument of the read. The wire recomputes
  what the cells claim (`ClaimsHonest`), and the theorems force the cells to it.

The half modules discharge each read from its circuit, and `stepProof_kimchiVerify_vesta`,
`wrapProof_kimchiVerify_pallas` compose both circuits into the top-level theorems.

## The direction

The reads pin every 128-bit prechallenge to the wire's (`Low128.exact`) and the `U` base to
`uBase`, so the bits reading `1` force acceptance. The converse needs the `ξ` comparison to be
exact: `xiCorrect` compares the claim against the low half of a split of the fr-sponge's
squeeze, which is canonical only where the circuit range-checks that low half. Both circuits
do (`xiExact_of_constrained`), so both theorems are equivalences at either proof.

## Scope

`SgOk` is no circuit's output: pickles defers it to the next proof's batch opening, and here it
is a conjunct of `twoHalves_kimchiVerify`. The message digests are entries of `pub` like any
other, and the packing of statements across the cycle is `verify`'s.

## Implementation notes

The proof identifies the scalar half's inputs with the run's through the ties (`rows_eq`), and
never unfolds a sponge run: `runOracles` and `transcriptFrom` are projected to the raw
`fqRun`/`ipaRunAt` fields, since unfolding them recurses into the permutation.

The group read's opening clause assumes the three scalars the `ft` commitment scales by are the
run's (`IvpReads`). They are supplied here: the scalar half's `plonkOk` compares them with the
transcript's values, which the group read gives without the opening, and the ties
(`HalvesTies.perm`, `zetaM`, `zetaN`) carry them to the group half's cells.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open Kimchi.Protocol.Linearization Poseidon.FqSponge
open scoped Kimchi

/-! ## The group half -/

/-- The group half of a proof's verification, as one circuit runs it (for a step proof, the
wrap circuit): its valuation, its side and its statement's claim cells. Inputs only: the
success bit is an argument of `GroupHalf.Reads`, and the circuit's `IvpOutput` is existential
there, pinned to the claims by `verify`'s assertions. -/
structure GroupHalf (C : KimchiCurve) (sf : Type) (k : ℕ) where
  /-- The circuit's valuation (over the base field). -/
  V : Valuation C.BaseField
  /-- The shifted-scalar operations of the side. -/
  ops : IpaScalarOps C.BaseField (Builder V (KimchiConstraint C.BaseField)) sf
  /-- The side. -/
  side : IvpSide C V ops
  /-- The statement's claim cells: the deferred values, the round challenges, the digest. -/
  claims : UnfinalizedProof k (FVar C.BaseField) (BoolVar C.BaseField) sf

/-! ## The scalar half -/

/-- The scalar half's side: how a shifted claim cell reads (`FopShiftOps.Reading.read`), how
that reading unshifts, and the side's linearization token stream. The two functions are the
gadget's own (`stepShiftOps.reading`, `wrapShiftOps.reading`), kept apart because
`FopVerifyReads` takes them apart. -/
structure FopSide (C : KimchiCurve) (V : Valuation C.ScalarField) (sf : Type) where
  /-- The value a shifted claim cell reads as, still shifted. -/
  read : sf → C.ScalarField
  /-- The decode of a reading: the shift the side's claims carry. -/
  unshiftV : C.ScalarField → C.ScalarField
  /-- The linearization token stream of the side. -/
  toks : Array Linearization.PolishToken

/-- The scalar a shifted claim cell reads as: its value, unshifted. -/
def FopSide.decode {C : KimchiCurve} {V : Valuation C.ScalarField} {sf : Type}
    (S : FopSide C V sf) (x : sf) : C.ScalarField := S.unshiftV (S.read x)

/-- Unshifting a claim's reading is the half's decode of it: `FopVerifyReads`' split form, put
back together. -/
theorem FopSide.unshiftV_read {C : KimchiCurve} {V : Valuation C.ScalarField} {sf : Type}
    (S : FopSide C V sf) (x : sf) : S.unshiftV (S.read x) = S.decode x := rfl

/-- The scalar half of a proof's verification, as the next circuit runs it (for a step proof,
the following step circuit): its valuation, its side, and its cells — the deferred claims with
the fq digest, the evaluations, the predecessor mask and the previous challenges. Inputs only:
the circuit's output is an argument of the statements that read it. -/
structure ScalarHalf (C : KimchiCurve) (sf : Type) (k nc : ℕ) where
  /-- The circuit's valuation (over the scalar field). -/
  V : Valuation C.ScalarField
  /-- The side. -/
  side : FopSide C V sf
  /-- The deferred claim cells and the fq digest cell. -/
  claims : UnfinalizedProof k (FVar C.ScalarField) (BoolVar C.ScalarField) sf
  /-- The evaluation cells: `ft(ζω)`, the public chunks, the proof's evaluation chunks. -/
  evals : ChunkedEvals nc (FVar C.ScalarField)
  /-- The predecessor mask cells, one per slot: `1` for a real predecessor, `0` for a dummy
  pad slot. The wrap half fixes them all true (`ScalarHalf.wrap`). -/
  mask : Vector (BoolVar C.ScalarField) MaxProofsVerified
  /-- The previous-challenge cells: per slot, the `k` expanded round challenges of that
  predecessor's opening. -/
  prevChallenges : Vector (Vector (FVar C.ScalarField) k) MaxProofsVerified

/-- The mask as the valuation reads it: a cell counts as set when it holds `1`. -/
def ScalarHalf.maskVals {C : KimchiCurve} {sf : Type} {k nc : ℕ} (Sc : ScalarHalf C sf k nc) :
    List Bool :=
  Sc.mask.toList.map fun (b : BoolVar C.ScalarField) =>
    decide ((↑b : CVar C.ScalarField).val Sc.V = 1)

/-- The previous challenges as the valuation reads them. -/
def ScalarHalf.prevVals {C : KimchiCurve} {sf : Type} {k nc : ℕ} (Sc : ScalarHalf C sf k nc) :
    List (List C.ScalarField) :=
  Sc.prevChallenges.toList.map fun cs => cs.toList.map fun x => x.val Sc.V

/-- The scalar half's parameters, read off the environment and the side's tokens. -/
def FopParams.ofEnv {C : KimchiCurve} {nc : ℕ} (E : Env C nc)
    (toks : Array Linearization.PolishToken) :
    FopParams C.ScalarField :=
  { sponge := C.frSponge.params
    endoLam := C.lam
    endo := E.cvk.endo
    mds := mdsOfParams C.frSponge.params
    toks := toks
    shifts := fun i => E.cvk.shifts[i]
    srsLengthLog2 := E.σ.k
    zkRows := E.cvk.zkRows }

/-! ## The two halves' reads at their own cells -/

section AtCells

variable {C : KimchiCurve} {sf sf' : Type}

/-- The group half's read: `VerifyReads` at the half's side and claim cells, off the base
case. -/
def GroupHalf.Reads {nc : ℕ} (E : Env C nc) (cp : KimchiProof C nc E.σ.k)
    (pub : Array C.ScalarField)
    (G : GroupHalf C sf E.σ.k) (success : BoolVar C.BaseField) : Prop :=
  VerifyReads G.side E.σ E.cvk cp pub G.claims false success

/-- The `ξ` comparison is exact at the half: a `ξ` claim reading as the fr-sponge's `ξ`
prechallenge at the half's own cells makes `xiCorrect` read `1`. It needs the low half of the
`ξ` split range-checked: unchecked, the prover could witness a low half at or above `2¹²⁸`
whose split stays below the modulus, and `xiCorrect` would read `0` at an honest claim. -/
private def ScalarHalf.XiExact {nc : ℕ} (E : Env C nc) (cp : KimchiProof C nc E.σ.k)
    (Sc : ScalarHalf C sf' E.σ.k nc)
    (out : FopOutput C.ScalarField) : Prop :=
  let pre := frPrechallenges C.frSponge.params
    (frTranscript (Sc.claims.spongeDigestBeforeEvaluations.val Sc.V)
      (recDigest C (cp.olds.map (·.u))) (Sc.evals.ftEval1.val Sc.V)
      (Sc.evals.pub.map fun v => v.map (·.val Sc.V))
      (Sc.evals.evals.map fun v => v.map (·.val Sc.V)))
  ∀ ξ₀ : Prechallenge, Reads128 Sc.V Sc.claims.deferredValues.xi ξ₀ → ξ₀.val = pre.1 →
    (↑out.xiCorrect : CVar C.ScalarField).val Sc.V = 1

end AtCells

/-! ## The ties between the two halves -/

section Ties

variable {C : KimchiCurve} {sf sf' : Type}

/-- The two halves' claim cells carry one value across the field crossing: the shifted claims
decode alike on both sides, the prechallenge cells read one prechallenge, and the fq digest
crosses as `castDigest` (zero when it does not fit the scalar field: a completeness gap, not a
soundness one). The protocol enforces these through the public-input commitment binding the
statement into the proof; no circuit computes them, so they are hypotheses here. -/
structure HalvesTies {k nc : ℕ} (G : GroupHalf C sf k) (Sc : ScalarHalf C sf' k nc) : Prop where
  /-- `α`: the two cells read one prechallenge. -/
  alpha : ∃ a₀ : Prechallenge,
    Reads128 G.V G.claims.deferredValues.plonk.alpha a₀ ∧
    Reads128 Sc.V Sc.claims.deferredValues.plonk.alpha a₀
  /-- `ζ`, likewise. -/
  zeta : ∃ z₀ : Prechallenge,
    Reads128 G.V G.claims.deferredValues.plonk.zeta z₀ ∧
    Reads128 Sc.V Sc.claims.deferredValues.plonk.zeta z₀
  /-- `β`, likewise. -/
  beta : ∃ b₀ : Prechallenge,
    Reads128 G.V G.claims.deferredValues.plonk.beta b₀ ∧
    Reads128 Sc.V Sc.claims.deferredValues.plonk.beta b₀
  /-- `γ`, likewise. -/
  gamma : ∃ g₀ : Prechallenge,
    Reads128 G.V G.claims.deferredValues.plonk.gamma g₀ ∧
    Reads128 Sc.V Sc.claims.deferredValues.plonk.gamma g₀
  /-- `ξ`, likewise. -/
  xi : ∃ ξ₀ : Prechallenge,
    Reads128 G.V G.claims.deferredValues.xi ξ₀ ∧
    Reads128 Sc.V Sc.claims.deferredValues.xi ξ₀
  /-- The `cip` claim decodes to the same scalar on both sides. -/
  cip : Sc.side.decode Sc.claims.deferredValues.combinedInnerProduct
    = G.side.decode G.claims.deferredValues.combinedInnerProduct
  /-- The `b` claim, likewise. -/
  b : Sc.side.decode Sc.claims.deferredValues.b = G.side.decode G.claims.deferredValues.b
  /-- The permutation-scalar claim, likewise. -/
  perm : Sc.side.decode Sc.claims.deferredValues.plonk.perm
    = G.side.decode G.claims.deferredValues.plonk.perm
  /-- The `ζ^(2^k)` claim, likewise. -/
  zetaM : Sc.side.decode Sc.claims.deferredValues.plonk.zetaToSrsLength
    = G.side.decode G.claims.deferredValues.plonk.zetaToSrsLength
  /-- The `ζⁿ` claim, likewise. -/
  zetaN : Sc.side.decode Sc.claims.deferredValues.plonk.zetaToDomainSize
    = G.side.decode G.claims.deferredValues.plonk.zetaToDomainSize
  /-- The round challenges: the two cell lists read one prechallenge list. -/
  chals : ∃ ms : List Prechallenge,
    List.Forall₂ (Reads128 G.V) G.claims.deferredValues.bulletproofChallenges.toList ms ∧
    List.Forall₂ (Reads128 Sc.V) Sc.claims.deferredValues.bulletproofChallenges.toList ms
  /-- The fq digest: the scalar half's cell is the cast of the group half's. -/
  digest : Sc.claims.spongeDigestBeforeEvaluations.val Sc.V
    = castDigest C (G.claims.spongeDigestBeforeEvaluations.val G.V)

/-- The scalar half's evaluation, mask and previous-challenge cells are the proof's. -/
structure FopTies {nc : ℕ} (E : Env C nc) (cp : KimchiProof C nc E.σ.k) (pub : Array C.ScalarField)
    (Sc : ScalarHalf C sf' E.σ.k nc) : Prop where
  /-- The kept previous challenges are the old accumulators' challenges, in order. -/
  olds : (List.zipWith (fun m cv => if m then [cv] else []) Sc.maskVals
      Sc.prevVals).flatten
    = (cp.olds.map (·.u.toList)).toList
  /-- `ft(ζω)` is the proof's. -/
  ftEval1 : Sc.evals.ftEval1.val Sc.V = cp.ftEval1
  /-- The evaluation cells are the proof's evaluations, chunk by chunk. -/
  evals : Sc.evals.evals.map (fun v => v.map (·.val Sc.V)) = cp.evals
  /-- The public evaluation cells are the run's (`runPubEvals`), chunk by chunk. -/
  pubEvals : Sc.evals.pub.map (fun v => v.map (·.val Sc.V)) = runPubEvals C E.σ E.cvk cp pub

/-- With the low half of the `ξ` split range-checked, the scalar half's read makes the `ξ`
comparison exact (`XiExact`). -/
private theorem ScalarHalf.xiExact_of_constrained {nc : ℕ} (E : Env C nc)
    (hscalar : 2 ^ 128 < C.scalar)
    (cp : KimchiProof C nc E.σ.k) {G : GroupHalf C sf E.σ.k}
    {Sc : ScalarHalf C sf' E.σ.k nc} {out : FopOutput C.ScalarField}
    (hs : FopVerifyReads (p := C.scalar) (FopParams.ofEnv E Sc.side.toks)
      true E.cvk.n E.cvk.omega (recDigest C (cp.olds.map (·.u)))
      Sc.maskVals Sc.prevVals Sc.claims Sc.evals C.lam
      Sc.side.read Sc.side.unshiftV Sc.V out)
    (ht : HalvesTies G Sc) : Sc.XiExact E cp out := by
  have hinjS := castInj128_of_lt _ hscalar
  obtain ⟨a₀, -, hαSa⟩ := ht.alpha
  obtain ⟨z₀, -, hζSz⟩ := ht.zeta
  simp only [FopVerifyReads] at hs
  obtain ⟨a₀', z₀', hαS, hζS, hs⟩ := hs
  obtain rfl := Reads128.unique hinjS hαSa hαS
  obtain rfl := Reads128.unique hinjS hζSz hζS
  simp only [FopReadsWire, FopParams.ofEnv] at hs
  obtain ⟨ξ₀', -, -, hξS, -, -, -, hex, -, -⟩ := hs
  intro ξ₀ hξ hpre
  obtain rfl := Reads128.unique hinjS hξ hξS
  exact hex trivial hpre

/-- The claims are the wire's own values: `cip`, `b`, the permutation scalar and the two `ζ`
powers are the run's, and the `ξ` cell reads as the run's fr-sponge `ξ` prechallenge. What the
scalar half's `finalized` bit asserts, in wire terms. -/
private def ClaimsHonest {nc : ℕ} (E : Env C nc) (cp : KimchiProof C nc E.σ.k)
    (pub : Array C.ScalarField)
    (cipV bV permV zetaMV zetaNV : C.ScalarField) (V : Valuation C.ScalarField)
    (xi : SizedF 128 (FVar C.ScalarField)) : Prop :=
  let run := runInput C E.σ E.cvk cp pub
  let tr := transcriptFrom C (runOracles C E.σ E.cvk cp pub).warm run
  cipV = cipOf run ∧
  bV = combinedB (fun i => tr.2.1[i]) run.evalscale run.pointFn ∧
  permV = runPScalar C E.σ E.cvk cp pub ∧
  zetaMV = runZetaM C E.σ E.cvk cp pub ∧
  zetaNV = runZetaN C E.σ E.cvk cp pub ∧
  ∃ m : Prechallenge, Reads128 V xi m ∧
    m.val = (frPrechallenges C.frSponge.params (frTranscript (runOracles C E.σ E.cvk cp pub).digest
      (recDigest C (cp.olds.map (·.u))) cp.ftEval1 (runPubEvals C E.σ E.cvk cp pub) cp.evals)).1

/-- The claims of a scalar half, as `ClaimsHonest` reads them: the five shifted claims
through the side's decode, the `ξ` cell at the half's valuation. -/
def ScalarHalf.ClaimsHonest {nc : ℕ} (E : Env C nc) (cp : KimchiProof C nc E.σ.k)
    (pub : Array C.ScalarField)
    (Sc : ScalarHalf C sf' E.σ.k nc) : Prop :=
  let dv := Sc.claims.deferredValues
  Pickles.ClaimsHonest E cp pub (Sc.side.decode dv.combinedInnerProduct) (Sc.side.decode dv.b)
    (Sc.side.decode dv.plonk.perm) (Sc.side.decode dv.plonk.zetaToSrsLength)
    (Sc.side.decode dv.plonk.zetaToDomainSize) Sc.V dv.xi

/-- The deferred `sg`-correctness equation of the proof's opening at the wire's round
challenges (`verifyWith`'s second conjunct), which pickles checks one proof later. Stated over
the SRS and the key, not an `Env`. -/
def SgOk {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField) : Prop :=
  let run := runInput C σ cvk cp pub
  let tr := transcriptFrom C (runOracles C σ cvk cp pub).warm run
  run.proof.sg = msm C σ.g (bPolyCoefficients fun i => tr.2.1[i])

/-- The decidable mirror of `SgOk`: the deferred check as run out of circuit on a wire
proof. -/
def sgOk {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField) : Bool :=
  let run := runInput C σ cvk cp pub
  let tr := transcriptFrom C (runOracles C σ cvk cp pub).warm run
  decide (run.proof.sg = msm C σ.g (bPolyCoefficients fun i => tr.2.1[i]))

/-! ## The deferred obligation, carried

Pickles never checks `SgOk` on the proof itself. The proof's `(sg, round challenges)` becomes
an old accumulator of the next proof on the same curve, whose batch opens it; the circuit in
between, on the other curve, computes the challenges and passes them through its statement.
`carry` decides that handover on two proofs, and `accOk` the deferred equation on the
accumulator alone. -/

/-- Whether an old accumulator's commitment is the challenge polynomial of its round challenges
over the SRS: `SgOk` with the proof's opening and transcript replaced by what the next proof
carries. -/
def accOk (σ : SRS C.Point) (a : Accumulator C σ.k) : Bool :=
  decide (a.sg = msm C σ.g (bPolyCoefficients fun i => a.u[i]))

/-- Whether `cp'` carries `cp`'s deferred obligation as its old accumulator `i`: the
accumulator's commitment is `cp`'s opening's `sg`, its challenges the wire's round challenges
of `cp`. -/
def carry {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField)
    {nc' : ℕ} (cp' : KimchiProof C nc' σ.k) (i : Fin cp'.olds.size) : Bool :=
  let run := runInput C σ cvk cp pub
  let tr := transcriptFrom C (runOracles C σ cvk cp pub).warm run
  decide (cp'.olds[i].sg = run.proof.sg ∧ cp'.olds[i].u = tr.2.1)

/-! ### Reading the wire's batch through the scalar half's rows -/

/-- The challenge polynomial over a vector's list is the one over the vector. -/
private theorem bPoly_toList {F : Type} [Field F] {k : ℕ} (u : Vector F k) (x : F) :
    bPoly (fun i : Fin u.toList.length => u.toList.get i) x = bPoly u.get x := by
  unfold bPoly
  refine Fintype.prod_equiv (finCongr Vector.length_toList) _ _ fun i => ?_
  simp only [finCongr_apply, Fin.val_cast, List.get_eq_getElem, Vector.getElem_toList,
    Vector.length_toList]
  rfl

/-- The proof's combined evaluations are the linearization view of its evaluations recombined
at the same points. -/
private theorem linEvals_combine {C : KimchiCurve} {nc k : ℕ} (cp : KimchiProof C nc k)
    (zM zOM : C.ScalarField) :
    cp.linEvals zM zOM = linEvals (combineEvals zM zOM cp.evals) := by
  ext <;> simp [KimchiProof.linEvals, linEvals, combineEvals, combineColumn]

/-- The combined inner product over a row list is the one over a vector with the same rows. -/
private theorem cip_congr {F : Type} [Field F] (ξ r : F) {m : ℕ} (rows : List (PointEvaluations F))
    (v : Vector (Vector F evalPts) m) (h : rows.map PointEvaluations.toVector = v.toList) :
    Bulletproof.combinedInnerProduct ξ r
        (fun (i : Fin rows.length) (j : Fin evalPts) => ((rows.get i).toVector)[j])
      = Bulletproof.combinedInnerProduct ξ r (fun (i : Fin m) (j : Fin evalPts) => (v[i])[j]) := by
  have hlen : rows.length = m := by
    have := congrArg List.length h
    simpa using this
  unfold Bulletproof.combinedInnerProduct
  refine Fintype.sum_equiv (finCongr hlen) _ _ fun i => ?_
  simp only [finCongr_apply, Fin.val_cast]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hi : PointEvaluations.toVector (rows.get i) = v[Fin.cast hlen i] := by
    have := List.getElem_of_eq h (i := i.val) (by simp)
    simpa [List.getElem_map, Vector.getElem_toList] using this
  rw [hi]

/-- One column's segments, as `(ζ, ζω)` rows, are its chunk rows. -/
private theorem zipSeg_rows {C : KimchiCurve} {nc : ℕ} (comm : Vector C.Point nc)
    (ev : PointEvaluations (Vector C.ScalarField nc)) :
    (zipSeg C comm ev).toList.map (fun r => (#v[r.2.1, r.2.2] : Vector C.ScalarField evalPts))
      = (chunkRows ev).map PointEvaluations.toVector := by
  apply List.ext_getElem (by simp [zipSeg, chunkRows])
  intro i h₁ h₂
  simp [zipSeg, chunkRows, PointEvaluations.toVector, Vector.toList_zipWith]

/-- The tail rows as a list: the four regions' lists (the vector append is typed at the
literal `tailRowCount`, which `Vector.toList_append` does not see through). -/
private theorem tailRows_toList {C : KimchiCurve} {nc k : ℕ} (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc k) :
    (tailRowsOf C cvk cp).toList
      = (litRowsOf C cvk cp).toList
        ++ ((cp.wComm.zip cp.evals.w).map (fun x => zipSeg C x.1 x.2)).toList
        ++ ((cvk.coefficientsComm.zip cp.evals.coefficients).map (fun x => zipSeg C x.1 x.2)).toList
        ++ (((cvk.sigmaComm.take sigmaRows).zip cp.evals.s).map
              (fun x => zipSeg C x.1 x.2)).toList := by
  unfold tailRowsOf
  erw [Vector.toList_append, Vector.toList_append, Vector.toList_append]

/-- The scalar half's rows are the run's stream: the rows it combines — the kept
challenge-polynomial rows, the public chunks, the `ft` row, the chunks of the `tailRowCount`
tail rows — projected to `(ζ, ζω)` pairs are the run's segment stream so projected. The
evaluations, public chunks, `ft(ζω)` and points are tied to the run's by equations, so a
caller supplies them in whatever form its hypotheses hold. -/
private theorem rows_eq {nc : ℕ} (E : Env C nc) (cp : KimchiProof C nc E.σ.k)
    (pub : Array C.ScalarField) (ms : List Bool) (cvs : List (List C.ScalarField))
    (holds : (List.zipWith (fun m cv => if m then [cv] else []) ms cvs).flatten
      = (cp.olds.map (·.u.toList)).toList)
    (ev : ProofEvaluations (Vector C.ScalarField nc))
    (pv : PointEvaluations (Vector C.ScalarField nc)) (ft1 zM zOM : C.ScalarField)
    (hev : ev = cp.evals) (hpv : pv = runPubEvals C E.σ E.cvk cp pub) (hft : ft1 = cp.ftEval1)
    (hzM : zM = (runOracles C E.σ E.cvk cp pub).zeta ^ 2 ^ E.σ.k)
    (hzOM : zOM = ((runOracles C E.σ E.cvk cp pub).zeta * E.cvk.omega) ^ 2 ^ E.σ.k) :
    let o := runOracles C E.σ E.cvk cp pub
    (sgRows ms (cvs.map fun cv => bPoly (fun i : Fin cv.length => cv.get i) o.zeta)
        (cvs.map fun cv => bPoly (fun i : Fin cv.length => cv.get i) (o.zeta * E.cvk.omega))
      ++ chunkRows pv
      ++ ⟨ftEval0 E.cvk.n E.cvk.zkRows E.cvk.omega (fun i => E.cvk.shifts[i]) E.cvk.endo
              (mdsOfParams C.frSponge.params) o.alpha o.beta o.gamma o.zeta
              (combineAt zM pv.zeta.toArray) (linEvals (combineEvals zM zOM ev)),
            ft1⟩
        :: (evalRows ev).flatMap chunkRows).map PointEvaluations.toVector
    = ((runStreamP C E.σ E.cvk cp pub (runPubEvals C E.σ E.cvk cp pub)).map
        (fun r => (#v[r.2.1, r.2.2] : Vector C.ScalarField evalPts))).toList := by
  intro o
  simp only [o]
  subst hev hpv hft hzM hzOM
  rw [sgRows_kept, holds]
  unfold runStreamP
  rw [Vector.toList_map]
  erw [Vector.toList_append, Vector.toList_append, Vector.toList_append]
  simp only [List.map_append, List.map_cons, List.map_map, List.append_assoc]
  congr 1
  · -- the kept accumulators' rows
    simp only [Function.comp_def, PointEvaluations.toVector, runZetaOmega]
    simp only [List.map_map, Function.comp_def, bPoly_toList, Vector.toList_mk, Array.toList_map]
  congr 1
  · -- the public chunks
    apply List.ext_getElem (by simp [chunkRows])
    intro i h₁ h₂
    simp [chunkRows, PointEvaluations.toVector, Vector.toList_zipWith]
  rw [← List.singleton_append]
  congr 1
  · -- the `ft` row
    simp [PointEvaluations.toVector, runFtEval0P, runLinEvals, runZetaM, runZetaOmegaM,
      runZetaOmega, powPow2_eq, linEvals_combine]
  · -- the tail: every column's chunks
    rw [toList_flatten', tailRows_toList]
    simp only [List.flatMap_def, List.map_flatten, List.map_map,
      Function.comp_def, zipSeg_rows, List.map_append, litRowsOf, evalRows, List.map_cons,
      List.cons_append, List.nil_append, Vector.toList_map, Vector.toList_zip]
    have hz := fun {α : Type} (l₁ : List α) (l₂ : List (PointEvaluations (Vector C.ScalarField nc)))
        (h : l₁.length = l₂.length) =>
      zip_map_snd (fun e => (chunkRows e).map PointEvaluations.toVector) l₁ l₂ h
    rw [hz _ _ (by simp), hz _ _ (by simp), hz _ _ (by simp)]
    simp [zipSeg_rows]
    rfl

/-! ### Reading the cells through the ties -/

/-- `combinedB` over a vector's list is `combinedB` over the vector. -/
private theorem combinedB_toList {F : Type} [Field F] {k m : ℕ} (v : Vector F k) (r : F)
    (x : Fin m → F) :
    combinedB (fun i : Fin v.toList.length => v.toList.get i) r x
      = combinedB (fun i => v[i]) r x := by
  unfold combinedB
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bPoly_toList]
  rfl

/-- The run's evaluation points, as the scalar half lists them. -/
private theorem pointFn_eq {nc : ℕ} (E : Env C nc) (cp : KimchiProof C nc E.σ.k)
    (pub : Array C.ScalarField) :
    (runInput C E.σ E.cvk cp pub).pointFn
      = ![(runOracles C E.σ E.cvk cp pub).zeta,
          (runOracles C E.σ E.cvk cp pub).zeta * E.cvk.omega] := by
  funext j
  fin_cases j <;> rfl

/-- **The two bits read `1` exactly when the claims are honest and the wire's Schnorr equation
holds.** The Schnorr equation is `verifyWith`'s first conjunct, at the wire's transcript;
`SgOk` is not needed. The group read's three `ft` scalars are supplied, not assumed (module
docstring, implementation notes). -/
theorem twoHalves_schnorr
    {nc : ℕ} (E : Env C nc)
    (hbase : 2 ^ 128 < C.base)
    (hscalar : 2 ^ 128 < C.scalar)
    (cp : KimchiProof C nc E.σ.k)
    (pub : Array C.ScalarField)
    -- the group half
    (G : GroupHalf C sf E.σ.k)
    (success : BoolVar C.BaseField)
    (hg : G.Reads E cp pub success)
    -- the scalar half
    (Sc : ScalarHalf C sf' E.σ.k nc)
    (out : FopOutput C.ScalarField)
    (hs : FopVerifyReads (p := C.scalar) (FopParams.ofEnv E Sc.side.toks)
      true E.cvk.n E.cvk.omega (recDigest C (cp.olds.map (·.u)))
      Sc.maskVals Sc.prevVals Sc.claims Sc.evals C.lam
      Sc.side.read Sc.side.unshiftV Sc.V out)
    -- across the two
    (ht : HalvesTies G Sc) (hf : FopTies E cp pub Sc) :
    let run := runInput C E.σ E.cvk cp pub
    let tr := transcriptFrom C (runOracles C E.σ E.cvk cp pub).warm run
    ((↑success : CVar C.BaseField).val G.V = 1
        ∧ (↑out.finalized : CVar C.ScalarField).val Sc.V = 1)
      ↔ Sc.ClaimsHonest E cp pub ∧
        schnorrAt C E.σ tr.1 tr.2.1 tr.2.2 (cipOf run)
          (combinedB (fun i => tr.2.1[i]) run.evalscale run.pointFn)
          (combineCommitments C run.polyscale run.commitments.toArray) run.proof := by
  intro run tr
  have hinjG := castInj128_of_lt _ hbase
  have hinjS := castInj128_of_lt _ hscalar
  have hxi := ScalarHalf.xiExact_of_constrained E hscalar cp hs ht
  -- the shared prechallenges
  obtain ⟨a₀, hαGa, hαSa⟩ := ht.alpha
  obtain ⟨z₀, hζGz, hζSz⟩ := ht.zeta
  obtain ⟨b₀, hβGb, hβSb⟩ := ht.beta
  obtain ⟨g₀, hγGg, hγSg⟩ := ht.gamma
  obtain ⟨ξ₀, hξGx, hξSx⟩ := ht.xi
  -- the group half's read: `α`, `ζ` are the wire's through the shared readings
  obtain ⟨o, hx, hsucc, hdig, hbpc⟩ := hg
  simp only [IvpReads, DeferredValues.toIvpClaims] at hx
  obtain ⟨hdE, hβG, hγG, hαG', hζG', hξG⟩ := hx
  have hαG := (hαG' a₀ hαGa) ▸ hαGa
  have hζG := (hζG' z₀ hζGz) ▸ hζGz
  -- the scalar half's read, at the shared `α`, `ζ`
  simp only [FopVerifyReads] at hs
  obtain ⟨a₀', z₀', hαS, hζS, hs⟩ := hs
  obtain rfl := Reads128.unique hinjS hαSa hαS
  obtain rfl := Reads128.unique hinjS hζSz hζS
  simp only [FopReadsWire, FopChecks, FopParams.ofEnv, FopSide.unshiftV_read] at hs
  obtain ⟨ξ₀', r', ĉ, hξS, hr', -, hxiF, -, hĉ, hcipC, hbC, hpermC, hfin, -⟩ := hs
  obtain rfl : ξ₀ = ξ₀' := Reads128.unique hinjS hξSx hξS
  -- the scalar half's inputs are the run's
  have hζ : endoExpand C.lam z₀.val = (runOracles C E.σ E.cvk cp pub).zeta := by
    simp only [runOracles, fqOracles, FqRun.expand]
    rw [Reads128.unique hinjG hζGz hζG]
  have hα : endoExpand C.lam a₀.val = (runOracles C E.σ E.cvk cp pub).alpha := by
    simp only [runOracles, fqOracles, FqRun.expand]
    rw [Reads128.unique hinjG hαGa hαG]
  have hβ : Sc.claims.deferredValues.plonk.beta.val.val Sc.V
      = (runOracles C E.σ E.cvk cp pub).beta := by
    simp only [runOracles, fqOracles, FqRun.expand]
    unfold Reads128 at hβSb
    rw [Reads128.unique hinjG hβGb hβG] at hβSb
    exact hβSb
  have hγ : Sc.claims.deferredValues.plonk.gamma.val.val Sc.V
      = (runOracles C E.σ E.cvk cp pub).gamma := by
    simp only [runOracles, fqOracles, FqRun.expand]
    unfold Reads128 at hγSg
    rw [Reads128.unique hinjG hγGg hγG] at hγSg
    exact hγSg
  have hd : Sc.claims.spongeDigestBeforeEvaluations.val Sc.V
      = (runOracles C E.σ E.cvk cp pub).digest := by
    rw [ht.digest, hdig, ← hdE]; rfl
  rw [hd, hf.ftEval1, hf.pubEvals, hf.evals] at hr' hxiF
  have hr : endoExpand C.lam r'.val = run.evalscale := by
    show _ = (frOracles C cp _ _).r
    rw [frOracles_eq_frPrechallenges, hr']
  have hxiF' : (↑out.xiCorrect : CVar C.ScalarField).val Sc.V = 1
      → ∃ m : Prechallenge, Reads128 Sc.V Sc.claims.deferredValues.xi m ∧
        m.val = (frPrechallenges C.frSponge.params
            (frTranscript (runOracles C E.σ E.cvk cp pub).digest
            (recDigest C (cp.olds.map (·.u))) cp.ftEval1 (runPubEvals C E.σ E.cvk cp pub)
            cp.evals)).1 :=
    fun h => ⟨ξ₀, hξS, hxiF h⟩
  have hξrun : (∃ m : Prechallenge, Reads128 Sc.V Sc.claims.deferredValues.xi m ∧
        m.val = (frPrechallenges C.frSponge.params
            (frTranscript (runOracles C E.σ E.cvk cp pub).digest
            (recDigest C (cp.olds.map (·.u))) cp.ftEval1 (runPubEvals C E.σ E.cvk cp pub)
            cp.evals)).1) →
      endoExpand C.lam ξ₀.val = run.polyscale := by
    rintro ⟨m, hm, hmv⟩
    rw [Reads128.unique hinjS hξS hm, hmv]
    show _ = (frOracles C cp _ _).xi
    rw [frOracles_eq_frPrechallenges]
  -- the permutation check reads the transcript's challenges and the evaluations, not the
  -- opening: it gives the scalar half's `perm`, and the claim tie the group half's
  rw [hζ, hα, hβ, hγ, hf.evals] at hpermC
  have hplonkIff : (↑out.plonkOk : CVar C.ScalarField).val Sc.V = 1
      ↔ Sc.side.decode Sc.claims.deferredValues.plonk.perm = runPScalar C E.σ E.cvk cp pub ∧
        Sc.side.decode Sc.claims.deferredValues.plonk.zetaToSrsLength
          = runZetaM C E.σ E.cvk cp pub ∧
        Sc.side.decode Sc.claims.deferredValues.plonk.zetaToDomainSize
          = runZetaN C E.σ E.cvk cp pub := by
    simp only [hpermC, ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
    unfold runPScalar runLinEvals runZetaM runZetaN runZetaOmegaM runZetaOmega
    rw [linEvals_combine, powPow2_eq, powPow2_eq, powPow2_eq, KimchiVK.n]
  by_cases hG : G.side.decode G.claims.deferredValues.plonk.perm = runPScalar C E.σ E.cvk cp pub ∧
      G.side.decode G.claims.deferredValues.plonk.zetaToSrsLength = runZetaM C E.σ E.cvk cp pub ∧
      G.side.decode G.claims.deferredValues.plonk.zetaToDomainSize = runZetaN C E.σ E.cvk cp pub
  swap
  · -- either side of the statement gives the group half's three scalars, through the ties
    have hGof : (Sc.side.decode Sc.claims.deferredValues.plonk.perm
          = runPScalar C E.σ E.cvk cp pub ∧
        Sc.side.decode Sc.claims.deferredValues.plonk.zetaToSrsLength
          = runZetaM C E.σ E.cvk cp pub ∧
        Sc.side.decode Sc.claims.deferredValues.plonk.zetaToDomainSize
          = runZetaN C E.σ E.cvk cp pub) → False := fun h =>
      hG ⟨ht.perm.symm.trans h.1, ht.zetaM.symm.trans h.2.1, ht.zetaN.symm.trans h.2.2⟩
    refine ⟨fun hA => absurd (hplonkIff.mp ?_) hGof,
      fun hB => absurd ⟨hB.1.2.2.1, hB.1.2.2.2.1, hB.1.2.2.2.2.1⟩ hGof⟩
    have hA2 := hA.2
    rw [hfin] at hA2
    by_contra hne
    simp [hne] at hA2
  obtain ⟨hpermG, hzetaM, hzetaN⟩ := hG
  -- the opening clause, at the three `ft` scalars
  obtain ⟨U, ns, c₀, chals, rfl, hns, rfl, rfl, hchals, hiff⟩ :=
    hξG hpermG hzetaM hzetaN ξ₀ hξGx
  have hch : chals = (ipaRunAt C (fqRun C E.cvk cp (publicCommitment C E.σ E.cvk pub)).warm
      (G.side.decode G.claims.deferredValues.combinedInnerProduct) cp.opening).2.1.map
        fun m => endoExpand C.lam m.val :=
    Vector.toList_inj.mp (by rw [hchals, Vector.toList_map])
  subst hch
  rw [hsucc] at hiff
  -- the round challenges: the cell lists' readings are equations of lists
  obtain ⟨ms, hmsG, hmsS⟩ := ht.chals
  -- `verify` compares the claimed challenges with the returned ones entry by entry off the
  -- base case; both lists have the SRS's round count, so the ties give the lists
  have hbpc' : G.claims.deferredValues.bulletproofChallenges.toList.map (·.val.val G.V)
      = o.bulletproofChallenges.map (·.val.val G.V) :=
    map_eq_map_of_zip (by simp [hns.length_eq]) (hbpc rfl)
  rw [forall₂_reads128_iff] at hmsG hmsS hns hĉ
  have hĉeq : ĉ = (ipaRunAt C (fqRun C E.cvk cp (publicCommitment C E.σ E.cvk pub)).warm
      (G.side.decode G.claims.deferredValues.combinedInnerProduct) cp.opening).2.1.toList :=
    (List.map_injective_iff.mpr hinjS.prechallenge_injective (hĉ.symm.trans hmsS)).trans
      (List.map_injective_iff.mpr hinjG.prechallenge_injective (hmsG.symm.trans (hbpc'.trans hns)))
  -- the four checks, in wire terms
  rw [hζ, hα, hβ, hγ] at hcipC
  rw [hζ] at hbC
  have hcipIff : endoExpand C.lam ξ₀.val = run.polyscale →
      ((↑out.cipCorrect : CVar C.ScalarField).val Sc.V = 1
        ↔ Sc.side.decode Sc.claims.deferredValues.combinedInnerProduct = cipOf run) := by
    intro hξv
    simp only [hcipC, ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
    rw [hξv, hr, cip_congr _ _ _ _ (rows_eq E cp pub _ _ hf.olds _ _ _ _ _ hf.evals hf.pubEvals
      hf.ftEval1 rfl rfl)]
    exact Iff.rfl
  have hbIff : (↑out.bCorrect : CVar C.ScalarField).val Sc.V = 1
      ↔ Sc.side.decode Sc.claims.deferredValues.b
        = combinedB (fun i =>
            ((ipaRunAt C (fqRun C E.cvk cp (publicCommitment C E.σ E.cvk pub)).warm
              (G.side.decode G.claims.deferredValues.combinedInnerProduct) cp.opening).2.1.map
                (fun m => endoExpand C.lam m.val))[i]) run.evalscale run.pointFn := by
    simp only [hbC, ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
    rw [hr, hĉeq, ← Vector.toList_map, combinedB_toList, pointFn_eq]
  -- assemble, the wire's transcript projected (no unfolding of the sponge runs)
  have hproof : (runInput C E.σ E.cvk cp pub).proof = cp.opening := rfl
  have hwarm : (runOracles C E.σ E.cvk cp pub).warm
      = (fqRun C E.cvk cp (publicCommitment C E.σ E.cvk pub)).warm := by
    simp only [runOracles, fqOracles, FqRun.expand]
  rw [hproof] at hiff
  simp only [ScalarHalf.ClaimsHonest, ClaimsHonest, run, tr, transcriptFrom, hwarm, hproof]
  rw [hfin]
  simp only [ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
  rw [hbIff, hplonkIff]
  constructor
  · rintro ⟨hsG, hxiC, hb, hcip, hperm, hzM, hzN⟩
    have hxiV := hxiF' hxiC
    have hξv := hξrun hxiV
    have hcip' := (hcipIff hξv).1 hcip
    have hcipG : G.side.decode G.claims.deferredValues.combinedInnerProduct = cipOf run :=
      ht.cip.symm.trans hcip'
    rw [hcipG] at hiff hb
    rw [hξv, ← ht.b, hb] at hiff
    exact ⟨⟨hcip', hb, hperm, hzM, hzN, hxiV⟩, hiff.1 hsG⟩
  · -- the converse: the exact `ξ` comparison turns the honest claim into the bit
    rintro ⟨⟨hcip, hb, hperm, hzM, hzN, hxiV⟩, hschnorr⟩
    simp only [ScalarHalf.XiExact] at hxi
    rw [hd, hf.ftEval1, hf.pubEvals, hf.evals] at hxi
    obtain ⟨m, hm, hmv⟩ := hxiV
    have hxiC := hxi m hm hmv
    have hξv := hξrun ⟨m, hm, hmv⟩
    have hcipG : G.side.decode G.claims.deferredValues.combinedInnerProduct = cipOf run :=
      ht.cip.symm.trans hcip
    rw [hcipG] at hiff ⊢
    rw [hξv, ← ht.b, hb] at hiff
    exact ⟨hiff.2 hschnorr, hxiC, hb, (hcipIff hξv).2 hcip, hperm, hzM, hzN⟩

/-- **The two halves accept exactly when the wire verifier does at honest claims, given the
deferred `sg` equation.** Under the `Guards`, the reads and the ties, both bits reading `1`
with `SgOk` is `kimchiVerify` accepting at honest claims. `kimchiVerify` never sees the cells,
so the honest-claims conjunct is what the `finalized` bit adds. -/
theorem twoHalves_kimchiVerify
    {nc : ℕ} (E : Env C nc)
    (hbase : 2 ^ 128 < C.base)
    (hscalar : 2 ^ 128 < C.scalar)
    (cp : KimchiProof C nc E.σ.k)
    (pub : Array C.ScalarField)
    (hguard : Guards C E.cvk cp pub)
    -- the group half
    (G : GroupHalf C sf E.σ.k)
    (success : BoolVar C.BaseField)
    (hg : G.Reads E cp pub success)
    -- the scalar half
    (Sc : ScalarHalf C sf' E.σ.k nc)
    (out : FopOutput C.ScalarField)
    (hs : FopVerifyReads (p := C.scalar) (FopParams.ofEnv E Sc.side.toks)
      true E.cvk.n E.cvk.omega (recDigest C (cp.olds.map (·.u)))
      Sc.maskVals Sc.prevVals Sc.claims Sc.evals C.lam
      Sc.side.read Sc.side.unshiftV Sc.V out)
    -- across the two
    (ht : HalvesTies G Sc) (hf : FopTies E cp pub Sc) :
    ((↑success : CVar C.BaseField).val G.V = 1
        ∧ (↑out.finalized : CVar C.ScalarField).val Sc.V = 1)
        ∧ SgOk E.σ E.cvk cp pub
      ↔ kimchiVerify C E.σ E.cvk cp pub = true ∧ Sc.ClaimsHonest E cp pub := by
  have h := twoHalves_schnorr E hbase hscalar cp pub G success hg Sc out hs ht hf
  -- the body reflection: under the guards, the warm-sponge IPA finish on the run's input
  simp only [transcriptFrom] at h
  rw [h, kimchiVerify_reflects, and_iff_right hguard]
  simp only [SgOk, verifyFrom, transcriptFrom, verifyWith_eq]
  exact ⟨fun ⟨⟨hc, hs⟩, hsg⟩ => ⟨⟨hs, hsg⟩, hc⟩, fun ⟨⟨hs, hsg⟩, hc⟩ => ⟨⟨hc, hs⟩, hsg⟩⟩

end Ties

/-! ## At a step proof: Vesta commitments

A step proof's commitments are Vesta points (`Fq` coordinates) with `Fp` scalars. Its group
half runs first, in the wrap circuit (over `Fq`, `wrapSide`, the claims as `Type1 (FVar Fq)`);
its scalar half one circuit later, in the next step circuit (over `Fp`, `fopStep`, the claims
as `Type1 (FVar Fp)`, carried through the wrap statement). -/

section StepProof

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

/-- The step circuit's scalar side: `Type1` claims decoded as the step reading unshifts them
(`stepShiftOps.reading`, `Type1.fromShifted 255`), the `Fp` linearization tokens. -/
def fopStep (V : Valuation Fp) : FopSide IpaVesta.curve V (Type1 (FVar Fp)) where
  read := (stepShiftOps.reading (V := V) (by decide)).read
  unshiftV := (stepShiftOps.reading (V := V) (by decide)).unshiftV
  toks := Linearization.fpTokens

/-- The wrap circuit's group half of a step proof: `wrapSide` at the circuit's valuation. -/
def GroupHalf.wrap {k : ℕ} (V : Valuation Fq)
    (claims : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq))) :
    GroupHalf IpaVesta.curve (Type1 (FVar Fq)) k :=
  ⟨V, IpaScalarOps.wrap, wrapSide V, claims⟩

/-- The step circuit's scalar half of a step proof: `fopStep` at the circuit's valuation, at
the round count `k` of the finalized proof's SRS (`StepIPARounds` when deployed). -/
def ScalarHalf.step {k nc : ℕ} (V : Valuation Fp)
    (claims : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (evals : ChunkedEvals nc (FVar Fp)) (mask : Vector (BoolVar Fp) MaxProofsVerified)
    (prevChallenges : Vector (Vector (FVar Fp) k) MaxProofsVerified) :
    ScalarHalf IpaVesta.curve (Type1 (FVar Fp)) k nc :=
  ⟨V, fopStep V, claims, evals, mask, prevChallenges⟩

end StepProof

/-! ## At a wrap proof: Pallas commitments

A wrap proof's commitments are Pallas points (`Fp` coordinates) with `Fq` scalars. Its group
half runs first, in the step circuit (over `Fp`, `stepSide`, the claims as split `Type2` cells);
its scalar half one circuit later, in the next wrap circuit (over `Fq`, `fopWrap`, the claims
as `Type2 (FVar Fq)`, carried through the step statement). -/

section WrapProof

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

/-- The wrap circuit's scalar side: `Type2` claims decoded as the wrap reading unshifts them
(`wrapShiftOps.reading`, `Type2.fromShifted 255`), the `Fq` linearization tokens. -/
def fopWrap (V : Valuation Fq) : FopSide IpaPallas.curve V (Type2 (FVar Fq)) where
  read := (wrapShiftOps.reading (V := V)).read
  unshiftV := (wrapShiftOps.reading (V := V)).unshiftV
  toks := Linearization.fqTokens

/-- The step circuit's group half of a wrap proof: `stepSide` at the circuit's valuation. -/
def GroupHalf.step {k : ℕ} (V : Valuation Fp)
    (claims : UnfinalizedProof k (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp)))) :
    GroupHalf IpaPallas.curve (Type2 (SplitField (FVar Fp) (BoolVar Fp))) k :=
  ⟨V, IpaScalarOps.step, stepSide V, claims⟩

/-- The wrap circuit's scalar half of a wrap proof: `fopWrap` at the circuit's valuation, at the
round count `k` of the finalized proof's SRS (`WrapIPARounds` when deployed). The wrap
circuit has no mask (`finalizeOtherProofWrap` absorbs every slot), so every mask cell is the
constant `true_`. -/
def ScalarHalf.wrap {k nc : ℕ} (V : Valuation Fq)
    (claims : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq)))
    (evals : ChunkedEvals nc (FVar Fq))
    (prevChallenges : Vector (Vector (FVar Fq) k) MaxProofsVerified) :
    ScalarHalf IpaPallas.curve (Type2 (FVar Fq)) k nc :=
  ⟨V, fopWrap V, claims, evals, Vector.replicate MaxProofsVerified true_, prevChallenges⟩

/-- The wrap half's mask reads all-true. -/
theorem ScalarHalf.wrap_maskVals {k nc : ℕ} (V : Valuation Fq)
    (claims : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq)))
    (evals : ChunkedEvals nc (FVar Fq))
    (prevChallenges : Vector (Vector (FVar Fq) k) MaxProofsVerified) :
    (ScalarHalf.wrap V claims evals prevChallenges).maskVals
      = List.replicate MaxProofsVerified true := by
  simp only [ScalarHalf.wrap, ScalarHalf.maskVals, Vector.toList_replicate, List.map_replicate,
    true_val, decide_true]

/-- At the wrap half the `olds` tie keeps every slot: the previous-challenge cells read as the
old accumulators' challenges, in order. -/
theorem ScalarHalf.wrap_olds {k nc : ℕ} (V : Valuation Fq)
    (claims : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq)))
    (evals : ChunkedEvals nc (FVar Fq))
    (prevChallenges : Vector (Vector (FVar Fq) k) MaxProofsVerified)
    (olds : List (List Fq)) :
    ((List.zipWith (fun m cv => if m then [cv] else [])
        (ScalarHalf.wrap V claims evals prevChallenges).maskVals
        (ScalarHalf.wrap V claims evals prevChallenges).prevVals).flatten = olds)
      ↔ (ScalarHalf.wrap V claims evals prevChallenges).prevVals = olds := by
  have hkeep : ∀ (n : ℕ) (l : List (List Fq)), l.length = n →
      (List.zipWith (fun m cv => if m then [cv] else []) (List.replicate n true) l).flatten
        = l := by
    intro n l hn
    subst hn
    induction l with
    | nil => rfl
    | cons x xs ih =>
      rw [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, List.flatten_cons,
        if_pos rfl, List.singleton_append, ih]
  rw [ScalarHalf.wrap_maskVals, hkeep _ _ (by simp [ScalarHalf.prevVals])]

end WrapProof

end Pickles
