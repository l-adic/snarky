import Kimchi.Columns
import PicklesFixture
import Pickles.TwoHalves
import Pickles.StepProof
import Snarky.Kimchi.Backend.Compile
import KimchiFixture.Cache
import BulletproofFixture.SRSLoader
import CompElliptic.Fields.Pasta

/-!
# The circuit halves, satisfied on proofs the PureScript suite produced

The two-halves capstones relate a circuit's success bits to `kimchiVerify` for any table
that satisfies the circuit. They say nothing about whether a real proof produces such a
table. This driver runs the modelled half through the Lean prover interpreter on the
inputs of a real proof — the advice code, which nothing else in the tree exercises — and
decides whether the table it produced satisfies every constraint, with the success bits
read back off it.

A scalar half finalizes the proof one level down: the step circuit's finalizes the *step*
proof its verified wrap proof wrapped, the wrap circuit's finalizes the *wrap* proof its
step proof verified in a slot — each proof's scalar-side checks live in the other field.
So a step-half run takes a wrap entry of the cache, follows its `step` link, and lays out
`finalize_other_proof`'s input from the two: the claims, the digest and the branch data
from the wrap statement (the wrap entry's public input), the evaluations and accumulators
from the step proof. A wrap-half run takes a step entry, follows a slot's `prevs` link to
the wrap proof it verified, and lays the input out from that slot of the step statement
and the wrap proof. The same pairs drive the two group halves: the step circuit's
(`verifyProof`, on the step→wrap pair: the wrap statement and proof, the slot's
unfinalized proof) and the wrap circuit's (`incrementallyVerifyProof` on the conditional
sponge, on the wrap→step pair: the wrap statement's claims, the step statement and proof,
the step proof's accumulators under the branch data's mask), each with the verified key's
commitments and the Lagrange bases as constants.

Per run (`PicklesFixture.runHalf`): the interpreter completes (a), the table it completes
(`Snarky.Kimchi.reduceSolved`, `Snarky.Kimchi.makeWitness`) satisfies the assembled system (b),
the success bits read 1 (c) — `finalized` and its four conjuncts for a scalar half, the
opening's `success` for the group half — and, per step-half run, `kimchiVerify` accepts
both proofs (d) — against the SRS they were made with (`srs-cache/`, cut to each proof's
round count) and the Lagrange basis computed from it, memoised under `lagrange-cache/`.

The carry (e): a proof's deferred `sg` obligation is an old accumulator of the next proof on
its curve — wrap k−1's in wrap k's, through the step between them; step k−1's in step k's,
through the wrap between them. Per linked pair, `Pickles.carry` is decided on the two checked
proofs (the accumulator is the predecessor's `sg` with the wire's round challenges of the
predecessor; at the memoized Lagrange points, `Pickles.carryWith_lagrangePoints`),
`Pickles.accOk` on the accumulator, `Pickles.sgOk` on the predecessor, and the two verdicts
must agree. An unlinked accumulator — a front pad, a base-case slot — must
satisfy `accOk` on its own: the dummy's `sg` commits the dummy
challenges. So no accumulator in the file is taken from the prover's list on trust.

The theorems (f): per wrap→step pair the hypotheses of `Pickles.stepProof_kimchiVerify_vesta`
that are facts about data (`theoremHyps`), per step→wrap pair those of
`Pickles.wrapProof_kimchiVerify_pallas` (`wrapTheoremHyps`) — each with the statement's two
circuits as `compile` builds them, so either theorem's assumptions are shown to hold together
on a proof the real prover made.

Run: `PROOF_CACHE=<file> lake exe check-halves` from `formal/`; the default is
`SimpleChain.json`. `SRS_CACHE_DIR` and `LAGRANGE_CACHE_DIR` relocate the two caches.
`HALVES` narrows the run to a comma-separated subset of `step`, `wrap`, `step-group`,
`wrap-group`, `verify`, `carry`, `theorem` (the default is all seven). Every lane over a
step proof runs at the entry's chunk count (`step`, `verify`, `wrap-group`, `theorem`, `carry`);
a wrap proof is one chunk.

The runs go to `HALVES_JOBS` workers (default 4), after a warm-up that builds every SRS
(`Bulletproof.Fixture.SRSLoader.loadSRS`), Lagrange memo (`Bulletproof.Fixture.lagrangeBasisCached`)
and checked key they read; each run's output is printed whole, in the order above. The
`kimchiVerify` and `sgOk` verdicts several lanes ask of one proof are computed once (`Memo`).
-/

open Lean Snarky Snarky.Kimchi PicklesFixture Kimchi.Fixture Bulletproof
open CompElliptic.Fields.Pasta
open scoped Kimchi

/-- The step side's `finalize_other_proof` input from a wrap entry and the checked step proof
it wrapped, at the step proof's `k` rounds: the unfinalized proof off the wrap statement
(`wrapStatementOf`), the evaluations off the step proof, the mask and `domain_log2` off the
branch data, and the step proof's accumulators' challenges in the LAST slots
(`unpackBranchData`), a zero vector in an absent one, which its mask bit leaves unread. -/
def stepFopInput (w : Cache.Entry CW) {k nc : ℕ} (cpS : Kimchi.Verifier.KimchiProof CS nc k) :
    Except String (StepFop k nc) := do
  let st ← wrapStatementOf toStep k w.publicInput
  let dv := st.proofState.deferredValues
  let u : Pickles.UnfinalizedProof k Fp Bool (Type1 Fp) :=
    { deferredValues := dv.toDeferredValues, shouldFinalize := true
      spongeDigestBeforeEvaluations := st.proofState.spongeDigestBeforeEvaluations }
  let accs := cpS.olds.toList.map (·.u)
  let prev : Vector (Vector Fp k) Pickles.MaxProofsVerified ←
    if h : accs.length ≤ Pickles.MaxProofsVerified then
      let slots := List.replicate (Pickles.MaxProofsVerified - accs.length) (Vector.replicate k 0)
        ++ accs
      pure ⟨slots.toArray, by simp [slots]; omega⟩
    else throw s!"accumulators: {accs.length}, more than {Pickles.MaxProofsVerified}"
  return (u, ← chunkedEvalsOf CS cpS, dv.branchData.proofsVerifiedMask, prev,
    dv.branchData.domainLog2)

/-- The scalar half's five bits. -/
def fopBits {F : Type} {k : ℕ} (o : Pickles.FopOutput F k) : List (String × BoolVar F) :=
  [("finalized", o.finalized), ("xiCorrect", o.xiCorrect), ("bCorrect", o.bCorrect),
   ("cipCorrect", o.cipCorrect), ("plonkOk", o.plonkOk)]

/-- The step half on its records at a known domain. -/
def runStep {k nc : ℕ} (dom : Pickles.KnownDomain Fp) (inp : StepFop k nc) :
    IO (Bool × List (String × ℕ)) :=
  runHalf (a := StepFop k nc) Kimchi.Fixture.PS.fpSide (fopStepOnAt [dom]) fopBits inp

/-- The wrap half on its records at a domain. -/
def runWrap {k : ℕ} (domainLog2 : ℕ) (inp : Pickles.WrapFop k 1) : IO (Bool × List (String × ℕ)) :=
  runHalf (a := Pickles.WrapFop k 1) Kimchi.Fixture.PS.fqSide (fopWrapOnAt domainLog2) fopBits inp

/-- The step circuit's group half on its records: the wrap key's commitments as constants,
the `x_hat` tables at the Lagrange bases, the SRS's blinding base. -/
def runGroup {ks kw : ℕ} (cvk : Kimchi.Verifier.KimchiVK CW 1)
    (basis : Array (Vector CW.Point 1)) (h : CW.Point) (inp : Pickles.StepGroup ks kw 1 Fp Bool) :
    IO (Bool × List (String × ℕ)) := do
  let tab ← IO.ofExcept (firstBases? basis)
  runHalf (a := Pickles.StepGroup ks kw 1 Fp Bool) Kimchi.Fixture.PS.fpSide
    (groupStepOn (Pickles.keyCellsOf xhatStepCell cvk) tab h) (fun b => [("success", b)]) inp

/-- The wrap circuit's group half on its records: the step key's commitments as constants,
the Lagrange bases, the SRS's blinding base. -/
def runGroupWrap {ks kw padN nc : ℕ} (cvk : Kimchi.Verifier.KimchiVK CS nc)
    (basis : Array (Vector CS.Point nc)) (h : CS.Point)
    (inp : Pickles.WrapGroup ks kw padN nc Fq Bool) :
    IO (Bool × List (String × ℕ)) := do
  let tab ← IO.ofExcept (firstBases? basis)
  runHalf (a := Pickles.WrapGroup ks kw padN nc Fq Bool) Kimchi.Fixture.PS.fqSide
    (groupWrapOn (Pickles.keyCellsOf xhatWrapCell cvk) tab (xhatWrapCell h))
    (fun b => [("success", b)])
    inp

/-- The wrap circuit's group-half input from a wrap entry, the step entry it wrapped and the
checked step proof at `ks` rounds, past `padN` padding slots: the wrap statement, the step
statement carried by value into the wrap field, the step proof (`z₁`, `z₂` as their Type1
registers `(s − 2^255 − 1)/2`), its accumulators' `sg`. -/
def wrapGroupInput (w : Cache.Entry CW) (s : Cache.Entry CS) (padN : ℕ) (pad : CS.Point)
    {ks nc : ℕ} (cpS : Kimchi.Verifier.KimchiProof CS nc ks) :
    Except String (Pickles.WrapGroup ks Pickles.WrapIPARounds padN nc Fq Bool) := do
  let statement ← wrapStatementOf id ks w.publicInput
  let st ← stepStatementOf toWrap Pickles.WrapIPARounds (Pickles.MaxProofsVerified - padN)
    s.publicInput
  let pr ← ivpProofOf CS (fun z => ⟨toWrap (Pasta.Shifted.shiftType1 255 z)⟩) cpS
  return { statement, stepStatement := st, proof := pr,
           sgOld := ← sgOldOf CS (Pickles.MaxProofsVerified - padN) pad cpS }

/-- The step circuit's group-half input from a wrap entry, a step entry's slot that verified
it and the checked wrap proof at `kw` rounds: the wrap statement carried by value into the
step field, the slot of the step statement, the wrap proof (`z₁`, `z₂` as their Type2
registers `s − 2^255`, split into a half and a parity bit), its two accumulators' `sg`, and
`is_base_case = false`: the slot is a real one. -/
def stepGroupInput (w : Cache.Entry CW) (s : Cache.Entry CS) (slot : ℕ) (pad : CW.Point)
    {kw : ℕ} (cpW : Kimchi.Verifier.KimchiProof CW 1 kw) :
    Except String (Pickles.StepGroup Pickles.StepIPARounds kw 1 Fp Bool) := do
  let statement ← wrapStatementOf toStep Pickles.StepIPARounds w.publicInput
  let n := (s.publicInput.size - 1) / (18 + kw)
  let st ← stepStatementOf id kw n s.publicInput
  let some u := st.proofState.unfinalizedProofs.toList[slot]? | throw s!"slot {slot} of {n}"
  let split (z : CW.ScalarField) : Type2 (SplitField Fp Bool) :=
    let t := (Pasta.Shifted.shiftType2 255 z).val
    ⟨⟨((t / 2 : ℕ) : Fp), decide (t % 2 = 1)⟩⟩
  let pr ← ivpProofOf CW split cpW
  return { statement, claims := u, proof := pr
           sgOld := ← sgOldOf CW Pickles.MaxProofsVerified pad cpW, isBaseCase := false }

/-- The wrap side's `finalize_other_proof` input from a step entry's slot and the checked wrap
proof that slot verified, at the wrap proof's `k` rounds: the slot of the step statement
(`stepStatementOf`) with each split claim as its `Type2` register `2·half + parity`, the
evaluations and the `MaxProofsVerified` accumulators off the wrap proof. -/
def wrapFopInput (s : Cache.Entry CS) (slot : ℕ) {k : ℕ}
    (cpW : Kimchi.Verifier.KimchiProof CW 1 k) : Except String (Pickles.WrapFop k 1) := do
  let n := (s.publicInput.size - 1) / (18 + k)
  let st ← stepStatementOf toWrap k n s.publicInput
  let some u2 := st.proofState.unfinalizedProofs.toList[slot]? | throw s!"slot {slot} of {n}"
  let t (x : Type2 (SplitField Fq Bool)) : Type2 Fq :=
    ⟨2 * x.val.sDiv2 + (if x.val.sOdd then 1 else 0)⟩
  let dv := u2.deferredValues
  let u : Pickles.UnfinalizedProof k Fq Bool (Type2 Fq) :=
    { deferredValues :=
        { plonk := { alpha := dv.plonk.alpha, beta := dv.plonk.beta, gamma := dv.plonk.gamma,
                     zeta := dv.plonk.zeta, perm := t dv.plonk.perm,
                     zetaToSrsLength := t dv.plonk.zetaToSrsLength,
                     zetaToDomainSize := t dv.plonk.zetaToDomainSize }
          combinedInnerProduct := t dv.combinedInnerProduct, b := t dv.b, xi := dv.xi
          bulletproofChallenges := dv.bulletproofChallenges }
      shouldFinalize := true
      spongeDigestBeforeEvaluations := u2.spongeDigestBeforeEvaluations }
  let accs := cpW.olds.map (·.u)
  let prev : Vector (Vector Fq k) Pickles.MaxProofsVerified ←
    if h : accs.size = Pickles.MaxProofsVerified then pure ⟨accs, h⟩
    else throw s!"wrap accumulators: {accs.size}, expected {Pickles.MaxProofsVerified}"
  return { claims := u, evals := ← chunkedEvalsOf CW cpW, prev }

/-- The hypotheses of `Pickles.stepProof_kimchiVerify_vesta` that are facts about data,
decided on a wrap entry and the step entry it wrapped — so the theorem's assumptions are
shown to hold together on a proof the real prover made, and its conclusion is checked at the
public input it names:

* the step SRS and key pass their checks (`Srs.check`, `Key.check`); the key is parsed at the
  SRS's chunk count on its domain, so `hnc` holds by definition (`Wire.runNc`);
* the file's step domains form a `KnownDomains`, and the wrap statement's `domain_log2` is
  the key's (`hdom`);
* the packed step statement, carried into the wrap field, reads back as the step proof's
  public input (`wrapPublicInput`);
* the SRS avoids the key's Lagrange relations, one per packed scalar (`havoid`), decided on the
  SRS's Lagrange points on the key's domain (`Key.avoids_lagrangeRelations_iff`);
* the wrap statement's `messages_for_next_wrap_proof` is the digest `wrapVerifyAt` asserts:
  the padding, the slots' expanded round challenges, the step opening's `sg`;
* `Guards`, `SgOk`, and the conclusion `kimchiVerify`, at that public input.

Booleanity is no hypothesis of the theorem any more — the statement's boolean cells are
constrained by the `x_hat` gadget, the mask by the branch data's input check — and both sets
of rows are among the ones decided here. -/
def theoremHyps (w : Cache.Entry CW) (s : Cache.Entry CS) (steps : Array (Cache.Entry CS))
    (loaded : IO.Ref (List (ℕ × SRS CS.Point)))
    (keys : IO.Ref (List (String × Checked CS))) (memo : Memo) : IO Bool := do
  let ⟨nc, S, K⟩ ← keyFor CS "vesta" vestaBase.sqrt? loaded keys s
  let σ := S.σ
  let cvk := K.cvk
  let cp ← checkedFor CS nc σ s
  do
    let cands := steps.toList.map (·.vk.domainLog2)
    let some doms := Pickles.KnownDomains.ofList? nc cands
      | IO.println s!"    ✗ the file's step domains {cands} are no KnownDomains \
          at {nc} chunks"
        return false
    let n := (s.publicInput.size - 1) / (18 + Pickles.WrapIPARounds)
    if Pickles.MaxProofsVerified < n then
      throw (IO.userError s!"step statement: {n} slots")
    -- the group input is indexed by its padding slots
    let padN := Pickles.MaxProofsVerified - n
    let wst ← match wrapStatementOf id σ.k w.publicInput with
      | .error e => throw (IO.userError s!"wrap statement: {e}") | .ok r => pure r
    let st ← match stepStatementOf toWrap Pickles.WrapIPARounds (Pickles.MaxProofsVerified - padN)
        s.publicInput with
      | .error e => throw (IO.userError s!"step statement: {e}") | .ok r => pure r
    let dv := wst.proofState.deferredValues
    let hdom := decide (dv.branchData.domainLog2 = (s.vk.domainLog2 : Fq))
    -- the statement as constant cells: every reading below is the value's own
    let stVar : Pickles.StepStatement
        (Pickles.UnfinalizedProof Pickles.WrapIPARounds (FVar Fq) (BoolVar Fq)
          (Type2 (SplitField (FVar Fq) (BoolVar Fq))))
        (FVar Fq) (Pickles.MaxProofsVerified - padN) := CircuitType.constVar (F := Fq) st
    let V : Valuation Fq := fun _ => 0
    let pub := Pickles.wrapPublicInput σ cvk V stVar
    let pubOk := decide (pub = s.publicInput)
    -- the message digest `wrapVerifyAt` asserts
    let params := IpaVesta.curve.sponge.params
    let expanded := st.proofState.unfinalizedProofs.toList.map fun u =>
      u.deferredValues.bulletproofChallenges.toList.map fun c =>
        Poseidon.FqSponge.endoExpand (F := Fq) (IpaPallas.curve.lam : Fq) c.val.val
    let sg := cp.opening.sg
    let digest := (Poseidon.squeeze params (Poseidon.absorb params (wrapMsgSpongeState n)
      (expanded.flatten ++ [sg.x, sg.y]))).1
    let msgOk := decide (digest = wst.proofState.messagesForNextWrapProof)
    let guards := decide (cp.olds.size = cvk.prevChallenges ∧ pub.size = cvk.publicCount)
    let L ← basisFor CS "vesta" σ nc s
    let tab ← IO.ofExcept (firstBases? (m := CircuitType.size Fp
      (Pickles.StepStatement (Pickles.UnfVal Pickles.WrapIPARounds) Fp
        (Pickles.MaxProofsVerified - padN))) L)
    let sg' ← memoized memo.sg (memoKey CS "vesta" σ.k s pub) fun _ =>
      Pickles.sgOkWith σ cvk L cp pub
    let kv ← memoized memo.verify (memoKey CS "vesta" σ.k s pub) fun _ =>
      Kimchi.Verifier.kimchiVerifyWith CS σ cvk L cp pub
    -- `havoid`, the theorem's own hypothesis, decided on the memoized Lagrange points as the
    -- right side of `Key.avoids_lagrangeRelations_iff`. The bounded `∀` is pinned to the list
    -- walk: left to resolution it goes to `Vector`'s finite-type instance, which enumerates
    -- the curve.
    let Lm := tab.toList
    let avoidOk := @decide (∀ Ps ∈ Lm, ∀ c : Fin nc, Ps[c] ≠ 0) (List.decidableBAll _ _)
    IO.println s!"    keys=true rounds={σ.k} domains={cands} \
      key=2^{s.vk.domainLog2} hdom={hdom} \
      pub={pubOk} ({pub.size} cells) avoids={avoidOk} msgDigest={msgOk} \
      guards={guards} \
      sgOk={sg'} kimchiVerify={kv}"
    -- `hsatS`: the theorem's scalar circuit, as `compile` builds it — the input's check (the
    -- branch data's; the rest of the input is unchecked) and then `scalarCircuit`, which
    -- asserts `finalized`
    let (u, ev, mask, prev, d) ← match stepFopInput w cp with
      | .error e => throw (IO.userError s!"step input: {e}") | .ok r => pure r
    let sinp : Pickles.StepProof.ScalarIn σ.k nc :=
      { branch := ⟨d, mask⟩, fop := ⟨{ claims := u, evals := ev, prev }⟩ }
    let (satS, _) ← runHalf (a := Pickles.StepProof.ScalarIn σ.k nc) Kimchi.Fixture.PS.fpSide
      (fun (v : Pickles.StepProof.ScalarVar σ.k nc) => do
        CheckedType.check (c := KimchiConstraint Fp) (val := Pickles.StepProof.ScalarIn σ.k nc) v
        Pickles.StepProof.scalarCircuit doms v)
      (fun _ => []) sinp
    IO.println s!"    scalarCircuit (input check, body, finalized asserted): satisfies={satS}"
    -- `hsatG`: the theorem's group circuit — the verify block with its success bit and its
    -- message digest asserted — on the wrap statement, the step statement and proof, and
    -- the slots' expanded round challenges; its key cells are the step key's, as constants,
    -- its sponge after the index digest is that key's, and its Lagrange points the memoized
    -- ones (`StepProof.groupCircuit` is `groupCircuitWith` at the key's)
    let ginp ← match wrapGroupInput w s padN (σ.g ⟨0, Nat.two_pow_pos _⟩) cp with
      | .error e => throw (IO.userError s!"wrap group input: {e}") | .ok r => pure r
    let newBp : Vector (Vector Fq Pickles.WrapIPARounds) (Pickles.MaxProofsVerified - padN) :=
      st.proofState.unfinalizedProofs.map fun u =>
        u.deferredValues.bulletproofChallenges.map fun c =>
          Poseidon.FqSponge.endoExpand (F := Fq) (IpaPallas.curve.lam : Fq) c.val.val
    let (satG, _) ← runHalf (a := Pickles.StepProof.GroupIn σ.k Pickles.WrapIPARounds padN nc)
      Kimchi.Fixture.PS.fqSide
      (fun (v : Pickles.StepProof.GroupVar σ.k Pickles.WrapIPARounds padN nc) => do
        let key := Pickles.keyCellsOf xhatWrapCell cvk
        let sv ← wrapIndexSponge key
        Pickles.StepProof.groupCircuitWith σ.h tab key sv
          (SpongeVar.ofConstants (wrapMsgSpongeState n)) v)
      (fun _ => []) ⟨{ group := ginp, newBp }⟩
    IO.println s!"    groupCircuit: satisfies={satG}"
    return hdom && pubOk && msgOk && guards && sg' && kv && avoidOk && satS && satG

/-- The hypotheses of `Pickles.wrapProof_kimchiVerify_pallas` that are facts about data,
decided on a step entry's slot and the wrap entry that slot verified — the twin of
`theoremHyps`:

* the wrap SRS and key pass their checks (`Srs.check`, `Key.check`); the key is parsed at the
  SRS's chunk count on its domain, so `hnc` holds by definition (`Wire.runNc`);
* the packed wrap statement, carried into the step field and flattened with its
  optional-feature cells, is the wrap proof's public input (`stepPublicInput`);
* the packed statement fits in the SRS (`hsmall`), and the SRS avoids the step relations
  (`havoid`), decided on the SRS's Lagrange points on the key's domain
  (`avoids_stepRelationsAt_iff`);
* `Guards`, `SgOk`, and the conclusion `kimchiVerify`, at that public input;
* both circuits, as `compile` builds them, are satisfied: `WrapProof.scalarCircuit` with
  `finalized` asserted, `WrapProof.groupCircuit` with its success bit asserted at a slot that
  must verify. -/
def wrapTheoremHyps (w : Cache.Entry CW) (s : Cache.Entry CS) (slot : ℕ)
    (loaded : IO.Ref (List (ℕ × SRS CW.Point)))
    (keys : IO.Ref (List (String × Checked CW))) (memo : Memo) : IO Bool := do
  let (S, K) ← keyFor1 CW "pallas" pallasBase.sqrt? loaded keys w
  let σ := S.σ
  let cvk := K.cvk
  let (_, cp) ← checkedAt CW σ w
  let wst ← match wrapStatementOf toStep Pickles.StepIPARounds w.publicInput with
    | .error e => throw (IO.userError s!"wrap statement: {e}") | .ok r => pure r
  -- the statement as constant cells: every reading below is the value's own
  let stVar : Pickles.WrapStatement Pickles.StepIPARounds (FVar Fp) (BoolVar Fp)
      (Type1 (FVar Fp)) := CircuitType.constVar (F := Fp) wst
  let V : Valuation Fp := fun _ => 0
  let pub := Pickles.stepPublicInput V stVar
  let pubOk := decide (pub = w.publicInput)
  let smallOk := decide (stVar.packed.toList.length ≤ 2 ^ σ.k)
  let L ← basisFor CW "pallas" σ 1 w
  let tab ← IO.ofExcept (firstBases? (m := CircuitType.size Fp
    (Pickles.PackedWrapStatement Pickles.StepIPARounds (Type1 Fp) Fp)) L)
  -- `havoid`, decided on the memoized Lagrange points as the right side of
  -- `avoids_stepRelationsAt_iff`, which holds under `hsmall` and a statement that fits in the
  -- domain, as it does under `guards`: the key's count is at most its domain; the bounded `∀`
  -- is pinned to the list walk
  let Lm := tab.toList
  let avoidOk :=
    decide (∀ c : Fin 1, Pickles.corrSumPt (C := CW) stVar.packed.toList Lm c ≠ 0)
      && @decide (∀ Ps ∈ Lm, ∀ c : Fin 1, Ps[c] ≠ 0) (List.decidableBAll _ _)
  let guards := decide (cp.olds.size = cvk.prevChallenges ∧ pub.size = cvk.publicCount)
  let sg' ← memoized memo.sg (memoKey CW "pallas" σ.k w pub) fun _ =>
    Pickles.sgOkWith σ cvk L cp pub
  let kv ← memoized memo.verify (memoKey CW "pallas" σ.k w pub) fun _ =>
    Kimchi.Verifier.kimchiVerifyWith CW σ cvk L cp pub
  IO.println s!"    keys=true rounds={σ.k} key=2^{cvk.domainLog2} pub={pubOk} \
    ({pub.size} cells) small={smallOk} avoids={avoidOk} guards={guards} \
    sgOk={sg'} kimchiVerify={kv}"
  -- `hsatS`: the theorem's scalar circuit, which asserts `finalized`
  let finp ← match wrapFopInput s slot cp with
    | .error e => throw (IO.userError s!"wrap input: {e}") | .ok r => pure r
  let (satS, _) ← runHalf (a := Pickles.WrapProof.ScalarIn σ.k 1) Kimchi.Fixture.PS.fqSide
    (fun (v : Pickles.WrapProof.ScalarVar σ.k 1) => Pickles.WrapProof.scalarCircuit cvk v)
    (fun _ => []) ⟨finp⟩
  IO.println s!"    scalarCircuit (finalized asserted): satisfies={satS}"
  -- `hsatG`: the theorem's group circuit — `verify` with its success bit asserted — on the
  -- wrap statement, the slot's claims and the wrap proof; its key cells are the wrap key's,
  -- as constants, its sponge after the index digest is that key's, and its Lagrange points the
  -- memoized ones (`WrapProof.groupCircuit` is `groupCircuitWith` at the key's)
  let ginp ← match stepGroupInput w s slot (σ.g ⟨0, Nat.two_pow_pos _⟩) cp with
    | .error e => throw (IO.userError s!"step group input: {e}") | .ok r => pure r
  let (satG, _) ← runHalf (a := Pickles.WrapProof.GroupIn Pickles.StepIPARounds σ.k 1)
    Kimchi.Fixture.PS.fpSide
    (fun (v : Pickles.WrapProof.GroupVar Pickles.StepIPARounds σ.k 1) => do
      let key := Pickles.keyCellsOf xhatStepCell cvk
      let sv ← stepIndexSponge key
      Pickles.WrapProof.groupCircuitWith σ.h tab key sv v)
    (fun _ => []) ⟨ginp⟩
  IO.println s!"    groupCircuit: satisfies={satG}"
  return pubOk && smallOk && avoidOk && guards && sg' && kv && satS && satG

def main : IO Unit := do
  let path := (← IO.getEnv "PROOF_CACHE").getD
    "../packages/pickles/test/fixtures/proof-cache/SimpleChain.json"
  let raw ← IO.FS.readFile path
  let (wraps, _) ← match Cache.parseFile CW Kimchi.Fixture.PS.fqSide.endo pallasBase.sqrt? raw with
    | .error e => throw (IO.userError s!"wrap side: {e}") | .ok r => pure r
  let (steps, _) ← match Cache.parseFile CS Kimchi.Fixture.PS.fpSide.endo vestaBase.sqrt? raw with
    | .error e => throw (IO.userError s!"step side: {e}") | .ok r => pure r
  IO.println s!"{path}: {wraps.size} wrap proofs, {steps.size} step proofs"
  let lanes := (← IO.getEnv "HALVES").getD
    "step,wrap,step-group,wrap-group,verify,carry,theorem"
  let halves := lanes.splitOn ","
  let on (h : String) : Bool := halves.contains h
  let limit := ((← IO.getEnv "LIMIT").bind String.toNat?).getD wraps.size
  let nJobs := ((← IO.getEnv "HALVES_JOBS").bind String.toNat?).getD 4
  let vestaSRS ← IO.mkRef ([] : List (ℕ × SRS CS.Point))
  let pallasSRS ← IO.mkRef ([] : List (ℕ × SRS CW.Point))
  let vestaKeys ← IO.mkRef ([] : List (String × Checked CS))
  let pallasKeys ← IO.mkRef ([] : List (String × Checked CW))
  let memo ← Memo.new
  -- The warm-up: every SRS, Lagrange memo and checked key the jobs read is built here, one
  -- at a time, so the workers only read shared data (and never write a memo file at once).
  let t0 ← IO.monoMsNow
  let needKeys := on "theorem" || on "carry"
  let needPoints := needKeys || on "verify" || on "wrap-group" || on "step-group"
  for s in steps do
    let σ ← srsAt CS "vesta" vestaBase.sqrt? vestaSRS s.proof.opening.lr.size
    let ⟨nc, _, _⟩ ← checkedAny CS σ s
    if needKeys then discard <| keyFor CS "vesta" vestaBase.sqrt? vestaSRS vestaKeys s
    if needPoints then discard <| basisFor CS "vesta" σ nc s
  for w in wraps do
    let σ ← srsAt CW "pallas" pallasBase.sqrt? pallasSRS w.proof.opening.lr.size
    let ⟨nc, _, _⟩ ← checkedAny CW σ w
    if needKeys then discard <| keyFor CW "pallas" pallasBase.sqrt? pallasSRS pallasKeys w
    if needPoints then discard <| basisFor CW "pallas" σ nc w
  IO.println s!"warm-up: {(← IO.monoMsNow) - t0} ms; {nJobs} worker(s)"
  let mut allOk := true
  let mut jobs : Array (IO Bool) := #[]
  -- One timed run of a half.
  let report (what : String) (run : IO (Bool × List (String × ℕ))) : IO Bool := do
    let t0 ← IO.monoMsNow
    let (sat, bits) ← run
    let t1 ← IO.monoMsNow
    let ok := sat ∧ bits.all (·.2 = 1)
    IO.println s!"  {if ok then "✓" else "✗"} {what}: satisfies={sat} \
      bits={bits.map fun (n, v) => s!"{n}={v}"} {t1 - t0} ms"
    return ok
  -- One timed verdict.
  let reportBool (what : String) (run : IO Bool) : IO Bool := do
    let t0 ← IO.monoMsNow
    let ok ← run
    let t1 ← IO.monoMsNow
    IO.println s!"  {if ok then "✓" else "✗"} {what} {t1 - t0} ms"
    return ok
  for w in wraps.toList.take limit do
    let some (d, pi) := w.step | continue
    let some s := steps.find? (fun s => s.vkDigest = d ∧ s.publicInputKey = pi)
      | IO.println s!"  ✗ wrap {w.vkDigest.take 10}…: its step {d.take 10}… is not in the file"
        allOk := false
        continue
    let pair := s!"wrap→step {d.take 10}…"
    if on "step" then
      jobs := jobs.push do
        let σS ← srsAt CS "vesta" vestaBase.sqrt? vestaSRS s.proof.opening.lr.size
        let ⟨nc, _, cpS⟩ ← checkedAny CS σS s
        let inp ← match stepFopInput w cpS with
          | .error e => throw (IO.userError s!"step input: {e}") | .ok r => pure r
        report s!"step half on {pair} (domain 2^{s.vk.domainLog2}, {nc} chunk(s), \
            zk_rows {Pickles.zkRowsOf nc})"
          (runStep ⟨s.vk.domainLog2, s.vk.omega⟩ inp)
    if on "verify" then
      jobs := jobs.push do
        let t0 ← IO.monoMsNow
        let stepOk ← verifies CS "vesta" vestaBase.sqrt? vestaSRS memo s
        let wrapOk ← verifies CW "pallas" pallasBase.sqrt? pallasSRS memo w
        let t1 ← IO.monoMsNow
        IO.println s!"  {if stepOk ∧ wrapOk then "✓" else "✗"} kimchiVerify on {pair}: \
          step={stepOk} wrap={wrapOk} {t1 - t0} ms"
        return stepOk ∧ wrapOk
    if on "theorem" then
      jobs := jobs.push <| reportBool s!"theorem hypotheses on {pair}"
        (theoremHyps w s steps vestaSRS vestaKeys memo)
    if on "wrap-group" then
      jobs := jobs.push do
        let n := (s.publicInput.size - 1) / (18 + Pickles.WrapIPARounds)
        let r := s.proof.opening.lr.size
        let σS ← srsAt CS "vesta" vestaBase.sqrt? vestaSRS r
        let ⟨nc, cvkS, cpS⟩ ← checkedAny CS σS s
        if Pickles.MaxProofsVerified < n then
          throw (IO.userError s!"step statement: {n} slots")
        let ginp ← match wrapGroupInput w s (Pickles.MaxProofsVerified - n)
            (σS.g ⟨0, Nat.two_pow_pos _⟩) cpS with
          | .error e => throw (IO.userError s!"wrap group input: {e}") | .ok i => pure i
        let basis ← basisFor CS "vesta" σS nc s
        report s!"wrap group half on {pair} ({n} slot(s), {r} rounds, {nc} chunk(s))"
          (runGroupWrap cvkS basis σS.h ginp)
  for s in steps.toList.take limit do
    for (ref, slot) in s.prevs.toList.zipIdx do
      let some (d, pi) := ref | continue
      let some w := wraps.find? (fun w => w.vkDigest = d ∧ w.publicInputKey = pi)
        | IO.println s!"  ✗ step {s.vkDigest.take 10}… slot {slot}: its wrap {d.take 10}… \
            is not in the file"
          allOk := false
          continue
      let pair := s!"step→wrap {d.take 10}… (slot {slot})"
      let r := w.proof.opening.lr.size
      if on "wrap" then
        jobs := jobs.push do
          let σW ← srsAt CW "pallas" pallasBase.sqrt? pallasSRS r
          let (_, cpW) ← checkedAt CW σW w
          let inp ← match wrapFopInput s slot cpW with
            | .error e => throw (IO.userError s!"wrap input: {e}") | .ok i => pure i
          report s!"wrap half on {pair} (domain 2^{w.vk.domainLog2}, {r} rounds)"
            (runWrap w.vk.domainLog2 inp)
      if on "step-group" then
        jobs := jobs.push do
          let σW ← srsAt CW "pallas" pallasBase.sqrt? pallasSRS r
          let (cvkW, cpW) ← checkedAt CW σW w
          let ginp ← match stepGroupInput w s slot (σW.g ⟨0, Nat.two_pow_pos _⟩) cpW with
            | .error e => throw (IO.userError s!"step group input: {e}") | .ok i => pure i
          let basis ← basisFor CW "pallas" σW 1 w
          report s!"step group half on {pair}" (runGroup cvkW basis σW.h ginp)
      if on "theorem" then
        jobs := jobs.push <| reportBool s!"theorem hypotheses on {pair}"
          (wrapTheoremHyps w s slot pallasSRS pallasKeys memo)
  if on "carry" then
    -- Wrap k−1 → wrap k through the step between them: the step's slot `j` is the wrap's
    -- accumulator `pad + j`; the pads in front and the base-case slots are unlinked.
    for w in wraps.toList.take limit do
      let some (d, pi) := w.step | continue
      let some s := steps.find? (fun s => s.vkDigest = d ∧ s.publicInputKey = pi) | continue
      let tag := s!"wrap {w.vkDigest.take 10}…/{w.publicInputKey.take 10}…"
      let pad := w.proof.prevChallenges.size - s.prevs.size
      for j in List.range pad do
        jobs := jobs.push <| reportBool s!"pad accumulator {j} of {tag}: AccOk"
          (padOk CW "pallas" pallasBase.sqrt? pallasSRS w j)
      for (ref, j) in s.prevs.toList.zipIdx do
        match ref with
        | none =>
          jobs := jobs.push <| reportBool s!"base-case accumulator {pad + j} of {tag}: AccOk"
            (padOk CW "pallas" pallasBase.sqrt? pallasSRS w (pad + j))
        | some (d', pi') =>
          let some w' := wraps.find? (fun w => w.vkDigest = d' ∧ w.publicInputKey = pi')
            | IO.println s!"  ✗ {tag}: its predecessor wrap {d'.take 10}… is not in the file"
              allOk := false
              continue
          jobs := jobs.push <| reportBool s!"carry wrap→wrap into accumulator {pad + j} of {tag}"
            (carriesInto CW "pallas" pallasBase.sqrt? pallasSRS pallasKeys memo w' w (pad + j))
    -- Step k−1 → step k through the wrap between them: slot `j` is accumulator `j`.
    for s in steps.toList.take limit do
      let tag := s!"step {s.vkDigest.take 10}…/{s.publicInputKey.take 10}…"
      for (ref, j) in s.prevs.toList.zipIdx do
        match ref with
        | none =>
          jobs := jobs.push <| reportBool s!"base-case accumulator {j} of {tag}: AccOk"
            (padOk CS "vesta" vestaBase.sqrt? vestaSRS s j)
        | some (d, pi) =>
          let some w' := wraps.find? (fun w => w.vkDigest = d ∧ w.publicInputKey = pi)
            | IO.println s!"  ✗ {tag} slot {j}: its wrap {d.take 10}… is not in the file"
              allOk := false
              continue
          let some (d2, pi2) := w'.step
            | IO.println s!"  ✗ {tag} slot {j}: its wrap wrapped no step"
              allOk := false
              continue
          let some s' := steps.find? (fun s => s.vkDigest = d2 ∧ s.publicInputKey = pi2)
            | IO.println s!"  ✗ {tag} slot {j}: its predecessor step {d2.take 10}… is not in \
                the file"
              allOk := false
              continue
          jobs := jobs.push <| reportBool s!"carry step→step into accumulator {j} of {tag}"
            (carriesInto CS "vesta" vestaBase.sqrt? vestaSRS vestaKeys memo s' s j)
  unless jobs.size > 0 do throw (IO.userError "no linked pairs to run")
  let oks ← runPool nJobs jobs
  unless allOk && oks.all id do throw (IO.userError "check-halves FAILED")
  IO.println s!"✓ {jobs.size} run(s): every table satisfies its system, every bit reads 1, \
    kimchiVerify accepts every proof, every accumulator is carried"
