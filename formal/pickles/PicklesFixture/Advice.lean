import Pickles.StepMain
import Pickles.WrapMain
import PicklesFixture.Constants
import PicklesFixture.Proofs

/-!
# The main circuits' advice, read off the proof cache

The values a run of the step circuit (`Pickles.StepMainAdvice`) and of the wrap circuit
(`Pickles.WrapMainAdvice`) allocates, for a proof in the cache: the step circuit's from the step
proof's public input, its rule's witness, the tag's wrap key and, per slot, the wrap proof the
slot verified and the step proof that wrap proof wrapped; the wrap circuit's from the step proof
it wraps, its public input and the wrap proofs that step proof verified.

A base-case slot verifies a dummy proof, which the cache does not hold: each entry carries the
cells its circuit allocated for such a slot instead. A wrap slot the rule lacks takes the
padding the tag dump records (`PicklesFixture.WrapPadding`).

## Main definitions

* `PicklesFixture.StepPrev`, `PicklesFixture.stepPrevsOf`: a step proof's slots, off the cache.
* `PicklesFixture.WrapPrev`, `PicklesFixture.wrapPrevsOf`: the wrap circuit's slots.
* `PicklesFixture.stepMainAdviceOf`: the step circuit's advice at a cached step proof.
* `PicklesFixture.wrapMainAdviceOf`: the wrap circuit's advice at the step proof it wraps.
-/

namespace PicklesFixture

open Lean Snarky Snarky.Kimchi Kimchi Kimchi.Fixture Bulletproof CompElliptic.Fields.Pasta
open scoped Kimchi

/-- The step circuit's advice, inert: a compile reads none of it. -/
def inertStepAdvice {n w : ℕ} {ws : Fin n → ℕ} {ncw k ks : ℕ} {ncs : Fin n → ℕ} {inVal : Type} :
    Pickles.StepMainAdvice n w ws ncw ncs k ks inVal :=
  ⟨AsProver.throw "advice", AsProver.throw "advice", AsProver.throw "advice",
    AsProver.throw "advice", AsProver.throw "advice", AsProver.throw "advice"⟩

/-- The wrap circuit's advice, inert: a compile reads none of it. -/
def inertWrapAdvice {mpv nc k ks wsum : ℕ} : Pickles.WrapMainAdvice mpv nc k ks wsum :=
  ⟨AsProver.throw "advice", AsProver.throw "advice", AsProver.throw "advice",
    AsProver.throw "advice", AsProver.throw "advice", AsProver.throw "advice",
    AsProver.throw "advice", AsProver.throw "advice"⟩

/-- A point as a checked cell value. -/
def checkedPt {F : Type} {a b : F} (C : Ipa.KimchiCurve) (P : C.Point) :
    CheckedPoint a b C.BaseField :=
  ⟨⟨P.x, P.y⟩⟩

/-- A proof's evaluations as allocated. -/
def allocEvalsOf {nc : ℕ} {f : Type} (e : Pickles.ChunkedEvals nc f) : Pickles.AllocEvals nc f :=
  { pub := e.pub, w := e.evals.w, coefficients := e.evals.coefficients, z := e.evals.z
    s := e.evals.s
    index := #v[e.evals.genericSelector, e.evals.poseidonSelector, e.evals.completeAddSelector,
      e.evals.mulSelector, e.evals.emulSelector, e.evals.endomulScalarSelector]
    ftEval1 := e.ftEval1 }

/-- An unfinalized proof as its entry is allocated. -/
def allocUnfinalizedOf {k : ℕ} {f bc sf : Type} (u : Pickles.UnfinalizedProof k f bc sf) :
    Pickles.AllocUnfinalized k f bc sf :=
  let dv := u.deferredValues
  { cip := dv.combinedInnerProduct, b := dv.b, zetaToSrsLength := dv.plonk.zetaToSrsLength
    zetaToDomainSize := dv.plonk.zetaToDomainSize, perm := dv.plonk.perm
    spongeDigest := u.spongeDigestBeforeEvaluations, beta := dv.plonk.beta.val
    gamma := dv.plonk.gamma.val, alpha := dv.plonk.alpha.val, zeta := dv.plonk.zeta.val
    xi := dv.xi.val, bulletproofChallenges := dv.bulletproofChallenges.map (·.val)
    shouldFinalize := u.shouldFinalize }

/-- The last `m` entries of `xs`, front-padded with `pad` when it has fewer: a proof carries its
accumulators in its last slots, padding in front. -/
def lastPadded {α : Type} (m : ℕ) (pad : α) (xs : Array α) : Except String (Vector α m) :=
  let all := Array.replicate (m - xs.size) pad ++ xs.extract (xs.size - m) xs.size
  if h : all.size = m then .ok ⟨all, h⟩ else .error s!"{xs.size} entries for {m} slots"

/-- A value off its cells, when there are as many as its type takes. -/
def ofCells (F : Type) {α v : Type} [CircuitType F α v] (cells : Array F) : Except String α :=
  if h : cells.size = CircuitType.size F α then .ok (CircuitType.fieldsToValue ⟨cells, h⟩)
  else .error s!"{cells.size} cells, not {CircuitType.size F α}"

/-- One of a step proof's slots: the wrap proof it verified there, with the step proof that
wrap proof wrapped, or a base case, with the cells the step circuit allocated for it. -/
inductive StepPrev where
  /-- A verified slot: the wrap proof and the step proof it wrapped. -/
  | proof (W : Cache.Entry CW) (S : Cache.Entry CS)
  /-- A base-case slot: the step circuit's cells for it. -/
  | baseCase (cells : Array Fp)

/-- The `n` slots of the cached step proof `S0`, its links resolved in `wraps` and `steps`. -/
def stepPrevsOf (n : ℕ) (wraps : Array (Cache.Entry CW)) (steps : Array (Cache.Entry CS))
    (S0 : Cache.Entry CS) : Except String (Vector StepPrev n) := do
  let find {C : Ipa.KimchiCurve} (es : Array (Cache.Entry C)) (link : String × String) :
      Except String (Cache.Entry C) :=
    match es.find? fun e => e.vkDigest = link.1 ∧ e.publicInputKey = link.2 with
    | some e => .ok e
    | none => .error s!"no cached proof at {link.1.take 12}…/{link.2.take 12}…"
  let prevs ← (S0.prevs.zip S0.baseCases).mapM fun
    | (some link, none) => do
      let W ← find wraps link
      let some l := W.step | throw "a wrap proof without its step proof"
      return StepPrev.proof W (← find steps l)
    | (none, some cells) => return StepPrev.baseCase cells
    | _ => throw "a slot neither verified nor a base case"
  if h : prevs.size = n then return ⟨prevs, h⟩
  else throw s!"{prevs.size} slots, not {n}"

/-- One slot's witness, at the slot's width `w`: the wrap proof `W` the slot verified (its
commitments, opening and old accumulators' points), the wrap statement it carries (the deferred
values of the step proof it verified, and its branch data), and that step proof `S` (its
evaluations at `ncs` chunks and its old accumulators' challenges, zero in a slot it lacks, whose
mask bit leaves it unread). -/
def slotValOf (w ncs : ℕ) (W : Cache.Entry CW) (S : Cache.Entry CS) :
    Except String (Pickles.SlotVal w 1 ncs 15 Pickles.StepIPARounds) := do
  let (_, cpW) ← W.checkedAt 15 1
  let (_, cpS) ← S.checkedAt Pickles.StepIPARounds ncs
  let split (z : CW.ScalarField) : Type2 (SplitField Fp Bool) :=
    let t := (Pasta.Shifted.shiftType2 255 z).val
    ⟨⟨((t / 2 : ℕ) : Fp), decide (t % 2 = 1)⟩⟩
  let iv ← ivpProofOf CW split cpW
  let st ← wrapStatementOf toStep Pickles.StepIPARounds W.publicInput
  let dv := st.proofState.deferredValues
  let cell (P : AffinePoint Fp) : Pickles.PallasPt Fp := ⟨P⟩
  let sgs ← lastPadded w (cell ⟨dummyWrapSgPt.x, dummyWrapSgPt.y⟩)
    (cpW.olds.map fun a => cell ⟨a.sg.x, a.sg.y⟩)
  let chals ← lastPadded w (Vector.replicate Pickles.StepIPARounds 0) (cpS.olds.map (·.u))
  return { wComm := iv.wComm.map (·.map cell), zComm := iv.zComm.map cell
           tComm := Vector.ofFn fun i => #v[cell (iv.tComm[i.val]'(by omega))]
           lr := iv.opening.lr.map fun (l, r) => (cell l, cell r)
           z1 := iv.opening.z1, z2 := iv.opening.z2, delta := cell iv.opening.delta
           sg := cell iv.opening.sg
           cip := dv.combinedInnerProduct.val, b := dv.b.val
           zetaToSrsLength := dv.plonk.zetaToSrsLength.val
           zetaToDomainSize := dv.plonk.zetaToDomainSize.val, perm := dv.plonk.perm.val
           spongeDigest := st.proofState.spongeDigestBeforeEvaluations
           beta := dv.plonk.beta.val, gamma := dv.plonk.gamma.val, alpha := dv.plonk.alpha.val
           zeta := dv.plonk.zeta.val, xi := dv.xi.val
           bulletproofChallenges := dv.bulletproofChallenges.map (·.val)
           branch := ⟨dv.branchData.proofsVerifiedMask, dv.branchData.domainLog2⟩
           evals := allocEvalsOf (← chunkedEvalsOf CS cpS)
           prevChallenges := chals, prevSgs := sgs }

/-- A function every value of which may fail, as a function or the first failure. -/
def finSequence {ε : Type} : {n : ℕ} → {β : Fin n → Type} → ((i : Fin n) → Except ε (β i)) →
    Except ε ((i : Fin n) → β i)
  | 0, _, _ => .ok fun i => i.elim0
  | _ + 1, _, f => do
    let h ← f 0
    let t ← finSequence fun i => f i.succ
    return Fin.cons h t

/-- Cached step advice at the supplied slot widths, chunk counts and input encoding. -/
def stepAdviceOf {n : ℕ} (w : ℕ) (ws ncs : Fin n → ℕ)
    {inVal inVar : Type} [CircuitType Fp inVal inVar]
    (wrapKey : Kimchi.Verifier.KimchiVK CW 1) (S0 : Cache.Entry CS) (prevs : Vector StepPrev n) :
    Except String (Pickles.StepMainAdvice n w ws 1 ncs 15 Pickles.StepIPARounds inVal) := do
  let inputSize := CircuitType.size Fp inVal
  let some rule := S0.rule | throw "the step proof's cache entry has no rule witness"
  let input : Vector Fp inputSize ←
    if h : rule.input.size = inputSize then pure ⟨rule.input, h⟩
    else throw s!"the rule witness has {rule.input.size} input cells, not {inputSize}"
  let slots ← finSequence fun i =>
    match prevs[i] with
    | .proof W S =>
      slotValOf (ws i) (ncs i) W S
    | .baseCase cells => (ofCells Fp cells).mapError (s!"slot {i}'s base case: " ++ ·)
  let st ← stepStatementOf id 15 w S0.publicInput
  if hnw : n ≤ w then
    let unfs : Vector (Pickles.UnfVal 15) n := Vector.ofFn fun i =>
      allocUnfinalizedOf (st.proofState.unfinalizedProofs[w - n + i.val]'(by omega))
    let msgs : Vector Fp n :=
      Vector.ofFn fun i => st.messagesForNextWrapProof[w - n + i.val]'(by omega)
    let msgsPad : Vector Fp (w - n) :=
      Vector.ofFn fun i => st.messagesForNextWrapProof[i.val]'(by omega)
    return { publicInput := pure (CircuitType.fieldsToValue input)
             vk := pure (wrapKey.comms.map (checkedPt CW))
             slots := pure slots, unfinalized := pure unfs, msgs := pure msgs
             msgsPad := pure msgsPad }
  else throw s!"{n} slots in a tag of width {w}"

/-- The step circuit's advice from a dumped configuration and a cached proof. -/
def stepMainAdviceOf {n : ℕ} (w : ℕ) (k : StepMainConsts n) (inputSize : ℕ)
    (wrapKey : Kimchi.Verifier.KimchiVK CW 1) (S0 : Cache.Entry CS) (prevs : Vector StepPrev n) :
    Except String (Pickles.StepMainAdvice n w
      (Pickles.SlotSource.widths w fun i => k.slots[i].source) 1 k.chunks 15 Pickles.StepIPARounds
      (Vector Fp inputSize)) :=
  stepAdviceOf w (Pickles.SlotSource.widths w fun i => k.slots[i].source) k.chunks
    wrapKey S0 prevs

/-- A shifted register split as `(half, parity)`, as one register `2·half + parity`. -/
def joinSplit {f : Type} [Field f] (x : Type2 (SplitField f Bool)) : Type2 f :=
  ⟨2 * x.val.sDiv2 + (if x.val.sOdd then 1 else 0)⟩

/-- An allocated entry with its split registers joined. -/
def AllocUnfinalized.joinSplits {k : ℕ} {f bc : Type} [Field f]
    (u : Pickles.AllocUnfinalized k f bc (Type2 (SplitField f Bool))) :
    Pickles.AllocUnfinalized k f bc (Type2 f) :=
  { u with cip := joinSplit u.cip, b := joinSplit u.b
           zetaToSrsLength := joinSplit u.zetaToSrsLength
           zetaToDomainSize := joinSplit u.zetaToDomainSize, perm := joinSplit u.perm }

/-- What the wrap prover allocates for a slot its rule lacks, as a tag dump records it: the
step proof's accumulator, the evaluations and the wrap domain's index. -/
structure WrapPadding where
  /-- The step proof's accumulator. -/
  stepAcc : Pickles.VestaPt Fq
  /-- The evaluations. -/
  evals : Pickles.AllocEvals 1 Fq
  /-- The wrap domain's index. -/
  domain : Fq

/-- A tag dump's wrap padding, off its `wrapMain`. -/
def WrapPadding.ofJson (wrapMain : Json) : Except String WrapPadding := do
  let p ← wrapMain.getObjVal? "padding"
  let P ← Bulletproof.Fixture.parsePt XhatWrapCurve (← p.getObjVal? "stepAcc")
  return { stepAcc := ⟨⟨P.x, P.y⟩⟩
           evals := ← ofCells Fq
             (← FixtureKit.parseArrOf FixtureKit.parseZMod (← p.getObjVal? "evals"))
           domain := ((← (← p.getObjVal? "domain").getNat?) : Fq) }

/-- One of the wrap circuit's slots: the wrap proof the step proof verified there, a base case,
with the cells the wrap circuit allocated for its evaluations and its wrap domain's index, or a
slot the rule lacks. -/
inductive WrapPrev where
  /-- A verified slot: the wrap proof. -/
  | proof (W : Cache.Entry CW)
  /-- A base-case slot: its evaluations' cells and its wrap domain's index. -/
  | baseCase (evals : Array Fq) (domain : Fq)
  /-- A slot the rule lacks. -/
  | padding

/-- The `mpv` slots of the wrap circuit at a step proof with slots `prevs`, wrapped by `W0`: the
rule's slots last, a base case's evaluations off `W0` and its wrap domain its branch's pin in
`pins`, one per wrap slot. -/
def wrapPrevsOf {n : ℕ} (mpv : ℕ) (pins : List (Option ℕ)) (W0 : Cache.Entry CW)
    (prevs : Vector StepPrev n) : Except String (Vector WrapPrev mpv) := do
  let own ← (List.finRange n).mapM fun i => match prevs[i] with
    | .proof W _ => pure (WrapPrev.proof W)
    | .baseCase _ => do
      let some (some evals) := W0.baseCases[i.val]?
        | throw s!"slot {i}: the wrap proof has no base case's cells"
      let some (some d) := pins[mpv - n + i.val]?
        | throw s!"slot {i}: a base case with no pinned wrap domain"
      pure (WrapPrev.baseCase evals (d : Fq))
  let all := List.replicate (mpv - n) WrapPrev.padding ++ own
  if h : all.length = mpv then return ⟨all.toArray, by simpa⟩
  else throw s!"{n} slots in a wrap circuit of {mpv}"

/-- The wrap circuit's advice for a tag with `mpv` slots of stack heights `slotWidths`, at the
step proof `S0` it wraps at `ncStep` chunks, of branch `b`: the step proof's statement in the
wrap field (its split registers joined), its old accumulators' points, its opening and
commitments, and per slot off `prevs` its evaluations, its old accumulators' challenges at the
slot's height and its wrap domain's index; padding from `pad` and the challenges `dummy`. -/
def wrapMainAdviceOf {mpv : ℕ} (ncStep b : ℕ)
    (slotWidths : Vector (Fin (Pickles.MaxProofsVerified + 1)) mpv) (pad : WrapPadding)
    (dummy : Vector Fq 15) (S0 : Cache.Entry CS) (prevs : Vector WrapPrev mpv) :
    Except String (Pickles.WrapMainAdvice mpv ncStep 15 Pickles.StepIPARounds
      (slotWidths.map Fin.val).sum) := do
  let (_, cpS) ← S0.checkedAt Pickles.StepIPARounds ncStep
  let st ← stepStatementOf toWrap 15 mpv S0.publicInput
  let cell (P : AffinePoint Fq) : Pickles.VestaPt Fq := ⟨P⟩
  let stepAccs ← lastPadded mpv pad.stepAcc (cpS.olds.map fun a => cell ⟨a.sg.x, a.sg.y⟩)
  let slots ← finSequence fun j =>
    show Except String (Pickles.AllocEvals 1 Fq × Vector (Vector Fq 15) slotWidths[j].val × Fq)
    from match prevs[j] with
    | .proof W => do
      let (vkW, cpW) ← W.checkedAt 15 1
      let l := vkW.domainLog2
      unless l ∈ Pickles.wrapDomainLog2s do throw s!"slot {j}: wrap domain 2^{l} is no wrap domain"
      return (allocEvalsOf (← chunkedEvalsOf CW cpW),
        ← lastPadded slotWidths[j].val (Vector.replicate 15 0) (cpW.olds.map (·.u)),
        ((Pickles.wrapDomainLog2s.idxOf l : ℕ) : Fq))
    | .baseCase cells d => do
      return (← (ofCells Fq cells).mapError (s!"slot {j}'s base case: " ++ ·),
        Vector.replicate _ dummy, d)
    | .padding => return (pad.evals, Vector.replicate _ dummy, pad.domain)
  let chalStacks := (List.finRange mpv).flatMap fun j => (slots j).2.1.toList
  let oldChallenges : Vector (Vector Fq 15) (slotWidths.map Fin.val).sum ←
    if h : chalStacks.length = (slotWidths.map Fin.val).sum then pure ⟨chalStacks.toArray, by simpa⟩
    else throw s!"{chalStacks.length} challenge stacks, not {(slotWidths.map Fin.val).sum}"
  let iv ← ivpProofOf CS (fun z => toWrap (Pasta.Shifted.shiftType1 255 z)) cpS
  return { whichBranch := pure (b : Fq)
           proofState := pure
             ⟨st.proofState.unfinalizedProofs.map fun u =>
               AllocUnfinalized.joinSplits (allocUnfinalizedOf u),
              st.proofState.messagesForNextStepProof⟩
           stepAccs := pure stepAccs
           oldChallenges := pure oldChallenges
           evals := pure (Vector.ofFn fun j => (slots j).1)
           domainIndices := pure (Vector.ofFn fun j => (slots j).2.2)
           opening := pure (iv.opening.lr.map (fun (l, r) => (cell l, cell r)), iv.opening.z1,
             iv.opening.z2, cell iv.opening.delta, cell iv.opening.sg)
           messages := pure (iv.wComm.map (·.map cell), iv.zComm.map cell,
             Vector.ofFn fun i => Vector.ofFn fun c =>
               cell (iv.tComm[i.val * ncStep + c.val]'(by
                 have hi : i.val + 1 ≤ quotChunks := i.isLt
                 have hc := c.isLt
                 calc i.val * ncStep + c.val < i.val * ncStep + ncStep := by omega
                   _ = (i.val + 1) * ncStep := by ring
                   _ ≤ quotChunks * ncStep := Nat.mul_le_mul_right _ hi))) }

/-- The wrap circuit's public input, off a wrap proof's: its packed statement. -/
def wrapInputOf (W : Cache.Entry CW) :
    Except String (Pickles.StatementPacked 16 (Type1 Fq) Fq) :=
  let m := CircuitType.size Fq (Pickles.StatementPacked 16 (Type1 Fq) Fq)
  if h : W.publicInput.size = m then
    .ok (CircuitType.fieldsToValue (F := Fq) ⟨W.publicInput, h⟩)
  else .error s!"wrap public input: {W.publicInput.size} cells, not {m}"

end PicklesFixture
