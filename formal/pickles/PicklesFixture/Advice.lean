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

A slot with no proof (a base case) and a wrap slot beyond the step proof's own carry the
compile's padding values, which the cache does not hold; the builders refuse them.

## Main definitions

* `PicklesFixture.stepMainAdviceOf`: the step circuit's advice at a cached step proof.
* `PicklesFixture.wrapMainAdviceOf`: the wrap circuit's advice at the step proof it wraps.
-/

namespace PicklesFixture

open Lean Snarky Snarky.Kimchi Kimchi Kimchi.Fixture Bulletproof CompElliptic.Fields.Pasta
open scoped Kimchi

/-- A cache entry's records checked at `k` rounds, at the chunk count an SRS of `2 ^ k` points
gives its domain. -/
def checkedEntry (C : Ipa.KimchiCurve) (k : ℕ) (e : Cache.Entry C) :
    Except String ((nc : ℕ) × Kimchi.Verifier.KimchiVK C nc × Kimchi.Verifier.KimchiProof C nc k) :=
  let nc := Kimchi.Verifier.chunkCount k e.vk.domainLog2
  match e.vk.check nc, e.proof.check nc k with
  | some cvk, some cp => .ok ⟨nc, cvk, cp⟩
  | _, _ => .error "the cache entry's records fail the wire check"

/-- `checkedEntry` at a given chunk count. -/
def checkedEntryAt (C : Ipa.KimchiCurve) (k nc : ℕ) (e : Cache.Entry C) :
    Except String (Kimchi.Verifier.KimchiVK C nc × Kimchi.Verifier.KimchiProof C nc k) := do
  let ⟨nc', cvk, cp⟩ ← checkedEntry C k e
  if h : nc' = nc then return (h ▸ cvk, h ▸ cp)
  else throw s!"the entry runs at {nc'} chunks, not {nc}"

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

/-- One slot's witness, at the slot's width `w`: the wrap proof `W` the slot verified (its
commitments, opening and old accumulators' points), the wrap statement it carries (the deferred
values of the step proof it verified, and its branch data), and that step proof `S` (its
evaluations at `ncs` chunks and its old accumulators' challenges, zero in a slot it lacks, whose
mask bit leaves it unread). -/
def slotValOf (w ncs : ℕ) (W : Cache.Entry CW) (S : Cache.Entry CS) :
    Except String (Pickles.SlotVal w 1 ncs 15 Pickles.StepIPARounds) := do
  let (_, cpW) ← checkedEntryAt CW 15 1 W
  let (_, cpS) ← checkedEntryAt CS Pickles.StepIPARounds ncs S
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

/-- The step circuit's advice at the step proof `S0` of a tag of width `w` with the step
constants `k`: the rule's witness as its input, the tag's wrap key `wrapKey`, per slot the
wrap proof it verified and the step proof that wrap proof wrapped (`prevs`), and the
unfinalized entries and messages off `S0`'s statement, the padding ones in front. -/
def stepMainAdviceOf {n ncs : ℕ} (w : ℕ) (k : StepMainConsts n ncs) (inputSize : ℕ)
    (wrapKey : Kimchi.Verifier.KimchiVK CW 1) (S0 : Cache.Entry CS)
    (prevs : Fin n → Option (Cache.Entry CW × Cache.Entry CS)) :
    Except String (Pickles.StepMainAdvice n w
      (Pickles.SlotSource.widths w fun i => k.slots[i].source) 1 ncs 15 Pickles.StepIPARounds
      (Vector Fp inputSize)) := do
  let some rule := S0.rule | throw "the step proof's cache entry has no rule witness"
  let input : Vector Fp inputSize ←
    if h : rule.input.size = inputSize then pure ⟨rule.input, h⟩
    else throw s!"the rule witness has {rule.input.size} input cells, not {inputSize}"
  let slots ← finSequence fun i => do
    let some (W, S) := prevs i | throw s!"slot {i} is a base case, whose padding is not cached"
    slotValOf (Pickles.SlotSource.widths w (fun i => k.slots[i].source) i) ncs W S
  let st ← stepStatementOf id 15 w S0.publicInput
  if hnw : n ≤ w then
    let unfs : Vector (Pickles.UnfVal 15) n := Vector.ofFn fun i =>
      allocUnfinalizedOf (st.proofState.unfinalizedProofs[w - n + i.val]'(by omega))
    let msgs : Vector Fp n :=
      Vector.ofFn fun i => st.messagesForNextWrapProof[w - n + i.val]'(by omega)
    let msgsPad : Vector Fp (w - n) :=
      Vector.ofFn fun i => st.messagesForNextWrapProof[i.val]'(by omega)
    return { publicInput := pure input, vk := pure (wrapKey.comms.map (checkedPt CW))
             slots := pure slots, unfinalized := pure unfs, msgs := pure msgs
             msgsPad := pure msgsPad }
  else throw s!"{n} slots in a tag of width {w}"

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

/-- The wrap circuit's advice for a tag with `mpv` slots of stack heights `slotWidths`, at the
step proof `S0` it wraps at `ncStep` chunks, of branch `b`: the step proof's statement in the
wrap field (its split registers joined), its old accumulators' points, its opening and
commitments, and per slot the wrap proof `S0` verified there (`prevs`): its evaluations, its old
accumulators' challenges at the slot's height and its wrap domain's index. -/
def wrapMainAdviceOf {mpv : ℕ} (ncStep b : ℕ)
    (slotWidths : Vector (Fin (Pickles.MaxProofsVerified + 1)) mpv) (S0 : Cache.Entry CS)
    (prevs : Fin mpv → Option (Cache.Entry CW)) :
    Except String (Pickles.WrapMainAdvice mpv ncStep 15 Pickles.StepIPARounds
      (slotWidths.map Fin.val).sum) := do
  let (_, cpS) ← checkedEntryAt CS Pickles.StepIPARounds ncStep S0
  let st ← stepStatementOf toWrap 15 mpv S0.publicInput
  let cell (P : AffinePoint Fq) : Pickles.VestaPt Fq := ⟨P⟩
  let accs ← lastPadded mpv none (cpS.olds.map fun a => some (cell ⟨a.sg.x, a.sg.y⟩))
  let stepAccs ← finSequence fun j => match accs[j] with
    | some P => .ok P
    | none => .error s!"slot {j} pads the step proof's accumulators, which the cache lacks"
  let wraps ← finSequence fun j => do
    let some W := prevs j | throw s!"slot {j} is padding, which the cache lacks"
    checkedEntryAt CW 15 1 W
  let evals ← finSequence fun j => do return allocEvalsOf (← chunkedEvalsOf CW (wraps j).2)
  let chalStacks ← (List.finRange mpv).flatMapM fun j => do
    let chals ← lastPadded slotWidths[j].val (Vector.replicate 15 0) ((wraps j).2.olds.map (·.u))
    pure chals.toList
  let oldChallenges : Vector (Vector Fq 15) (slotWidths.map Fin.val).sum ←
    if h : chalStacks.length = (slotWidths.map Fin.val).sum then pure ⟨chalStacks.toArray, by simpa⟩
    else throw s!"{chalStacks.length} challenge stacks, not {(slotWidths.map Fin.val).sum}"
  let domainIndices ← finSequence fun j => do
    let l := (wraps j).1.domainLog2
    unless l ∈ Pickles.wrapDomainLog2s do throw s!"slot {j}: wrap domain 2^{l} is no wrap domain"
    return ((Pickles.wrapDomainLog2s.idxOf l : ℕ) : Fq)
  let iv ← ivpProofOf CS (fun z => toWrap (Pasta.Shifted.shiftType1 255 z)) cpS
  return { whichBranch := pure (b : Fq)
           proofState := pure
             ⟨st.proofState.unfinalizedProofs.map fun u =>
               AllocUnfinalized.joinSplits (allocUnfinalizedOf u),
              st.proofState.messagesForNextStepProof⟩
           stepAccs := pure (Vector.ofFn stepAccs)
           oldChallenges := pure oldChallenges
           evals := pure (Vector.ofFn evals)
           domainIndices := pure (Vector.ofFn domainIndices)
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
