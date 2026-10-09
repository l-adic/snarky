import Pickles.Application.MatrixRun

/-!
# Connections and proof readings of accepted matrices

The readers use the fixed valuation of a table and the handles retained by the canonical
compilation. They require no chosen source execution. Connections therefore describe the
supplied matrices before lifting: branch selections, source slots, public-statement ties,
verification requests, masks and key bindings. Whole-message equality is a conclusion of
handover, not a connection premise.

`matrixStepWrapRun` and `matrixWrapStepRun` assemble observation contexts, not satisfying
executions. The proof readers combine the group and scalar cells just as the native links
do. The handover conclusions retain the original accumulator-failure and collision
alternatives. The matrix handover theorems establish them after lifting.
-/

namespace Pickles.Application

open Snarky Snarky.Kimchi Bulletproof CompElliptic.Fields.Pasta Kimchi.Verifier
open scoped Kimchi

variable {D : Shape} {L : Layout D}
variable {PD MD CD : Shape} {PL : Layout PD} {ML : Layout MD} {CL : Layout CD}
variable {I : ApplicationIndices D} {PI : ApplicationIndices PD}
  {MI : ApplicationIndices MD} {CI : ApplicationIndices CD}

/-- The slot input retained by the canonical step compilation. -/
def matrixInp (C : Circuits D L) (b : D.Branch) (i : D.Slot b) :=
  let cells := (stepCompilation C b).result.1.2
  slotInput (C.source_bound b i) (constPt C.setup.dummySg)
    (cells.prevs i) (cells.slots i) cells.unfs[i] cells.msgs[i]

/-- The proof mask read from a step matrix. -/
noncomputable def matrixMask (C : Circuits D L) (I : ApplicationIndices D) (b : D.Branch)
    (s : StepTable I b) (i : D.Slot b) :
    Vector Bool (SlotSource.widths D.width (C.wiring.sources b) i) :=
  CircuitType.readVal (stepValuation C I b s) (matrixInp C b i).proofMask

-- Input conditions on fixed readers of the two tables, before constructing any run.

/-- A wrap matrix selects the branch and carries the step matrix’s public statement. -/
def MatrixStepWrap (C : Circuits D L) (I : ApplicationIndices D) (b : D.Branch)
    (s : StepTable I b) (w : WrapTable I) : Prop :=
  (wrapCompilation C).result.1.2.1.whichBranch.val (wrapValuation C I w) = (b : Fq) ∧
  StepStatement.ofWrap (wrapValuation C I w) (wrapCompilation C).result.1.2.2.statement =
    s.statement

/-- A producer wrap matrix is passed to a consumer step slot, with its source and mask. -/
structure MatrixWrapStep (P : Circuits PD PL) (C : Circuits CD CL)
    (PI : ApplicationIndices PD) (CI : ApplicationIndices CD)
    (pb : PD.Branch) (cb : CD.Branch) (i : CD.Slot cb)
    (w : WrapTable PI) (s : StepTable CI cb) where
  /-- The consumer slot identifies the producer and its shared setup. -/
  sourceFor : SourceFor P C cb i
  /-- The producer wrap selects the stated branch. -/
  branch : (wrapCompilation P).result.1.2.1.whichBranch.val (wrapValuation P PI w) = (pb : Fq)
  /-- The consumer requests verification of this slot. -/
  mustVerify : CircuitType.Reads (stepValuation C CI cb s)
    ((stepCompilation C cb).result.1.2.prevs i).mustVerify true
  /-- The proof mask carried by the consumer slot. -/
  mask : Vector Bool (SlotSource.widths CD.width (C.wiring.sources cb) i)
  /-- The matrix reads the declared proof mask. -/
  maskReads : CircuitType.Reads (stepValuation C CI cb s) (matrixInp C cb i).proofMask mask
  /-- The producer’s public statement equals the consumer’s packed input. -/
  publicInput : w.statement =
    (matrixInp C cb i).packedAt P.wiring.backend.wrapKey.cvk (stepValuation C CI cb s) mask

/-- Two connected step/wrap pairs, with the intervening public statement and key bindings. -/
structure MatrixWrapHandover (P : Circuits PD PL) (C : Circuits CD CL)
    (PI : ApplicationIndices PD) (CI : ApplicationIndices CD)
    (pb : PD.Branch) (cb : CD.Branch) (pi : PD.Slot pb) (ci : CD.Slot cb)
    (ps : StepTable PI pb) (pw : WrapTable PI)
    (cs : StepTable CI cb) (cw : WrapTable CI) : Prop where
  /-- The producer pair is connected. -/
  producerPair : MatrixStepWrap P PI pb ps pw
  /-- The consumer pair is connected. -/
  consumerPair : MatrixStepWrap C CI cb cs cw
  /-- The consumer slot identifies the producer and its shared setup. -/
  sourceFor : SourceFor P C cb ci
  /-- The producer requests verification of its selected slot. -/
  mustVerifyProducer : CircuitType.Reads (stepValuation P PI pb ps)
    ((stepCompilation P pb).result.1.2.prevs pi).mustVerify true
  /-- The producer’s selected key cells read the source key. -/
  keyProducer : KeyReads IpaPallas.curve (stepValuation P PI pb ps)
    ((P.wiring.sources pb pi).keyCells (stepCompilation P pb).result.1.2.vk.points)
    (P.wiring.source pb pi).wrapKey.cvk
  /-- The consumer requests verification of its selected slot. -/
  mustVerifyConsumer : CircuitType.Reads (stepValuation C CI cb cs)
    ((stepCompilation C cb).result.1.2.prevs ci).mustVerify true
  /-- The consumer’s selected key cells read the source key. -/
  keyConsumer : KeyReads IpaPallas.curve (stepValuation C CI cb cs)
    ((C.wiring.sources cb ci).keyCells (stepCompilation C cb).result.1.2.vk.points)
    (C.wiring.source cb ci).wrapKey.cvk
  /-- The intervening public statement agrees across the two pairs. -/
  middlePublicInput : pw.statement = (matrixInp C cb ci).packedAt
    P.wiring.backend.wrapKey.cvk (stepValuation C CI cb cs) (matrixMask C CI cb cs ci)

/-- Two connected wrap/step pairs, joined at the middle step statement. -/
structure MatrixStepHandover (P : Circuits PD PL) (M : Circuits MD ML) (C : Circuits CD CL)
    (PI : ApplicationIndices PD) (MI : ApplicationIndices MD) (CI : ApplicationIndices CD)
    (pb : PD.Branch) (mb : MD.Branch) (cb : CD.Branch) (mi : MD.Slot mb) (ci : CD.Slot cb)
    (pw : WrapTable PI) (ms : StepTable MI mb) (mw : WrapTable MI) (cs : StepTable CI cb) where
  /-- The producer pair is connected. -/
  producerPair : MatrixWrapStep P M PI MI pb mb mi pw ms
  /-- The consumer pair is connected. -/
  consumerPair : MatrixWrapStep M C MI CI mb cb ci mw cs
  /-- The intervening public statement agrees across the two pairs. -/
  middlePublicInput :
    StepStatement.ofWrap (wrapValuation M MI mw) (wrapCompilation M).result.1.2.2.statement =
      ms.statement

/-- The capstone’s observation context read directly from a pair of matrices. -/
noncomputable def matrixStepWrapRun (C : Circuits D L) (I : ApplicationIndices D)
    (b : D.Branch) (s : StepTable I b) (w : WrapTable I) (i : D.Slot b)
    (ms : Vector Bool (SlotSource.widths D.width (C.wiring.sources b) i)) :
    StepWrapRun (D.slots b) D.width (SlotSource.widths D.width (C.wiring.sources b))
      (D.prevSize b) D.schema.size
      (C.wiring.sourceChunks b) WrapIPARounds StepIPARounds D.branches
      C.wiring.backend.stepChunks L.wrapWidths where
  Vg := (stepValuation C I b s)
  Vs := (wrapValuation C I w)
  stepOut := (stepCompilation C b).result.1.2
  hws := C.source_bound b
  dummySg := C.setup.dummySg
  i := i
  hn := D.slots_le_width b
  hw := L.width_le
  ms := ms
  wrapStmt := wrapStatement
  wrapFinalizeOut := (wrapCompilation C).result.1.2.1
  wrapVerifyOut := (wrapCompilation C).result.1.2.2

/-- The wrap proof read from the group cells in a step and the scalar cells in its wrap. -/
noncomputable def matrixWrapProof (C : Circuits D L) (I : ApplicationIndices D)
    (b : D.Branch) (s : StepTable I b) (w : WrapTable I) (i : D.Slot b) :
    Kimchi.Verifier.KimchiProof IpaPallas.curve 1 WrapIPARounds :=
  let r := matrixStepWrapRun C I b s w i (matrixMask C I b s i)
  let sl := (wrapCompilation C).result.1.2.1.slots[r.jf]
  IvpProof.read (stepSide (stepValuation C I b s)) r.inp.proof
    (sl.evals.evals.map fun v => v.map (·.val (wrapValuation C I w)))
    (.carried (sl.evals.pub.map fun v => v.map (·.val (wrapValuation C I w))))
    (sl.evals.ftEval1.val (wrapValuation C I w))
    (StepWrap.consumedAccumulators (stepValuation C I b s) (wrapValuation C I w) r.inp C.setup.dummy
      (wrapCompilation C).result.1.2.1 r.jf).toArray

/-- The public input accompanying the wrap proof read by a step slot. -/
noncomputable def matrixWrapPub (C : Circuits D L) (I : ApplicationIndices D)
    (b : D.Branch) (s : StepTable I b) (i : D.Slot b) : Array Fq :=
  (matrixInp C b i).publicInputAt (C.wiring.source b i).wrapKey.cvk
    (stepValuation C I b s) (matrixMask C I b s i)

/-- The observation context for a wrap matrix and its consuming step matrix. -/
noncomputable def matrixWrapStepRun (P : Circuits PD PL) (C : Circuits CD CL)
    (PI : ApplicationIndices PD) (CI : ApplicationIndices CD)
    (cb : CD.Branch) (i : CD.Slot cb)
    (w : WrapTable PI) (s : StepTable CI cb) (hs : SourceFor P C cb i)
    (ms : Vector Bool (SlotSource.widths CD.width (C.wiring.sources cb) i)) :
    WrapStepRun PD.branches PD.width P.wiring.backend.stepChunks WrapIPARounds StepIPARounds
      (CD.slots cb) CD.width (SlotSource.widths CD.width (C.wiring.sources cb))
      (CD.prevSize cb) (C.wiring.sourceChunks cb) CD.schema.size PL.wrapWidths where
  Vw := wrapValuation P PI w
  Vs := stepValuation C CI cb s
  wrapStmt := wrapStatement
  wrapFinalizeOut := (wrapCompilation P).result.1.2.1
  wrapVerifyOut := (wrapCompilation P).result.1.2.2
  stepOut := (stepCompilation C cb).result.1.2
  hn := CD.slots_le_width cb
  hws := C.source_bound cb
  dummySg := constPt C.setup.dummySg
  i := i
  hwi := hs.width
  ms := ms

/-- The step proof read from the group cells in a wrap and the scalar cells in its consumer. -/
noncomputable def matrixStepProof (P : Circuits PD PL) (C : Circuits CD CL)
    (PI : ApplicationIndices PD) (CI : ApplicationIndices CD)
    (cb : CD.Branch) (i : CD.Slot cb)
    (w : WrapTable PI) (s : StepTable CI cb) (hs : SourceFor P C cb i)
    (ms : Vector Bool (SlotSource.widths CD.width (C.wiring.sources cb) i)) :
    KimchiProof IpaVesta.curve P.wiring.backend.stepChunks StepIPARounds :=
  let r := matrixWrapStepRun P C PI CI cb i w s hs ms
  let inp : VerifyOneInput (CD.prevSize cb i) StepIPARounds WrapIPARounds 1
      P.wiring.backend.stepChunks (SlotSource.widths CD.width (C.wiring.sources cb) i) :=
    hs.chunks ▸ r.inp
  let cells := (wrapCompilation P).result.1.2.2.cells
  let pr : IvpProof StepIPARounds P.wiring.backend.stepChunks (FVar Fq) (Type1 (FVar Fq)) :=
    ⟨cells.wComm, cells.zComm, cells.tComm, cells.opening⟩
  IvpProof.read (wrapSide (wrapValuation P PI w)) pr
    (inp.evals.evals.map fun v => v.map (·.val (stepValuation C CI cb s)))
    (.carried (inp.evals.pub.map fun v => v.map (·.val (stepValuation C CI cb s))))
    (inp.evals.ftEval1.val (stepValuation C CI cb s))
    (WrapStep.consumedAccumulators (wrapValuation P PI w) (stepValuation C CI cb s)
      (wrapCompilation P).result.1.2.1 r.inp.prevChallenges hs.width ms).toArray

/-- The public input accompanying the step proof read by a wrap. -/
noncomputable def matrixStepPub (P : Circuits PD PL) (PI : ApplicationIndices PD)
    (pb : PD.Branch) (w : WrapTable PI) : Array Fp :=
  wrapPublicInput P.setup.stepSrs.σ P.wiring.backend.stepKeys[pb].cvk (wrapValuation P PI w)
    (wrapCompilation P).result.1.2.2.statement

/-- Whole messages and recursive verification for the proofs read from four matrices. -/
def WrapHandoverConclusion (P : Circuits PD PL) (C : Circuits CD CL)
    (PI : ApplicationIndices PD) (CI : ApplicationIndices CD)
    (pb : PD.Branch) (cb : CD.Branch) (pi : PD.Slot pb) (ci : CD.Slot cb)
    (ps : StepTable PI pb) (pw : WrapTable PI)
    (cs : StepTable CI cb) (cw : WrapTable CI) : Prop :=
  let σ := P.setup.wrapSrs.σ
  let vk := (P.wiring.source pb pi).wrapKey.cvk
  let nextVk := (C.wiring.source cb ci).wrapKey.cvk
  let r := matrixStepWrapRun P PI pb ps pw pi (matrixMask P PI pb ps pi)
  let r' := matrixStepWrapRun C CI cb cs cw ci (matrixMask C CI cb cs ci)
  kimchiVerify IpaPallas.curve σ nextVk
    (matrixWrapProof C CI cb cs cw ci) (matrixWrapPub C CI cb cs ci) = true →
  (readStepMessage (stepValuation P PI pb ps)
      (stepCompilation P pb).result.1.2.messagesForNextStepProof =
    rebuildStepMessage (stepValuation C CI cb cs) nextVk
      (matrixInp C cb ci) (matrixMask C CI cb cs ci) ∧
   readWrapMessage (wrapValuation P PI pw) P.setup.dummy
      ((wrapCompilation P).result.1.2.2.messagesForNextWrapProof
        (wrapCompilation P).result.1.2.1) =
    readWrapMessage (wrapValuation C CI cw) P.setup.dummy
      ((wrapCompilation C).result.1.2.1.messagesForNextWrapProof r'.jf) ∧
   (kimchiVerify IpaPallas.curve σ vk
      (matrixWrapProof P PI pb ps pw pi) (matrixWrapPub P PI pb ps pi) = true ∨
    AccumulatorFailure σ nextVk
      (matrixWrapProof C CI cb cs cw ci) (matrixWrapPub C CI cb cs ci))) ∨
  r.WrapCollision r' P.setup.dummy ∨ r.StepCollision r' nextVk

/-- The dual handover conclusion, on the proofs and messages read from four matrices. -/
def StepHandoverConclusion (P : Circuits PD PL) (M : Circuits MD ML) (C : Circuits CD CL)
    (PI : ApplicationIndices PD) (MI : ApplicationIndices MD) (CI : ApplicationIndices CD)
    (pb : PD.Branch) (mb : MD.Branch) (cb : CD.Branch) (mi : MD.Slot mb) (ci : CD.Slot cb)
    (pw : WrapTable PI) (ms : StepTable MI mb) (mw : WrapTable MI) (cs : StepTable CI cb)
    (h : MatrixStepHandover P M C PI MI CI pb mb cb mi ci pw ms mw cs) : Prop :=
  let σ := P.setup.stepSrs.σ
  let vk := P.wiring.backend.stepKeys[pb].cvk
  let nextVk := M.wiring.backend.stepKeys[mb].cvk
  let r := matrixWrapStepRun P M PI MI mb mi pw ms
    h.producerPair.sourceFor h.producerPair.mask
  let r' := matrixWrapStepRun M C MI CI cb ci mw cs
    h.consumerPair.sourceFor h.consumerPair.mask
  let earlier := matrixStepProof P M PI MI mb mi pw ms
    h.producerPair.sourceFor h.producerPair.mask
  let later := matrixStepProof M C MI CI cb ci mw cs
    h.consumerPair.sourceFor h.consumerPair.mask
  kimchiVerify IpaVesta.curve σ nextVk later (matrixStepPub M MI mb mw) = true →
  (readStepMessage (stepValuation M MI mb ms)
      (stepCompilation M mb).result.1.2.messagesForNextStepProof =
    rebuildStepMessage (stepValuation C CI cb cs) M.wiring.backend.wrapKey.cvk
      (matrixInp C cb ci) h.consumerPair.mask ∧
   readWrapMessage (wrapValuation P PI pw) P.setup.dummy
      ((wrapCompilation P).result.1.2.2.messagesForNextWrapProof
        (wrapCompilation P).result.1.2.1) =
    readWrapMessage (wrapValuation M MI mw) P.setup.dummy
      ((wrapCompilation M).result.1.2.1.messagesForNextWrapProof r.slotIndex) ∧
   (kimchiVerify IpaVesta.curve σ vk earlier (matrixStepPub P PI pb pw) = true ∨
    AccumulatorFailure σ nextVk later (matrixStepPub M MI mb mw))) ∨
  r.WrapCollision r' P.setup.dummy ∨ r.StepCollision r' M.wiring.backend.wrapKey.cvk

/-- The complete verification conclusion on a step/wrap pair’s matrix readings. -/
def StepWrapConclusion (C : Circuits D L) (I : ApplicationIndices D) (b : D.Branch)
    (s : StepTable I b) (w : WrapTable I) (i : D.Slot b) : Prop :=
  let σ := C.setup.wrapSrs.σ
  let vk := (C.wiring.source b i).wrapKey.cvk
  let r := matrixStepWrapRun C I b s w i (matrixMask C I b s i)
  let proof := matrixWrapProof C I b s w i
  let pub := matrixWrapPub C I b s i
  r.Produces C.setup.dummy ⟨proof.opening.sg, wireChallenges σ vk proof pub⟩ ∧
  r.Consumes C.setup.dummy proof.olds.toList ∧
  (SgOk σ vk proof pub → kimchiVerify IpaPallas.curve σ vk proof pub = true)

/-- The complete verification conclusion on a wrap/step pair’s matrix readings. -/
def WrapStepConclusion (P : Circuits PD PL) (C : Circuits CD CL)
    (PI : ApplicationIndices PD) (CI : ApplicationIndices CD)
    (pb : PD.Branch) (cb : CD.Branch) (i : CD.Slot cb)
    (w : WrapTable PI) (s : StepTable CI cb)
    (h : MatrixWrapStep P C PI CI pb cb i w s) : Prop :=
  let σ := P.setup.stepSrs.σ
  let vk := P.wiring.backend.stepKeys[pb].cvk
  let r := matrixWrapStepRun P C PI CI cb i w s h.sourceFor h.mask
  let proof := matrixStepProof P C PI CI cb i w s h.sourceFor h.mask
  let pub := matrixStepPub P PI pb w
  r.Produces P.wiring.backend.wrapKey.cvk P.setup.dummy
    ⟨proof.opening.sg, wireChallenges σ vk proof pub⟩ ∧
  r.Consumes P.wiring.backend.wrapKey.cvk P.setup.dummy proof.olds.toList ∧
  (∀ (j : Nat) (hj : j < SlotSource.widths CD.width (C.wiring.sources cb) i),
    h.mask[j] = decide (PD.width - PD.slots pb ≤ j)) ∧
  (SgOk σ vk proof pub → kimchiVerify IpaVesta.curve σ vk proof pub = true)

end Pickles.Application
