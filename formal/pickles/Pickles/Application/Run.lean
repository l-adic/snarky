import Pickles.Application.Circuit
import Pickles.Handover

/-!
# Satisfying application executions

Step and wrap executions retain their valuation, advice and satisfaction of the compiled
application circuit. Connections identify the selected source interface and public statements;
the complete messages remain conclusions of the handover results.
-/

namespace Pickles.Application

open Snarky Snarky.Kimchi Bulletproof CompElliptic.Fields.Pasta

variable {D : Shape} {L : Layout D}

/-- The wrap SRS with the protocol round count explicit. -/
def Setup.wrapSrs (S : Setup) : Srs IpaPallas.curve where
  σ := ⟨WrapIPARounds, S.wrapRounds ▸ S.wrap.σ.g, S.wrap.σ.h, S.wrap.σ.U⟩
  rounds_small := by change MaxProofsVerified * WrapIPARounds < 2 ^ 128; decide
  rounds_pos := by change 0 < WrapIPARounds; decide
  h_ne := S.wrap.h_ne

/-- The step SRS with the protocol round count explicit. -/
def Setup.stepSrs (S : Setup) : Srs IpaVesta.curve where
  σ := ⟨StepIPARounds, S.stepRounds ▸ S.step.σ.g, S.step.σ.h, S.step.σ.U⟩
  rounds_small := by change MaxProofsVerified * StepIPARounds < 2 ^ 128; decide
  rounds_pos := by change 0 < StepIPARounds; decide
  h_ne := S.step.h_ne

/-- A satisfying execution of a selected branch's step circuit. -/
structure StepRun (C : Circuits D L) (b : D.Branch) where
  /-- The circuit's valuation. -/
  V : Valuation Fp
  /-- The execution's witness advice. -/
  advice : C.StepAdvice b
  /-- Every compiled constraint holds at the valuation. -/
  holds : ∀ con ∈ (C.stepBuilt b advice).constraints, ConstraintHolds.Holds V con

/-- A satisfying execution of an application's shared wrap circuit. -/
structure WrapRun (C : Circuits D L) where
  /-- The circuit's valuation. -/
  V : Valuation Fq
  /-- The execution's witness advice. -/
  advice : C.WrapAdvice
  /-- Every compiled constraint holds at the valuation. -/
  holds : ∀ con ∈ (C.wrapBuilt advice).constraints, ConstraintHolds.Holds V con

/-- The selected step circuit's retained cells. -/
def StepRun.cells {C : Circuits D L} {b : D.Branch} (r : StepRun C b) : C.StepCells b :=
  (C.stepBuilt b r.advice).result.1.2

/-- The shared wrap circuit's retained cells. -/
def WrapRun.cells {C : Circuits D L} (r : WrapRun C) : C.WrapCells :=
  (C.wrapBuilt r.advice).result.1.2

/-- The wrap circuit's public input cells. -/
def wrapStatement :=
  inputVar (F := Fq) (a := StatementPacked StepIPARounds (Type1 Fq) Fq)

/-- The predecessor-verification cells at one branch slot. -/
def StepRun.inp {C : Circuits D L} {b : D.Branch} (r : StepRun C b) (i : D.Slot b) :=
  slotInput (C.source_bound b i) (constPt C.setup.dummySg)
    (r.cells.prevs i) (r.cells.slots i) r.cells.unfs[i] r.cells.msgs[i]

/-- The slot's key cells read as the statically selected source key. -/
def StepRun.KeyBound {C : Circuits D L} {b : D.Branch} (r : StepRun C b) (i : D.Slot b) :
    Prop :=
  KeyReads IpaPallas.curve r.V ((C.wiring.sources b i).keyCells r.cells.vk.points)
    (C.wiring.source b i).wrapKey.cvk

/-- A step execution and the wrap execution receiving its public statement. -/
structure StepWrapLink (C : Circuits D L) (b : D.Branch) where
  /-- The selected branch's step execution. -/
  step : StepRun C b
  /-- The receiving wrap execution. -/
  wrap : WrapRun C
  /-- The wrap execution selects this branch. -/
  branch : wrap.cells.1.whichBranch.val wrap.V = (b : Fq)
  /-- The step statement reads as the one held by the wrap verifier. -/
  publicInput : CircuitType.Reads step.V step.cells.out
    (StepStatement.ofWrap wrap.V wrap.cells.2.statement)

/-- The existing handover record at the selected slot and mask. -/
def StepWrapLink.run {C : Circuits D L} {b : D.Branch} (e : StepWrapLink C b)
    (i : D.Slot b) (ms : Vector Bool (SlotSource.widths D.width (C.wiring.sources b) i)) :
    StepWrapRun (D.slots b) D.width (SlotSource.widths D.width (C.wiring.sources b))
      (D.prevSize b) D.schema.size
      (C.wiring.sourceChunks b) WrapIPARounds StepIPARounds D.branches
      C.wiring.backend.stepChunks L.wrapWidths where
  Vg := e.step.V
  Vs := e.wrap.V
  stepOut := e.step.cells
  hws := C.source_bound b
  dummySg := C.setup.dummySg
  i := i
  hn := D.slots_le_width b
  hw := L.width_le
  ms := ms
  wrapStmt := wrapStatement
  wrapFinalizeOut := e.wrap.cells.1
  wrapVerifyOut := e.wrap.cells.2

variable {producerD consumerD : Shape}
  {producerL : Layout producerD} {consumerL : Layout consumerD}

/-- A consumer slot resolves to the producer's exported interface at the same protocol setup. -/
structure SourceFor
    (producer : Circuits producerD producerL)
    (consumer : Circuits consumerD consumerL)
    (branch : consumerD.Branch)
    (slot : consumerD.Slot branch) : Prop where
  /-- Both applications share their SRSs and padding constants. -/
  setup : producer.setup = consumer.setup
  /-- The selected source has the producer's layout, key, domains and tables. -/
  source : (⟨_, consumer.wiring.source branch slot⟩ : (I : LayoutInterface) × CircuitInterface I) =
    ⟨producerL.export, producer.wiring.export⟩

/-- The selected source's width is the producer's width. -/
theorem SourceFor.width
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {branch : consumerD.Branch} {slot : consumerD.Slot branch}
    (h : SourceFor producer consumer branch slot) :
    SlotSource.widths consumerD.width (consumer.wiring.sources branch) slot = producerD.width := by
  have he := congrArg (fun x : (I : LayoutInterface) × CircuitInterface I => x.1.width.val)
    h.source
  rw [SlotSource.widths, consumer.wiring.source_width]
  cases hs : consumerD.source branch slot <;>
    simpa [Shape.sourceLayout, Shape.slotWidth, hs, Layout.export] using he

/-- The selected source's chunk count is the producer's chunk count. -/
theorem SourceFor.chunks
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {branch : consumerD.Branch} {slot : consumerD.Slot branch}
    (h : SourceFor producer consumer branch slot) :
    consumer.wiring.sourceChunks branch slot = producer.wiring.backend.stepChunks :=
  congrArg (fun x : (I : LayoutInterface) × CircuitInterface I => x.2.stepChunks) h.source

/-- The source's candidate step domains are the producer's branch domains. -/
theorem SourceFor.domains
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {branch : consumerD.Branch} {slot : consumerD.Slot branch}
    (h : SourceFor producer consumer branch slot) :
    (consumer.wiring.sources branch slot).domains consumer.wiring.backend.stepDomains.list =
      producer.wiring.backend.stepDomains.list := by
  rw [consumer.wiring.source_domains]
  exact congrArg (fun x : (I : LayoutInterface) × CircuitInterface I =>
    x.2.stepDomains.list) h.source

/-- The source's wrap key is the producer's exported key. -/
theorem SourceFor.wrapKey
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {branch : consumerD.Branch} {slot : consumerD.Slot branch}
    (h : SourceFor producer consumer branch slot) :
    (consumer.wiring.source branch slot).wrapKey = producer.wiring.backend.wrapKey :=
  congrArg (fun x : (I : LayoutInterface) × CircuitInterface I => x.2.wrapKey) h.source

/-- The selected source's statement has the producer's schema size. -/
theorem SourceFor.prevSize
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {branch : consumerD.Branch} {slot : consumerD.Slot branch}
    (h : SourceFor producer consumer branch slot) :
    consumerD.prevSize branch slot = producerD.schema.size := by
  have he := congrArg (fun x : (I : LayoutInterface) × CircuitInterface I =>
    x.1.schema.size) h.source
  cases hs : consumerD.source branch slot <;>
    simpa [Shape.sourceLayout, Shape.prevSize, hs, Layout.export] using he

/-- A producer wrap execution and the consumer step slot verifying its wrap proof. -/
structure WrapStepLink
    (producer : Circuits producerD producerL) (consumer : Circuits consumerD consumerL)
    (producerBranch : producerD.Branch) (consumerBranch : consumerD.Branch)
    (slot : consumerD.Slot consumerBranch) where
  /-- The consumer slot resolves to the producer's exported interface. -/
  sourceFor : SourceFor producer consumer consumerBranch slot
  /-- The producer's wrap execution. -/
  wrap : WrapRun producer
  /-- The consumer's step execution. -/
  step : StepRun consumer consumerBranch
  /-- The wrap execution selects the producer's branch. -/
  branch : wrap.cells.1.whichBranch.val wrap.V = (producerBranch : Fq)
  /-- The consumer's selected slot must verify. -/
  mustVerify : CircuitType.Reads step.V (step.cells.prevs slot).mustVerify true
  /-- The source proof's old-accumulator mask. -/
  mask :
    Vector Bool (SlotSource.widths consumerD.width (consumer.wiring.sources consumerBranch) slot)
  /-- The consumer's mask cells read this mask. -/
  maskReads : CircuitType.Reads step.V (step.inp slot).proofMask mask
  /-- The consumer reconstructs the producer's wrap public input. -/
  publicInput : CircuitType.Reads wrap.V wrapStatement
    ((step.inp slot).packedAt producer.wiring.backend.wrapKey.cvk step.V mask)

/-- The existing handover record for the connected application executions. -/
def WrapStepLink.run
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {producerBranch : producerD.Branch} {consumerBranch : consumerD.Branch}
    {slot : consumerD.Slot consumerBranch}
    (e : WrapStepLink producer consumer producerBranch consumerBranch slot) :
    WrapStepRun producerD.branches producerD.width producer.wiring.backend.stepChunks
      WrapIPARounds StepIPARounds
      (consumerD.slots consumerBranch) consumerD.width
      (SlotSource.widths consumerD.width (consumer.wiring.sources consumerBranch))
      (consumerD.prevSize consumerBranch) (consumer.wiring.sourceChunks consumerBranch)
      consumerD.schema.size producerL.wrapWidths where
  Vw := e.wrap.V
  Vs := e.step.V
  wrapStmt := wrapStatement
  wrapFinalizeOut := e.wrap.cells.1
  wrapVerifyOut := e.wrap.cells.2
  stepOut := e.step.cells
  hn := consumerD.slots_le_width consumerBranch
  hws := consumer.source_bound consumerBranch
  dummySg := constPt consumer.setup.dummySg
  i := slot
  hwi := e.sourceFor.width
  ms := e.mask

/-- The slot's old-accumulator mask decoded from its cells. -/
def StepWrapLink.mask {C : Circuits D L} {b : D.Branch} (e : StepWrapLink C b)
    (i : D.Slot b) : Vector Bool (SlotSource.widths D.width (C.wiring.sources b) i) :=
  CircuitType.readVal e.step.V (e.step.inp i).proofMask

/-- The wrap proof reconstructed from the connected group and scalar cells. -/
def StepWrapLink.proof {C : Circuits D L} {b : D.Branch} (e : StepWrapLink C b)
    (i : D.Slot b) : Kimchi.Verifier.KimchiProof IpaPallas.curve 1 WrapIPARounds :=
  let r := e.run i (e.mask i)
  let sl := e.wrap.cells.1.slots[r.jf]
  IvpProof.read (stepSide e.step.V) r.inp.proof
    (sl.evals.evals.map fun v => v.map (·.val e.wrap.V))
    (.carried (sl.evals.pub.map fun v => v.map (·.val e.wrap.V)))
    (sl.evals.ftEval1.val e.wrap.V)
    (StepWrap.consumedAccumulators e.step.V e.wrap.V r.inp C.setup.dummy
      e.wrap.cells.1 r.jf).toArray

/-- The reconstructed wrap proof's public input at the source key. -/
def StepWrapLink.proofPublicInput {C : Circuits D L} {b : D.Branch}
    (e : StepWrapLink C b) (i : D.Slot b) : Array Fq :=
  (e.step.inp i).publicInputAt (C.wiring.source b i).wrapKey.cvk e.step.V (e.mask i)

/-- The step proof reconstructed from the connected group and scalar cells. -/
def WrapStepLink.proof
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {producerBranch : producerD.Branch} {consumerBranch : consumerD.Branch}
    {slot : consumerD.Slot consumerBranch}
    (e : WrapStepLink producer consumer producerBranch consumerBranch slot) :
    Kimchi.Verifier.KimchiProof IpaVesta.curve producer.wiring.backend.stepChunks StepIPARounds :=
  let inp : VerifyOneInput (consumerD.prevSize consumerBranch slot) StepIPARounds WrapIPARounds
      1 producer.wiring.backend.stepChunks
      (SlotSource.widths consumerD.width (consumer.wiring.sources consumerBranch) slot) :=
    e.sourceFor.chunks ▸ e.run.inp
  let cells := e.wrap.cells.2.cells
  let pr : IvpProof StepIPARounds producer.wiring.backend.stepChunks
      (FVar Fq) (Type1 (FVar Fq)) :=
    ⟨cells.wComm, cells.zComm, cells.tComm, cells.opening⟩
  IvpProof.read (wrapSide e.wrap.V) pr
    (inp.evals.evals.map fun v => v.map (·.val e.step.V))
    (.carried (inp.evals.pub.map fun v => v.map (·.val e.step.V)))
    (inp.evals.ftEval1.val e.step.V)
    (WrapStep.consumedAccumulators e.wrap.V e.step.V e.wrap.cells.1
      e.run.inp.prevChallenges e.sourceFor.width e.mask).toArray

/-- The reconstructed step proof's public input at the selected branch key. -/
def WrapStepLink.proofPublicInput
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {producerBranch : producerD.Branch} {consumerBranch : consumerD.Branch}
    {slot : consumerD.Slot consumerBranch}
    (e : WrapStepLink producer consumer producerBranch consumerBranch slot) : Array Fp :=
  wrapPublicInput producer.setup.stepSrs.σ producer.wiring.backend.stepKeys[producerBranch].cvk
    e.wrap.V e.wrap.cells.2.statement

end Pickles.Application
