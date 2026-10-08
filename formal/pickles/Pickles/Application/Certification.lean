import Pickles.Application.MatrixRun
import Pickles.Application.Handover

/-!
# A checked application is Pickles-correct

`PicklesCorrect C I` is the claim the checked compilation of an application establishes for
its family of indices `I`: every table an index accepts at a typed statement has an execution
of the circuit at that statement (`Realizes`), and the framework's four capstones hold for
every connection among executions (`FrameworkCorrect`). `checkedApplication_picklesCorrect`
proves it for a checked application's own indices, from the lifts of accepted tables.

The quantifier order is fixed. A consumer supplies accepted tables and recovers executions
with their public readings; connections are then quantified over those particular executions
(`StepWrapConnection`, `WrapStepConnection`, `WrapHandoverConnection`,
`StepHandoverConnection`), and the capstones' implications hold whenever they do. Nothing
here says that accepted tables are connected, and nothing identifies a recovered execution
with any prover's: a connection's hypotheses concern the recovered executions alone. The
records carrying data, a mask, are types; the others are propositions.

The four conclusion predicates spell out the capstones' conclusions, retaining their
whole-message grouping, the accumulator-failure alternative and the collision alternatives
outside it. `frameworkCorrect` proves each field by the capstone itself, so a capstone whose
conclusion changes fails here rather than drifting from its restatement. The application-state
projection is derived from the whole-message conclusion (`WrapHandoverConclusion.appState`),
not restated.

The fixture lanes that execute reconstructed applications decide the same connection
hypotheses on their own executions and apply the same capstones; they are evidence about those
executions. The theorems here are about every accepted table.

## Main definitions

- `Realizes`, `FrameworkCorrect`, `PicklesCorrect`: the claim.
- `StepWrapConclusion`, `WrapStepConclusion`, `StepHandoverConclusion`,
  `WrapHandoverConclusion`: the capstones' conclusions.
- The connection records and their links.

## Main results

- `checkedApplication_picklesCorrect`: a checked application's indices are Pickles-correct.
- `matrices_stepWrap`, `matrices_wrapStep`, `matrices_wrap_handover`, `matrices_step_handover`:
  each capstone from accepted tables, the executions recovered first.
- `WrapHandoverConclusion.appState`: the application-state projection.
-/

namespace Pickles.Application

open Snarky Snarky.Kimchi Bulletproof CompElliptic.Fields.Pasta Kimchi.Verifier
open scoped Kimchi

variable {D : Shape} {L : Layout D}

/-- Every accepted table has an execution at exactly the same public statement. -/
structure Realizes (C : Circuits D L) (I : ApplicationIndices D) : Prop where
  /-- Every accepted step table has a step execution at its statement. -/
  step : ∀ (b : D.Branch) (t : StepTable I b),
    ∃ r : StepRun C b, CircuitType.Reads r.V r.cells.out t.statement
  /-- Every accepted wrap table has a wrap execution at its statement. -/
  wrap : ∀ t : WrapTable I,
    ∃ r : WrapRun C, CircuitType.Reads r.V wrapStatement t.statement

/-- The complete conclusion of the existing step-wrap verification capstone. -/
def StepWrapConclusion {C : Circuits D L} {b : D.Branch}
    (e : StepWrapLink C b) (i : D.Slot b) : Prop :=
  let σ := C.setup.wrapSrs.σ
  let vk := (C.wiring.source b i).wrapKey.cvk
  let r := e.run i (e.mask i)
  r.Produces C.setup.dummy
    ⟨(e.proof i).opening.sg, wireChallenges σ vk (e.proof i) (e.proofPublicInput i)⟩ ∧
  r.Consumes C.setup.dummy (e.proof i).olds.toList ∧
  (SgOk σ vk (e.proof i) (e.proofPublicInput i) →
    kimchiVerify IpaPallas.curve σ vk (e.proof i) (e.proofPublicInput i) = true)

variable {producerD middleD consumerD : Shape}
  {producerL : Layout producerD} {middleL : Layout middleD} {consumerL : Layout consumerD}

/-- The complete conclusion of the existing wrap-step verification capstone. -/
def WrapStepConclusion
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {pb : producerD.Branch} {cb : consumerD.Branch} {i : consumerD.Slot cb}
    (e : WrapStepLink producer consumer pb cb i) : Prop :=
  let σ := producer.setup.stepSrs.σ
  let vk := producer.wiring.backend.stepKeys[pb].cvk
  e.run.Produces producer.wiring.backend.wrapKey.cvk producer.setup.dummy
    ⟨e.proof.opening.sg, wireChallenges σ vk e.proof e.proofPublicInput⟩ ∧
  e.run.Consumes producer.wiring.backend.wrapKey.cvk producer.setup.dummy e.proof.olds.toList ∧
  (∀ (j : Nat)
      (hj : j < SlotSource.widths consumerD.width (consumer.wiring.sources cb) i),
    e.mask[j] = decide (producerD.width - producerD.slots pb ≤ j)) ∧
  (SgOk σ vk e.proof e.proofPublicInput →
    kimchiVerify IpaVesta.curve σ vk e.proof e.proofPublicInput = true)

/-- Whole messages and recursive verification, in the step-proof direction. -/
def StepHandoverConclusion
    {producer : Circuits producerD producerL} {middle : Circuits middleD middleL}
    {consumer : Circuits consumerD consumerL}
    {pb : producerD.Branch} {mb : middleD.Branch} {cb : consumerD.Branch}
    {mi : middleD.Slot mb} {ci : consumerD.Slot cb}
    (e : StepProofHandover producer middle consumer pb mb cb mi ci) : Prop :=
  let σ := producer.setup.stepSrs.σ
  let vk := producer.wiring.backend.stepKeys[pb].cvk
  let nextVk := middle.wiring.backend.stepKeys[mb].cvk
  kimchiVerify IpaVesta.curve σ nextVk e.consumer.proof e.consumer.proofPublicInput = true →
  (e.sentStep = e.receivedStep ∧
   e.sentWrap = e.receivedWrap ∧
   (kimchiVerify IpaVesta.curve σ vk e.producer.proof e.producer.proofPublicInput = true ∨
    AccumulatorFailure σ nextVk e.consumer.proof e.consumer.proofPublicInput)) ∨
  e.producer.run.WrapCollision e.consumer.run producer.setup.dummy ∨
  e.producer.run.StepCollision e.consumer.run middle.wiring.backend.wrapKey.cvk

/-- Whole messages and recursive verification, in the wrap-proof direction. -/
def WrapHandoverConclusion
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {pb : producerD.Branch} {cb : consumerD.Branch}
    {pi : producerD.Slot pb} {ci : consumerD.Slot cb}
    (e : WrapProofHandover producer consumer pb cb pi ci) : Prop :=
  let σ := producer.setup.wrapSrs.σ
  let vk := (producer.wiring.source pb pi).wrapKey.cvk
  let nextVk := (consumer.wiring.source cb ci).wrapKey.cvk
  let r := e.producer.run pi (e.producer.mask pi)
  let r' := e.consumer.run ci (e.consumer.mask ci)
  kimchiVerify IpaPallas.curve σ nextVk
    (e.consumer.proof ci) (e.consumer.proofPublicInput ci) = true →
  (e.sentStep = e.receivedStep ∧
   e.sentWrap = e.receivedWrap ∧
   (kimchiVerify IpaPallas.curve σ vk
      (e.producer.proof pi) (e.producer.proofPublicInput pi) = true ∨
    AccumulatorFailure σ nextVk
      (e.consumer.proof ci) (e.consumer.proofPublicInput ci))) ∨
  r.WrapCollision r' producer.setup.dummy ∨ r.StepCollision r' nextVk

/-- The four capstones, over every connection ending in `C`. -/
structure FrameworkCorrect (C : Circuits D L) : Prop where
  /-- The step-wrap capstone. -/
  stepWrap : ∀ (b : D.Branch) (e : StepWrapLink C b) (i : D.Slot b),
    StepWrapAssumptions C b i →
    CircuitType.Reads e.step.V (e.step.cells.prevs i).mustVerify true →
    e.step.KeyBound i → StepWrapConclusion e i
  /-- The wrap-step capstone. -/
  wrapStep : ∀ {producerD : Shape} {producerL : Layout producerD}
    (producer : Circuits producerD producerL)
    (pb : producerD.Branch) (cb : D.Branch) (i : D.Slot cb)
    (e : WrapStepLink producer C pb cb i),
    WrapStepAssumptions producer pb → WrapStepConclusion e
  /-- The step-proof handover. -/
  stepHandover : ∀ {producerD middleD : Shape}
    {producerL : Layout producerD} {middleL : Layout middleD}
    (producer : Circuits producerD producerL) (middle : Circuits middleD middleL)
    (pb : producerD.Branch) (mb : middleD.Branch) (cb : D.Branch)
    (mi : middleD.Slot mb) (ci : D.Slot cb)
    (e : StepProofHandover producer middle C pb mb cb mi ci),
    WrapStepAssumptions producer pb → WrapStepAssumptions middle mb →
    StepHandoverConclusion e
  /-- The wrap-proof handover. -/
  wrapHandover : ∀ {producerD : Shape} {producerL : Layout producerD}
    (producer : Circuits producerD producerL) (pb : producerD.Branch) (cb : D.Branch)
    (pi : producerD.Slot pb) (ci : D.Slot cb)
    (e : WrapProofHandover producer C pb cb pi ci),
    StepWrapAssumptions producer pb pi → StepWrapAssumptions C cb ci →
    WrapHandoverConclusion e

theorem frameworkCorrect (C : Circuits D L) : FrameworkCorrect C where
  stepWrap _ e i h hm hk := e.verifies_proof i h hm hk
  wrapStep _ _ _ _ e h := e.verifies_proof h
  stepHandover _ _ _ _ _ _ _ e hp hc := e.handover_or_collision hp hc
  wrapHandover _ _ _ _ _ e hp hc := e.handover_or_collision hp hc

/-- Tables realized as executions, together with the framework's capstone guarantees. -/
def PicklesCorrect (C : Circuits D L) (I : ApplicationIndices D) : Prop :=
  Realizes C I ∧ FrameworkCorrect C

/-- A checked application realizes its indices: the two lifts. -/
theorem CheckedApplication.realizes {C : Circuits D L} (checked : CheckedApplication C) :
    Realizes C checked.indices :=
  ⟨checked.lift_step, checked.lift_wrap⟩

/-- **A checked application's indices are Pickles-correct.** Every table they accept at a typed
statement has an execution at that statement, and the framework's four capstones hold for every
connection among executions. -/
theorem checkedApplication_picklesCorrect (C : Circuits D L) (checked : CheckedApplication C) :
    PicklesCorrect C checked.indices :=
  ⟨checked.realizes, frameworkCorrect C⟩

/-- A connection between a fixed step execution and a fixed wrap execution. -/
structure StepWrapConnection {C : Circuits D L} {b : D.Branch}
    (step : StepRun C b) (wrap : WrapRun C) : Prop where
  /-- The wrap execution selects the branch. -/
  branch : wrap.cells.1.whichBranch.val wrap.V = (b : Fq)
  /-- The step statement reads as the one the wrap verifier holds. -/
  publicInput : CircuitType.Reads step.V step.cells.out
    (StepStatement.ofWrap wrap.V wrap.cells.2.statement)

/-- The connection as the capstone's link. -/
def StepWrapConnection.link {C : Circuits D L} {b : D.Branch}
    {step : StepRun C b} {wrap : WrapRun C} (h : StepWrapConnection step wrap) :
    StepWrapLink C b :=
  ⟨step, wrap, h.branch, h.publicInput⟩

/-- A connection between a fixed producer wrap execution and a fixed consumer step execution,
with the mask it reads. -/
structure WrapStepConnection
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {pb : producerD.Branch} {cb : consumerD.Branch}
    (wrap : WrapRun producer) (step : StepRun consumer cb) (i : consumerD.Slot cb) where
  /-- The consumer slot resolves to the producer's exported interface. -/
  sourceFor : SourceFor producer consumer cb i
  /-- The wrap execution selects the producer's branch. -/
  branch : wrap.cells.1.whichBranch.val wrap.V = (pb : Fq)
  /-- The consumer's slot must verify. -/
  mustVerify : CircuitType.Reads step.V (step.cells.prevs i).mustVerify true
  /-- The source proof's old-accumulator mask. -/
  mask : Vector Bool (SlotSource.widths consumerD.width (consumer.wiring.sources cb) i)
  /-- The consumer's mask cells read the mask. -/
  maskReads : CircuitType.Reads step.V (step.inp i).proofMask mask
  /-- The consumer reconstructs the producer's wrap public input. -/
  publicInput : CircuitType.Reads wrap.V wrapStatement
    ((step.inp i).packedAt producer.wiring.backend.wrapKey.cvk step.V mask)

/-- The connection as the capstone's link. -/
def WrapStepConnection.link
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {pb : producerD.Branch} {cb : consumerD.Branch}
    {wrap : WrapRun producer} {step : StepRun consumer cb} {i : consumerD.Slot cb}
    (h : WrapStepConnection (pb := pb) wrap step i) : WrapStepLink producer consumer pb cb i :=
  ⟨h.sourceFor, wrap, step, h.branch, h.mustVerify, h.mask, h.maskReads, h.publicInput⟩

/-- The wrap-proof handover's hypotheses, over four fixed executions. -/
structure WrapHandoverConnection
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {pb : producerD.Branch} {cb : consumerD.Branch}
    (ps : StepRun producer pb) (pw : WrapRun producer)
    (cs : StepRun consumer cb) (cw : WrapRun consumer)
    (pi : producerD.Slot pb) (ci : consumerD.Slot cb) : Prop where
  /-- The producer's step and wrap executions are connected. -/
  producerPair : StepWrapConnection ps pw
  /-- The consumer's step and wrap executions are connected. -/
  consumerPair : StepWrapConnection cs cw
  /-- The consumer slot resolves to the producer's exported interface. -/
  sourceFor : SourceFor producer consumer cb ci
  /-- The producer's slot must verify. -/
  mustVerifyProducer : CircuitType.Reads ps.V (ps.cells.prevs pi).mustVerify true
  /-- The producer's slot key cells read the source key. -/
  keyProducer : ps.KeyBound pi
  /-- The consumer's slot must verify. -/
  mustVerifyConsumer : CircuitType.Reads cs.V (cs.cells.prevs ci).mustVerify true
  /-- The consumer's slot key cells read the source key. -/
  keyConsumer : cs.KeyBound ci
  /-- The producer's wrap statement is the one the consumer reconstructs at its slot. -/
  middlePublicInput : CircuitType.Reads pw.V wrapStatement
    ((cs.inp ci).packedAt producer.wiring.backend.wrapKey.cvk
      cs.V (consumerPair.link.mask ci))

/-- The connection as the capstone's handover record. -/
def WrapHandoverConnection.handover
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {pb : producerD.Branch} {cb : consumerD.Branch}
    {ps : StepRun producer pb} {pw : WrapRun producer}
    {cs : StepRun consumer cb} {cw : WrapRun consumer}
    {pi : producerD.Slot pb} {ci : consumerD.Slot cb}
    (h : WrapHandoverConnection ps pw cs cw pi ci) :
    WrapProofHandover producer consumer pb cb pi ci :=
  ⟨h.producerPair.link, h.consumerPair.link, h.sourceFor,
    h.mustVerifyProducer, h.keyProducer, h.mustVerifyConsumer, h.keyConsumer,
    h.middlePublicInput⟩

/-- The step-proof handover's hypotheses, over four fixed executions. -/
structure StepHandoverConnection
    {producer : Circuits producerD producerL} {middle : Circuits middleD middleL}
    {consumer : Circuits consumerD consumerL}
    {pb : producerD.Branch} {mb : middleD.Branch} {cb : consumerD.Branch}
    (pw : WrapRun producer) (ms : StepRun middle mb)
    (mw : WrapRun middle) (cs : StepRun consumer cb)
    (mi : middleD.Slot mb) (ci : consumerD.Slot cb) where
  /-- The producer's wrap execution and the middle step execution are connected. -/
  producerPair : WrapStepConnection (pb := pb) pw ms mi
  /-- The middle wrap execution and the consumer's step execution are connected. -/
  consumerPair : WrapStepConnection (pb := mb) mw cs ci
  /-- The middle step statement is the one its wrap verifier holds. -/
  middlePublicInput : CircuitType.Reads ms.V ms.cells.out
    (StepStatement.ofWrap mw.V mw.cells.2.statement)

/-- The connection as the capstone's handover record. -/
def StepHandoverConnection.handover
    {producer : Circuits producerD producerL} {middle : Circuits middleD middleL}
    {consumer : Circuits consumerD consumerL}
    {pb : producerD.Branch} {mb : middleD.Branch} {cb : consumerD.Branch}
    {pw : WrapRun producer} {ms : StepRun middle mb}
    {mw : WrapRun middle} {cs : StepRun consumer cb}
    {mi : middleD.Slot mb} {ci : consumerD.Slot cb}
    (h : StepHandoverConnection (pb := pb) pw ms mw cs mi ci) :
    StepProofHandover producer middle consumer pb mb cb mi ci :=
  ⟨h.producerPair.link, h.consumerPair.link, h.middlePublicInput⟩

/-- The step-wrap capstone, after recovering the two executions. -/
theorem matrices_stepWrap
    {C : Circuits D L} {I : ApplicationIndices D} (hC : PicklesCorrect C I)
    (b : D.Branch) (step : StepTable I b) (wrap : WrapTable I) :
    ∃ (s : StepRun C b) (w : WrapRun C),
      CircuitType.Reads s.V s.cells.out step.statement ∧
      CircuitType.Reads w.V wrapStatement wrap.statement ∧
      ∀ (h : StepWrapConnection s w) (i : D.Slot b),
        StepWrapAssumptions C b i →
        CircuitType.Reads s.V (s.cells.prevs i).mustVerify true →
        s.KeyBound i → StepWrapConclusion h.link i := by
  obtain ⟨s, hs⟩ := hC.1.step b step
  obtain ⟨w, hw⟩ := hC.1.wrap wrap
  exact ⟨s, w, hs, hw, fun h i ha hm hk ↦ hC.2.stepWrap b h.link i ha hm hk⟩

/-- The wrap-step capstone, after recovering the two executions. -/
theorem matrices_wrapStep
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {producerIndices : ApplicationIndices producerD}
    {consumerIndices : ApplicationIndices consumerD}
    (hp : PicklesCorrect producer producerIndices)
    (hc : PicklesCorrect consumer consumerIndices)
    (pb : producerD.Branch) (cb : consumerD.Branch) (i : consumerD.Slot cb)
    (wrap : WrapTable producerIndices) (step : StepTable consumerIndices cb) :
    ∃ (w : WrapRun producer) (s : StepRun consumer cb),
      CircuitType.Reads w.V wrapStatement wrap.statement ∧
      CircuitType.Reads s.V s.cells.out step.statement ∧
      ∀ h : WrapStepConnection (pb := pb) w s i,
        WrapStepAssumptions producer pb → WrapStepConclusion h.link := by
  obtain ⟨w, hw⟩ := hp.1.wrap wrap
  obtain ⟨s, hs⟩ := hc.1.step cb step
  exact ⟨w, s, hw, hs, fun h ha ↦ hc.2.wrapStep producer pb cb i h.link ha⟩

/-- The wrap-proof handover, after recovering the four executions: connections concern those
executions. -/
theorem matrices_wrap_handover
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {producerIndices : ApplicationIndices producerD}
    {consumerIndices : ApplicationIndices consumerD}
    (hp : PicklesCorrect producer producerIndices)
    (hc : PicklesCorrect consumer consumerIndices)
    (pb : producerD.Branch) (cb : consumerD.Branch)
    (pi : producerD.Slot pb) (ci : consumerD.Slot cb)
    (producerStep : StepTable producerIndices pb) (producerWrap : WrapTable producerIndices)
    (consumerStep : StepTable consumerIndices cb) (consumerWrap : WrapTable consumerIndices) :
    ∃ (ps : StepRun producer pb) (pw : WrapRun producer)
      (cs : StepRun consumer cb) (cw : WrapRun consumer),
      CircuitType.Reads ps.V ps.cells.out producerStep.statement ∧
      CircuitType.Reads pw.V wrapStatement producerWrap.statement ∧
      CircuitType.Reads cs.V cs.cells.out consumerStep.statement ∧
      CircuitType.Reads cw.V wrapStatement consumerWrap.statement ∧
      ∀ h : WrapHandoverConnection ps pw cs cw pi ci,
        StepWrapAssumptions producer pb pi → StepWrapAssumptions consumer cb ci →
        WrapHandoverConclusion h.handover := by
  obtain ⟨ps, hps⟩ := hp.1.step pb producerStep
  obtain ⟨pw, hpw⟩ := hp.1.wrap producerWrap
  obtain ⟨cs, hcs⟩ := hc.1.step cb consumerStep
  obtain ⟨cw, hcw⟩ := hc.1.wrap consumerWrap
  exact ⟨ps, pw, cs, cw, hps, hpw, hcs, hcw, fun h ha hb ↦
    hc.2.wrapHandover producer pb cb pi ci h.handover ha hb⟩

/-- The step-proof handover, after recovering the four executions across three applications. -/
theorem matrices_step_handover
    {producer : Circuits producerD producerL} {middle : Circuits middleD middleL}
    {consumer : Circuits consumerD consumerL}
    {producerIndices : ApplicationIndices producerD}
    {middleIndices : ApplicationIndices middleD}
    {consumerIndices : ApplicationIndices consumerD}
    (hp : PicklesCorrect producer producerIndices)
    (hm : PicklesCorrect middle middleIndices)
    (hc : PicklesCorrect consumer consumerIndices)
    (pb : producerD.Branch) (mb : middleD.Branch) (cb : consumerD.Branch)
    (mi : middleD.Slot mb) (ci : consumerD.Slot cb)
    (producerWrap : WrapTable producerIndices) (middleStep : StepTable middleIndices mb)
    (middleWrap : WrapTable middleIndices) (consumerStep : StepTable consumerIndices cb) :
    ∃ (pw : WrapRun producer) (ms : StepRun middle mb)
      (mw : WrapRun middle) (cs : StepRun consumer cb),
      CircuitType.Reads pw.V wrapStatement producerWrap.statement ∧
      CircuitType.Reads ms.V ms.cells.out middleStep.statement ∧
      CircuitType.Reads mw.V wrapStatement middleWrap.statement ∧
      CircuitType.Reads cs.V cs.cells.out consumerStep.statement ∧
      ∀ h : StepHandoverConnection (pb := pb) pw ms mw cs mi ci,
        WrapStepAssumptions producer pb → WrapStepAssumptions middle mb →
        StepHandoverConclusion h.handover := by
  obtain ⟨pw, hpw⟩ := hp.1.wrap producerWrap
  obtain ⟨ms, hms⟩ := hm.1.step mb middleStep
  obtain ⟨mw, hmw⟩ := hm.1.wrap middleWrap
  obtain ⟨cs, hcs⟩ := hc.1.step cb consumerStep
  exact ⟨pw, ms, mw, cs, hpw, hms, hmw, hcs, fun h ha hb ↦
    hc.2.stepHandover producer middle pb mb cb mi ci h.handover ha hb⟩

/-- Application-state threading is a projection of the whole-message conclusion. -/
theorem WrapHandoverConclusion.appState
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {pb : producerD.Branch} {cb : consumerD.Branch}
    {pi : producerD.Slot pb} {ci : consumerD.Slot cb}
    {e : WrapProofHandover producer consumer pb cb pi ci} (h : WrapHandoverConclusion e) :
    let nextVk := (consumer.wiring.source cb ci).wrapKey.cvk
    let r := e.producer.run pi (e.producer.mask pi)
    let r' := e.consumer.run ci (e.consumer.mask ci)
    kimchiVerify IpaPallas.curve producer.setup.wrapSrs.σ nextVk
      (e.consumer.proof ci) (e.consumer.proofPublicInput ci) = true →
    (e.producer.step.cells.messagesForNextStepProof.appState.map
        (·.val e.producer.step.V) =
      ((e.consumer.step.cells.prevs ci).appState.map
        (·.val e.consumer.step.V)).cast e.sourceFor.prevSize) ∨
    r.WrapCollision r' producer.setup.dummy ∨ r.StepCollision r' nextVk := by
  intro nextVk r r' hAccept
  rcases h hAccept with hm | hf
  · left
    apply Vector.toList_inj.mp
    simpa only [Vector.toList_map, Vector.toList_cast] using
      congrArg (fun m ↦ m.appState) hm.1
  · exact Or.inr hf

end Pickles.Application
