import Pickles.Application.Handover
import Snarky.Kimchi.Backend.CheckedCompile
import Kimchi.Columns

/-!
An elaboration draft, outside the library. The matrix-to-run contract is stated, not proved
from checked application compilation. All other proofs below use the existing capstones.
There are no new axioms, and no executable recovery of valuations is asserted.
-/

namespace Pickles.Application.CertificationDraft

set_option autoImplicit false

open Snarky Snarky.Kimchi Bulletproof CompElliptic.Fields.Pasta Kimchi.Verifier
open scoped Kimchi

variable {D : Shape} {L : Layout D}

abbrev StepPublic (D : Shape) := StepStatement (UnfVal WrapIPARounds) Fp D.width
abbrev WrapPublic := StatementPacked StepIPARounds (Type1 Fq) Fq

/-- One application's indices, with the prescribed public-statement sizes. -/
structure ApplicationIndices (D : Shape) where
  stepSize : D.Branch → Nat
  step : (b : D.Branch) → Kimchi.Index Fp (stepSize b)
  wrapSize : Nat
  wrap : Kimchi.Index Fq wrapSize
  stepPublicCount : ∀ b, (step b).publicCount = CircuitType.size Fp (StepPublic D)
  wrapPublicCount : wrap.publicCount = CircuitType.size Fq WrapPublic

private def stepAdvice (C : Circuits D L) (b : D.Branch) : C.StepAdvice b :=
  ⟨AsProver.throw "advice", AsProver.throw "advice", AsProver.throw "advice",
    AsProver.throw "advice", AsProver.throw "advice", AsProver.throw "advice"⟩

private def wrapAdvice (C : Circuits D L) : C.WrapAdvice :=
  ⟨AsProver.throw "advice", AsProver.throw "advice", AsProver.throw "advice",
    AsProver.throw "advice", AsProver.throw "advice", AsProver.throw "advice",
    AsProver.throw "advice", AsProver.throw "advice"⟩

private def stepCompilation (C : Circuits D L) (b : D.Branch) :=
  C.stepBuilt (fun _ ↦ 0) b (stepAdvice C b)

private def wrapCompilation (C : Circuits D L) :=
  C.wrapBuilt (fun _ ↦ 0) (wrapAdvice C)

/-- Proposed certificate type; the checking function is phase 1, not implemented here. -/
structure CheckedApplication (C : Circuits D L) where
  step : (b : D.Branch) → CheckedIndex
    (stepCompilation C b).constraints
    (compiledPublicVars (F := Fp) (a := Unit) (b := StepPublic D) (stepCompilation C b))
    (stepCompilation C b).nextVar C.wiring.backend.stepKeys[b].cvk.n
  wrap : CheckedIndex
    (wrapCompilation C).constraints
    (compiledPublicVars (F := Fq) (a := WrapPublic) (b := Unit) (wrapCompilation C))
    (wrapCompilation C).nextVar C.wiring.backend.wrapKey.cvk.n

/-- Public sizes follow from compilation; indices are not stored twice in the certificate. -/
def CheckedApplication.indices {C : Circuits D L} (checked : CheckedApplication C) :
    ApplicationIndices D where
  stepSize b := C.wiring.backend.stepKeys[b].cvk.n
  step b := (checked.step b).index
  wrapSize := C.wiring.backend.wrapKey.cvk.n
  wrap := checked.wrap.index
  stepPublicCount b := (checked.step b).publicCount_eq.trans (by
    simpa only [show CircuitType.size Fp Unit = 0 from rfl, Nat.zero_add] using
      length_compiledPublicVars_compileWith (a := Unit) (b := StepPublic D)
        (C.stepCircuit (fun _ ↦ 0) b (stepAdvice C b)))
  wrapPublicCount := checked.wrap.publicCount_eq.trans (by
    simpa only [show CircuitType.size Fq Unit = 0 from rfl, Nat.add_zero] using
      length_compiledPublicVars_compileWith (a := WrapPublic) (b := Unit)
        (C.wrapCircuit (fun _ ↦ 0) (wrapAdvice C)))

private def satisfies {F : Type} [Field F] [DecidableEq F] {n : Nat}
    (idx : Kimchi.Index F n) (pub : Fin idx.publicCount → F)
    (table : Fin n → Fin wCols → F) : Prop :=
  haveI : NeZero n := ⟨by have := idx.zk_three; have := idx.zk_le; omega⟩
  idx.Satisfies pub table

/-- A table accepted at a particular typed step statement. -/
structure StepTable (I : ApplicationIndices D) (b : D.Branch) where
  statement : StepPublic D
  table : Fin (I.stepSize b) → Fin wCols → Fp
  holds : satisfies (I.step b)
    (fun j ↦ (CircuitType.valueToFields statement)[Fin.cast (I.stepPublicCount b) j]) table

/-- A table accepted at a particular typed wrap statement. -/
structure WrapTable (I : ApplicationIndices D) where
  statement : WrapPublic
  table : Fin I.wrapSize → Fin wCols → Fq
  holds : satisfies I.wrap
    (fun j ↦ (CircuitType.valueToFields statement)[Fin.cast I.wrapPublicCount j]) table

/-- Every accepted matrix has a source run at exactly the same public statement. -/
structure Realizes (C : Circuits D L) (I : ApplicationIndices D) : Prop where
  step : ∀ (b : D.Branch) (t : StepTable I b),
    ∃ r : StepRun C b, CircuitType.Reads r.V r.cells.out t.statement
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

/-- The four existing capstones, universally quantified over connections ending in `C`. -/
structure FrameworkCorrect (C : Circuits D L) : Prop where
  stepWrap : ∀ (b : D.Branch) (e : StepWrapLink C b) (i : D.Slot b),
    StepWrapAssumptions C b i →
    CircuitType.Reads e.step.V (e.step.cells.prevs i).mustVerify true →
    e.step.KeyBound i → StepWrapConclusion e i
  wrapStep : ∀ {producerD : Shape} {producerL : Layout producerD}
    (producer : Circuits producerD producerL)
    (pb : producerD.Branch) (cb : D.Branch) (i : D.Slot cb)
    (e : WrapStepLink producer C pb cb i),
    WrapStepAssumptions producer pb → WrapStepConclusion e
  stepHandover : ∀ {producerD middleD : Shape}
    {producerL : Layout producerD} {middleL : Layout middleD}
    (producer : Circuits producerD producerL) (middle : Circuits middleD middleL)
    (pb : producerD.Branch) (mb : middleD.Branch) (cb : D.Branch)
    (mi : middleD.Slot mb) (ci : D.Slot cb)
    (e : StepProofHandover producer middle C pb mb cb mi ci),
    WrapStepAssumptions producer pb → WrapStepAssumptions middle mb →
    StepHandoverConclusion e
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

/-- Matrix-to-run realization together with the native framework's capstone guarantees. -/
def PicklesCorrect (C : Circuits D L) (I : ApplicationIndices D) : Prop :=
  Realizes C I ∧ FrameworkCorrect C

/-- Complete statement of the unproved phase-1/2 lifting obligation. -/
def CheckedApplicationLiftingGoal : Prop :=
  ∀ {D : Shape} {L : Layout D} {C : Circuits D L} (checked : CheckedApplication C),
    Realizes C checked.indices

/-- Complete native endpoint. This defines the target proposition and does not prove it. -/
def CheckedApplicationCorrectGoal : Prop :=
  ∀ {D : Shape} {L : Layout D} {C : Circuits D L} (checked : CheckedApplication C),
    PicklesCorrect C checked.indices

/-- No new Pickles proof is needed once the application-specific lifting obligation is proved. -/
theorem checkedApplicationCorrect_of_lifting
    (h : CheckedApplicationLiftingGoal) : CheckedApplicationCorrectGoal :=
  fun checked ↦ ⟨h checked, frameworkCorrect _⟩

/-- The phase-1/2 lifting obligation supplies exactly the missing part of native correctness. -/
theorem picklesCorrect_of_realizes (C : Circuits D L) (I : ApplicationIndices D)
    (h : Realizes C I) : PicklesCorrect C I :=
  ⟨h, frameworkCorrect C⟩

/-- Transport keeps native correctness explicit and changes only the indices. -/
theorem importedApplication_picklesCorrect
    (C : Circuits D L) (native imported : ApplicationIndices D)
    (hNative : PicklesCorrect C native) (hMatch : imported = native) :
    PicklesCorrect C imported :=
  hMatch ▸ hNative

/-- Connection data for already fixed step and wrap runs. -/
structure StepWrapConnection {C : Circuits D L} {b : D.Branch}
    (step : StepRun C b) (wrap : WrapRun C) : Prop where
  branch : wrap.cells.1.whichBranch.val wrap.V = (b : Fq)
  publicInput : CircuitType.Reads step.V step.cells.out
    (StepStatement.ofWrap wrap.V wrap.cells.2.statement)

def StepWrapConnection.link {C : Circuits D L} {b : D.Branch}
    {step : StepRun C b} {wrap : WrapRun C} (h : StepWrapConnection step wrap) :
    StepWrapLink C b :=
  ⟨step, wrap, h.branch, h.publicInput⟩

/-- Connection data for already fixed producer-wrap and consumer-step runs. -/
structure WrapStepConnection
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {pb : producerD.Branch} {cb : consumerD.Branch}
    (wrap : WrapRun producer) (step : StepRun consumer cb) (i : consumerD.Slot cb) where
  sourceFor : SourceFor producer consumer cb i
  branch : wrap.cells.1.whichBranch.val wrap.V = (pb : Fq)
  mustVerify : CircuitType.Reads step.V (step.cells.prevs i).mustVerify true
  mask : Vector Bool (SlotSource.widths consumerD.width (consumer.wiring.sources cb) i)
  maskReads : CircuitType.Reads step.V (step.inp i).proofMask mask
  publicInput : CircuitType.Reads wrap.V wrapStatement
    ((step.inp i).packedAt producer.wiring.backend.wrapKey.cvk step.V mask)

def WrapStepConnection.link
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {pb : producerD.Branch} {cb : consumerD.Branch}
    {wrap : WrapRun producer} {step : StepRun consumer cb} {i : consumerD.Slot cb}
    (h : WrapStepConnection (pb := pb) wrap step i) : WrapStepLink producer consumer pb cb i :=
  ⟨h.sourceFor, wrap, step, h.branch, h.mustVerify, h.mask, h.maskReads, h.publicInput⟩

/-- The residual hypotheses of wrap handover, indexed by four fixed recovered runs. -/
structure WrapHandoverConnection
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {pb : producerD.Branch} {cb : consumerD.Branch}
    (ps : StepRun producer pb) (pw : WrapRun producer)
    (cs : StepRun consumer cb) (cw : WrapRun consumer)
    (pi : producerD.Slot pb) (ci : consumerD.Slot cb) : Prop where
  producerPair : StepWrapConnection ps pw
  consumerPair : StepWrapConnection cs cw
  sourceFor : SourceFor producer consumer cb ci
  mustVerifyProducer : CircuitType.Reads ps.V (ps.cells.prevs pi).mustVerify true
  keyProducer : ps.KeyBound pi
  mustVerifyConsumer : CircuitType.Reads cs.V (cs.cells.prevs ci).mustVerify true
  keyConsumer : cs.KeyBound ci
  middlePublicInput : CircuitType.Reads pw.V wrapStatement
    ((cs.inp ci).packedAt producer.wiring.backend.wrapKey.cvk
      cs.V (consumerPair.link.mask ci))

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

/-- The residual hypotheses of step handover, indexed by four fixed recovered runs. -/
structure StepHandoverConnection
    {producer : Circuits producerD producerL} {middle : Circuits middleD middleL}
    {consumer : Circuits consumerD consumerL}
    {pb : producerD.Branch} {mb : middleD.Branch} {cb : consumerD.Branch}
    (pw : WrapRun producer) (ms : StepRun middle mb)
    (mw : WrapRun middle) (cs : StepRun consumer cb)
    (mi : middleD.Slot mb) (ci : consumerD.Slot cb) where
  producerPair : WrapStepConnection (pb := pb) pw ms mi
  consumerPair : WrapStepConnection (pb := mb) mw cs ci
  middlePublicInput : CircuitType.Reads ms.V ms.cells.out
    (StepStatement.ofWrap mw.V mw.cells.2.statement)

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

/-- The individual step-wrap capstone applied after recovering the two runs. -/
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

/-- The individual wrap-step capstone applied after recovering the two runs. -/
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

/-- Matrices are arbitrary; recovered runs are fixed before connection hypotheses are supplied. -/
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

/-- The step-proof direction uses three applications and four recovered runs. -/
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

end Pickles.Application.CertificationDraft
