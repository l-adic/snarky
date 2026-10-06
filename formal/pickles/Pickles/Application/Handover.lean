import Pickles.Application.Verify

/-!
# Handover between application executions

Connected application executions preserve both complete messages and pass a proof's deferred
accumulator into the next proof on the same curve. Acceptance of that later proof gives
acceptance of the earlier proof or an accumulator-validity failure, unless a message hash
collides. The application capstones supply production, consumption and conditional verification;
the connections and assembled interfaces supply the intervening public statements and layouts.
-/

namespace Pickles.Application

open Snarky Snarky.Kimchi Bulletproof CompElliptic.Fields.Pasta Kimchi.Verifier

variable {producerD middleD consumerD : Shape}
  {producerL : Layout producerD} {middleL : Layout middleD} {consumerL : Layout consumerD}

/-- Four executions along a producer wrap, an intermediate step and wrap, and a consumer step. -/
structure StepProofHandover
    (producerApp : Circuits producerD producerL)
    (middleApp : Circuits middleD middleL)
    (consumerApp : Circuits consumerD consumerL)
    (producerBranch : producerD.Branch) (middleBranch : middleD.Branch)
    (consumerBranch : consumerD.Branch) (middleSlot : middleD.Slot middleBranch)
    (consumerSlot : consumerD.Slot consumerBranch) where
  /-- The producer wrap and intermediate step executions. -/
  producer : WrapStepLink producerApp middleApp producerBranch middleBranch middleSlot
  /-- The intermediate wrap and consumer step executions. -/
  consumer : WrapStepLink middleApp consumerApp middleBranch consumerBranch consumerSlot
  /-- The intermediate step's statement is the one its wrap circuit verifies. -/
  middlePublicInput : CircuitType.Reads producer.step.V producer.step.cells.out
    (StepStatement.ofWrap consumer.wrap.V consumer.wrap.cells.2.statement)

namespace StepProofHandover

variable {producerApp : Circuits producerD producerL}
  {middleApp : Circuits middleD middleL}
  {consumerApp : Circuits consumerD consumerL}
  {producerBranch : producerD.Branch} {middleBranch : middleD.Branch}
  {consumerBranch : consumerD.Branch} {middleSlot : middleD.Slot middleBranch}
  {consumerSlot : consumerD.Slot consumerBranch}
  (e : StepProofHandover producerApp middleApp consumerApp
    producerBranch middleBranch consumerBranch middleSlot consumerSlot)

/-- The complete step message emitted by the intermediate step execution. -/
def sentStep := readStepMessage e.producer.step.V e.producer.step.cells.messagesForNextStepProof

/-- The complete step message reconstructed by the consumer slot. -/
def receivedStep := rebuildStepMessage e.consumer.step.V middleApp.wiring.backend.wrapKey.cvk
  (e.consumer.step.inp consumerSlot) e.consumer.mask

/-- The complete wrap message emitted by the producer wrap execution. -/
def sentWrap := readWrapMessage e.producer.wrap.V producerApp.setup.dummy
  (e.producer.wrap.cells.2.messagesForNextWrapProof e.producer.wrap.cells.1)

/-- The complete wrap message reconstructed at the intermediate wrap's selected position. -/
def receivedWrap := readWrapMessage e.consumer.wrap.V producerApp.setup.dummy
  (e.consumer.wrap.cells.1.messagesForNextWrapProof e.producer.run.slotIndex)

/-- The application interfaces and middle statement connect the generic handover records. -/
private theorem hands : e.producer.run.Hands e.consumer.run :=
  ⟨e.middlePublicInput, e.consumer.sourceFor.prevSize⟩

/-- Complete messages agree and the earlier step proof accepts, or the accepted later proof
carries an invalid accumulator, unless one of the message hashes collides. -/
theorem handover_or_collision
    (hProducer : WrapStepAssumptions producerApp producerBranch)
    (hConsumer : WrapStepAssumptions middleApp middleBranch) :
    let σ := producerApp.setup.stepSrs.σ
    let vk := producerApp.wiring.backend.stepKeys[producerBranch].cvk
    let nextVk := middleApp.wiring.backend.stepKeys[middleBranch].cvk
    kimchiVerify IpaVesta.curve σ nextVk e.consumer.proof e.consumer.proofPublicInput = true →
    (e.sentStep = e.receivedStep ∧
     e.sentWrap = e.receivedWrap ∧
     (kimchiVerify IpaVesta.curve σ vk e.producer.proof e.producer.proofPublicInput = true ∨
      AccumulatorFailure σ nextVk e.consumer.proof e.consumer.proofPublicInput)) ∨
    e.producer.run.WrapCollision e.consumer.run producerApp.setup.dummy ∨
    e.producer.run.StepCollision e.consumer.run middleApp.wiring.backend.wrapKey.cvk := by
  intro σ vk nextVk hAccept
  obtain ⟨he, _, _, hv⟩ := e.producer.verifies_proof hProducer
  obtain ⟨_, hc, _, _⟩ := e.consumer.verifies_proof hConsumer
  have hd := congrArg Setup.dummy e.producer.sourceFor.setup
  exact WrapStepRun.handover_or_collision σ e.producer.run e.consumer.run
    producerApp.wiring.backend.wrapKey.cvk middleApp.wiring.backend.wrapKey.cvk
    producerApp.setup.dummy
    vk e.producer.proof e.producer.proofPublicInput
    nextVk e.consumer.proof e.consumer.proofPublicInput
    he (hd ▸ hc) e.hands hAccept hv

end StepProofHandover

/-- Two step-wrap pairs connected by a consumer slot receiving the producer's wrap proof. -/
structure WrapProofHandover
    (producerApp : Circuits producerD producerL) (consumerApp : Circuits consumerD consumerL)
    (producerBranch : producerD.Branch) (consumerBranch : consumerD.Branch)
    (producerSlot : producerD.Slot producerBranch)
    (consumerSlot : consumerD.Slot consumerBranch) where
  /-- The producer's step and wrap executions. -/
  producer : StepWrapLink producerApp producerBranch
  /-- The consumer's step and wrap executions. -/
  consumer : StepWrapLink consumerApp consumerBranch
  /-- The consumer slot resolves to the producer's exported interface. -/
  sourceFor : SourceFor producerApp consumerApp consumerBranch consumerSlot
  /-- The producer's selected predecessor must verify. -/
  mustVerifyProducer :
    CircuitType.Reads producer.step.V (producer.step.cells.prevs producerSlot).mustVerify true
  /-- The producer slot's cells hold its selected source key. -/
  keyProducer : producer.step.KeyBound producerSlot
  /-- The consumer's selected predecessor must verify. -/
  mustVerifyConsumer :
    CircuitType.Reads consumer.step.V (consumer.step.cells.prevs consumerSlot).mustVerify true
  /-- The consumer slot's cells hold its selected source key. -/
  keyConsumer : consumer.step.KeyBound consumerSlot
  /-- The consumer reconstructs the producer wrap's public statement. -/
  middlePublicInput : CircuitType.Reads producer.wrap.V wrapStatement
    ((consumer.step.inp consumerSlot).packedAt producerApp.wiring.backend.wrapKey.cvk
      consumer.step.V (consumer.mask consumerSlot))

namespace WrapProofHandover

variable {producerApp : Circuits producerD producerL}
  {consumerApp : Circuits consumerD consumerL}
  {producerBranch : producerD.Branch} {consumerBranch : consumerD.Branch}
  {producerSlot : producerD.Slot producerBranch} {consumerSlot : consumerD.Slot consumerBranch}
  (e : WrapProofHandover producerApp consumerApp
    producerBranch consumerBranch producerSlot consumerSlot)

/-- The complete step message emitted by the producer step execution. -/
def sentStep := readStepMessage e.producer.step.V e.producer.step.cells.messagesForNextStepProof

/-- The complete step message reconstructed by the consumer slot. -/
def receivedStep := rebuildStepMessage e.consumer.step.V
  (consumerApp.wiring.source consumerBranch consumerSlot).wrapKey.cvk
  (e.consumer.step.inp consumerSlot) (e.consumer.mask consumerSlot)

/-- The complete wrap message emitted by the producer wrap execution. -/
def sentWrap := readWrapMessage e.producer.wrap.V producerApp.setup.dummy
  (e.producer.wrap.cells.2.messagesForNextWrapProof e.producer.wrap.cells.1)

/-- The complete wrap message reconstructed at the consumer wrap's selected position. -/
def receivedWrap := readWrapMessage e.consumer.wrap.V producerApp.setup.dummy
  (e.consumer.wrap.cells.1.messagesForNextWrapProof
    (e.consumer.run consumerSlot (e.consumer.mask consumerSlot)).jf)

/-- Complete messages agree and the earlier wrap proof accepts, or the accepted later proof
carries an invalid accumulator, unless one of the message hashes collides. -/
theorem handover_or_collision
    (hProducer : StepWrapAssumptions producerApp producerBranch producerSlot)
    (hConsumer : StepWrapAssumptions consumerApp consumerBranch consumerSlot) :
    let σ := producerApp.setup.wrapSrs.σ
    let vk := (producerApp.wiring.source producerBranch producerSlot).wrapKey.cvk
    let nextVk := (consumerApp.wiring.source consumerBranch consumerSlot).wrapKey.cvk
    let r := e.producer.run producerSlot (e.producer.mask producerSlot)
    let r' := e.consumer.run consumerSlot (e.consumer.mask consumerSlot)
    kimchiVerify IpaPallas.curve σ nextVk
      (e.consumer.proof consumerSlot) (e.consumer.proofPublicInput consumerSlot) = true →
    (e.sentStep = e.receivedStep ∧
     e.sentWrap = e.receivedWrap ∧
     (kimchiVerify IpaPallas.curve σ vk
        (e.producer.proof producerSlot) (e.producer.proofPublicInput producerSlot) = true ∨
      AccumulatorFailure σ nextVk
        (e.consumer.proof consumerSlot) (e.consumer.proofPublicInput consumerSlot))) ∨
    r.WrapCollision r' producerApp.setup.dummy ∨ r.StepCollision r' nextVk := by
  intro σ vk nextVk r r' hAccept
  obtain ⟨he, _, hv⟩ :=
    e.producer.verifies_proof producerSlot hProducer e.mustVerifyProducer e.keyProducer
  obtain ⟨_, hc, _⟩ :=
    e.consumer.verifies_proof consumerSlot hConsumer e.mustVerifyConsumer e.keyConsumer
  let middle : WrapStepLink producerApp consumerApp producerBranch consumerBranch consumerSlot :=
    { sourceFor := e.sourceFor, wrap := e.producer.wrap, step := e.consumer.step
      branch := e.producer.branch, mustVerify := e.mustVerifyConsumer
      mask := e.consumer.mask consumerSlot, maskReads := hc.2.2
      publicInput := e.middlePublicInput }
  have hk := middle.mask_keeps
  have htie : CircuitType.Reads e.producer.wrap.V wrapStatement
      ((e.consumer.step.inp consumerSlot).packedAt nextVk
        e.consumer.step.V (e.consumer.mask consumerSlot)) := by
    dsimp only [nextVk]
    rw [e.sourceFor.wrapKey]
    exact e.middlePublicInput
  have hH : r.Hands r' nextVk :=
    ⟨htie, e.sourceFor.width,
      ⟨producerD.slots producerBranch, producerD.slots_le_width producerBranch, hk⟩,
      e.sourceFor.prevSize⟩
  have hd := congrArg Setup.dummy e.sourceFor.setup
  exact StepWrapRun.handover_or_collision σ r r' producerApp.setup.dummy vk
    (e.producer.proof producerSlot) (e.producer.proofPublicInput producerSlot) nextVk
    (e.consumer.proof consumerSlot) (e.consumer.proofPublicInput consumerSlot)
    he (hd ▸ hc) hH hAccept hv

/-- The producer's application-state vector equals the consumer rule's selected predecessor
statement, with its length identified by the source interface, unless a message hash collides. -/
theorem appState_eq_or_collision
    (hProducer : StepWrapAssumptions producerApp producerBranch producerSlot)
    (hConsumer : StepWrapAssumptions consumerApp consumerBranch consumerSlot) :
    let nextVk := (consumerApp.wiring.source consumerBranch consumerSlot).wrapKey.cvk
    let r := e.producer.run producerSlot (e.producer.mask producerSlot)
    let r' := e.consumer.run consumerSlot (e.consumer.mask consumerSlot)
    kimchiVerify IpaPallas.curve producerApp.setup.wrapSrs.σ nextVk
      (e.consumer.proof consumerSlot) (e.consumer.proofPublicInput consumerSlot) = true →
    (e.producer.step.cells.messagesForNextStepProof.appState.map
        (·.val e.producer.step.V) =
      ((e.consumer.step.cells.prevs consumerSlot).appState.map
        (·.val e.consumer.step.V)).cast e.sourceFor.prevSize) ∨
    r.WrapCollision r' producerApp.setup.dummy ∨ r.StepCollision r' nextVk := by
  intro nextVk r r' hAccept
  rcases e.handover_or_collision hProducer hConsumer hAccept with h | h
  · left
    apply Vector.toList_inj.mp
    simpa only [Vector.toList_map, Vector.toList_cast] using
      congrArg (fun m => m.appState) h.1
  · exact Or.inr h

end WrapProofHandover

end Pickles.Application
