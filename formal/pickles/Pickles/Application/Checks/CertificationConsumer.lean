import Pickles.Application.Certification

/-!
# Consumers of the matrix-level interface

The capstones' implications obtained from accepted tables alone, against the supported
interface: the executions recovered first, the connection hypotheses over those executions,
and each conclusion read out of its predicate. Three consumers: the step-wrap capstone's
verifier acceptance under `SgOk`; the wrap-proof handover's application-state alternative,
across a producer and a consumer application with their own certificates; and the step-proof
handover's whole-message grouping, across three.
-/

namespace Pickles.Application.CertificationConsumer

open Snarky Bulletproof CompElliptic.Fields.Pasta Kimchi.Verifier

variable {D : Shape} {L : Layout D}

/-- From a certificate and two accepted tables: a step execution and a wrap execution at the
tables' statements such that, for any connection of the two and any slot, the capstone's
hypotheses give the reconstructed wrap proof's acceptance under `SgOk`. -/
theorem stepWrap_accepts {C : Circuits D L} (checked : CheckedApplication C) (b : D.Branch)
    (step : StepTable checked.indices b) (wrap : WrapTable checked.indices) :
    ∃ (s : StepRun C b) (w : WrapRun C),
      CircuitType.Reads s.V s.cells.out step.statement ∧
      CircuitType.Reads w.V wrapStatement wrap.statement ∧
      ∀ (h : StepWrapConnection s w) (i : D.Slot b),
        StepWrapAssumptions C b i →
        CircuitType.Reads s.V (s.cells.prevs i).mustVerify true →
        s.KeyBound i →
        SgOk C.setup.wrapSrs.σ (C.wiring.source b i).wrapKey.cvk (h.link.proof i)
          (h.link.proofPublicInput i) →
        kimchiVerify IpaPallas.curve C.setup.wrapSrs.σ (C.wiring.source b i).wrapKey.cvk
          (h.link.proof i) (h.link.proofPublicInput i) = true := by
  obtain ⟨s, w, hs, hw, hc⟩ :=
    matrices_stepWrap (checkedApplication_picklesCorrect C checked) b step wrap
  exact ⟨s, w, hs, hw, fun h i ha hm hk hsg => (hc h i ha hm hk).2.2 hsg⟩

variable {producerD middleD consumerD : Shape}
  {producerL : Layout producerD} {middleL : Layout middleD} {consumerL : Layout consumerD}

/-- Across a producer and a consumer application, each with its own certificate: the four
executions recovered from four accepted tables, and for any wrap-proof handover connection of
them, the consumer's accepted wrap proof carries the producer's application state to the
consumer's slot, unless a message collides. -/
theorem wrapHandover_appState
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    (pc : CheckedApplication producer) (cc : CheckedApplication consumer)
    (pb : producerD.Branch) (cb : consumerD.Branch)
    (pi : producerD.Slot pb) (ci : consumerD.Slot cb)
    (ps : StepTable pc.indices pb) (pw : WrapTable pc.indices)
    (cs : StepTable cc.indices cb) (cw : WrapTable cc.indices) :
    ∃ (s : StepRun producer pb) (w : WrapRun producer)
      (s' : StepRun consumer cb) (w' : WrapRun consumer),
      CircuitType.Reads s.V s.cells.out ps.statement ∧
      CircuitType.Reads w.V wrapStatement pw.statement ∧
      CircuitType.Reads s'.V s'.cells.out cs.statement ∧
      CircuitType.Reads w'.V wrapStatement cw.statement ∧
      ∀ h : WrapHandoverConnection s w s' w' pi ci,
        StepWrapAssumptions producer pb pi → StepWrapAssumptions consumer cb ci →
        kimchiVerify IpaPallas.curve producer.setup.wrapSrs.σ
            (consumer.wiring.source cb ci).wrapKey.cvk
            (h.handover.consumer.proof ci) (h.handover.consumer.proofPublicInput ci) = true →
        (h.handover.producer.step.cells.messagesForNextStepProof.appState.map
            (·.val h.handover.producer.step.V) =
          ((h.handover.consumer.step.cells.prevs ci).appState.map
            (·.val h.handover.consumer.step.V)).cast h.handover.sourceFor.prevSize) ∨
        (h.handover.producer.run pi (h.handover.producer.mask pi)).WrapCollision
          (h.handover.consumer.run ci (h.handover.consumer.mask ci)) producer.setup.dummy ∨
        (h.handover.producer.run pi (h.handover.producer.mask pi)).StepCollision
          (h.handover.consumer.run ci (h.handover.consumer.mask ci))
          (consumer.wiring.source cb ci).wrapKey.cvk := by
  obtain ⟨s, w, s', w', h1, h2, h3, h4, hc⟩ := matrices_wrap_handover
    (checkedApplication_picklesCorrect producer pc) (checkedApplication_picklesCorrect consumer cc)
    pb cb pi ci ps pw cs cw
  exact ⟨s, w, s', w', h1, h2, h3, h4, fun h ha hb hacc => (hc h ha hb).appState hacc⟩

/-- Across a producer, a middle and a consumer application, each with its own certificate: the
four executions recovered from four accepted tables, and for any step-proof handover connection
of them, the consumer's accepted step proof gives whole-message agreement with the producer's
proof accepted or the consumer's carrying an invalid accumulator, unless a message collides. -/
theorem stepHandover_messages
    {producer : Circuits producerD producerL} {middle : Circuits middleD middleL}
    {consumer : Circuits consumerD consumerL}
    (pc : CheckedApplication producer) (mc : CheckedApplication middle)
    (cc : CheckedApplication consumer)
    (pb : producerD.Branch) (mb : middleD.Branch) (cb : consumerD.Branch)
    (mi : middleD.Slot mb) (ci : consumerD.Slot cb)
    (pw : WrapTable pc.indices) (ms : StepTable mc.indices mb)
    (mw : WrapTable mc.indices) (cs : StepTable cc.indices cb) :
    ∃ (w : WrapRun producer) (s : StepRun middle mb)
      (w' : WrapRun middle) (s' : StepRun consumer cb),
      CircuitType.Reads w.V wrapStatement pw.statement ∧
      CircuitType.Reads s.V s.cells.out ms.statement ∧
      CircuitType.Reads w'.V wrapStatement mw.statement ∧
      CircuitType.Reads s'.V s'.cells.out cs.statement ∧
      ∀ h : StepHandoverConnection (pb := pb) w s w' s' mi ci,
        WrapStepAssumptions producer pb → WrapStepAssumptions middle mb →
        kimchiVerify IpaVesta.curve producer.setup.stepSrs.σ
            middle.wiring.backend.stepKeys[mb].cvk
            h.handover.consumer.proof h.handover.consumer.proofPublicInput = true →
        (h.handover.sentStep = h.handover.receivedStep ∧
          h.handover.sentWrap = h.handover.receivedWrap ∧
          (kimchiVerify IpaVesta.curve producer.setup.stepSrs.σ
              producer.wiring.backend.stepKeys[pb].cvk
              h.handover.producer.proof h.handover.producer.proofPublicInput = true ∨
            AccumulatorFailure producer.setup.stepSrs.σ middle.wiring.backend.stepKeys[mb].cvk
              h.handover.consumer.proof h.handover.consumer.proofPublicInput)) ∨
        h.handover.producer.run.WrapCollision h.handover.consumer.run producer.setup.dummy ∨
        h.handover.producer.run.StepCollision h.handover.consumer.run
          middle.wiring.backend.wrapKey.cvk := by
  obtain ⟨w, s, w', s', h1, h2, h3, h4, hc⟩ := matrices_step_handover
    (checkedApplication_picklesCorrect producer pc) (checkedApplication_picklesCorrect middle mc)
    (checkedApplication_picklesCorrect consumer cc) pb mb cb mi ci pw ms mw cs
  exact ⟨w, s, w', s', h1, h2, h3, h4, fun h ha hb => hc h ha hb⟩

end Pickles.Application.CertificationConsumer
