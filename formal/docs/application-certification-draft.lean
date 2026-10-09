import Pickles.Application.Imported

/-!
# Elaborated examples of the production certification contract

Each consumer supplies certificates, arbitrary accepted imported matrices, connections
stated on those matrices, and the original capstone assumptions. No source valuation or
connection on an execution chosen by the lift is supplied. The conclusions expose verifier
acceptance, application-state threading and the complete message/failure grouping.
-/

namespace Pickles.Application.CertificationExamples

open Snarky Bulletproof CompElliptic.Fields.Pasta Kimchi.Verifier

variable {D : Shape} {L : Layout D}
variable {PD MD CD : Shape} {PL : Layout PD} {ML : Layout MD} {CL : Layout CD}

/-- The wrap proof read from connected matrices verifies under the accumulator check. -/
theorem stepWrap_accepts {C : Circuits D L} (cert : CertifiedIndices C)
    (b : D.Branch) (s : StepTable cert.indices b) (w : WrapTable cert.indices)
    (h : MatrixStepWrap C cert.indices b s w) (i : D.Slot b)
    (ha : StepWrapAssumptions C b i)
    (hm : CircuitType.Reads (stepValuation C cert.indices b s)
      ((stepCompilation C b).result.1.2.prevs i).mustVerify true)
    (hk : KeyReads IpaPallas.curve (stepValuation C cert.indices b s)
      ((C.wiring.sources b i).keyCells (stepCompilation C b).result.1.2.vk.points)
      (C.wiring.source b i).wrapKey.cvk)
    (hsg : SgOk C.setup.wrapSrs.σ (C.wiring.source b i).wrapKey.cvk
      (matrixWrapProof C cert.indices b s w i) (matrixWrapPub C cert.indices b s i)) :
    kimchiVerify IpaPallas.curve C.setup.wrapSrs.σ (C.wiring.source b i).wrapKey.cvk
      (matrixWrapProof C cert.indices b s w i) (matrixWrapPub C cert.indices b s i) = true :=
  (matrices_stepWrap cert.correct b s w h i ha hm hk).2.2 hsg

/-- Certified matrices thread application state unless a message collides. -/
theorem wrapHandover_appState
    {P : Circuits PD PL} {C : Circuits CD CL}
    (pc : CertifiedIndices P) (cc : CertifiedIndices C)
    {pb : PD.Branch} {cb : CD.Branch} {pi : PD.Slot pb} {ci : CD.Slot cb}
    {ps : StepTable pc.indices pb} {pw : WrapTable pc.indices}
    {cs : StepTable cc.indices cb} {cw : WrapTable cc.indices}
    (conn : MatrixWrapHandover P C pc.indices cc.indices pb cb pi ci ps pw cs cw)
    (hp : StepWrapAssumptions P pb pi) (hc : StepWrapAssumptions C cb ci) :
    let nextVk := (C.wiring.source cb ci).wrapKey.cvk
    let r := matrixStepWrapRun P pc.indices pb ps pw pi (matrixMask P pc.indices pb ps pi)
    let r' := matrixStepWrapRun C cc.indices cb cs cw ci (matrixMask C cc.indices cb cs ci)
    kimchiVerify IpaPallas.curve P.setup.wrapSrs.σ nextVk
      (matrixWrapProof C cc.indices cb cs cw ci) (matrixWrapPub C cc.indices cb cs ci) = true →
    ((stepCompilation P pb).result.1.2.messagesForNextStepProof.appState.map
        (·.val (stepValuation P pc.indices pb ps)) =
      (((stepCompilation C cb).result.1.2.prevs ci).appState.map
        (·.val (stepValuation C cc.indices cb cs))).cast conn.sourceFor.prevSize) ∨
    r.WrapCollision r' P.setup.dummy ∨ r.StepCollision r' nextVk :=
  (pc.wrap_handover cc pb cb pi ci ps pw cs cw conn hp hc).appState conn

/-- Certified matrices retain the whole-message, accumulator and collision alternatives. -/
theorem stepHandover_messages {P : Circuits PD PL} {M : Circuits MD ML}
    {C : Circuits CD CL} (pc : CertifiedIndices P) (mc : CertifiedIndices M)
    (cc : CertifiedIndices C)
    (pb : PD.Branch) (mb : MD.Branch) (cb : CD.Branch) (mi : MD.Slot mb) (ci : CD.Slot cb)
    (pw : WrapTable pc.indices) (ms : StepTable mc.indices mb)
    (mw : WrapTable mc.indices) (cs : StepTable cc.indices cb)
    (h : MatrixStepHandover P M C pc.indices mc.indices cc.indices pb mb cb mi ci pw ms mw cs)
    (hp : WrapStepAssumptions P pb) (hc : WrapStepAssumptions M mb) :
  let σ := P.setup.stepSrs.σ
  let vk := P.wiring.backend.stepKeys[pb].cvk
  let nextVk := M.wiring.backend.stepKeys[mb].cvk
  let r := matrixWrapStepRun P M pc.indices mc.indices mb mi pw ms
    h.producerPair.sourceFor h.producerPair.mask
  let r' := matrixWrapStepRun M C mc.indices cc.indices cb ci mw cs
    h.consumerPair.sourceFor h.consumerPair.mask
  let earlier := matrixStepProof P M pc.indices mc.indices mb mi pw ms
    h.producerPair.sourceFor h.producerPair.mask
  let later := matrixStepProof M C mc.indices cc.indices cb ci mw cs
    h.consumerPair.sourceFor h.consumerPair.mask
  kimchiVerify IpaVesta.curve σ nextVk later (matrixStepPub M mc.indices mb mw) = true →
  (readStepMessage (stepValuation M mc.indices mb ms)
      (stepCompilation M mb).result.1.2.messagesForNextStepProof =
    rebuildStepMessage (stepValuation C cc.indices cb cs) M.wiring.backend.wrapKey.cvk
      (matrixInp C cb ci) h.consumerPair.mask ∧
   readWrapMessage (wrapValuation P pc.indices pw) P.setup.dummy
      ((wrapCompilation P).result.1.2.2.messagesForNextWrapProof
        (wrapCompilation P).result.1.2.1) =
    readWrapMessage (wrapValuation M mc.indices mw) P.setup.dummy
      ((wrapCompilation M).result.1.2.1.messagesForNextWrapProof r.slotIndex) ∧
   (kimchiVerify IpaVesta.curve σ vk earlier (matrixStepPub P pc.indices pb pw) = true ∨
    AccumulatorFailure σ nextVk later (matrixStepPub M mc.indices mb mw))) ∨
  r.WrapCollision r' P.setup.dummy ∨ r.StepCollision r' M.wiring.backend.wrapKey.cvk :=
  pc.step_handover mc cc pb mb cb mi ci pw ms mw cs h hp hc

end Pickles.Application.CertificationExamples
