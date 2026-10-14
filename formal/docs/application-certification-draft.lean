import Pickles.Application.Certification
import PicklesFixture.ImportedIndices

/-!
# Elaborated examples of foreign-index comparison

Each consumer supplies application certificates, successful index comparisons, arbitrary
accepted imported matrices and connections on those matrices. The certificates supply the
capstones' static setup assumptions.
No source valuation or connection on an execution chosen by the lift is supplied. The conclusions
expose verifier acceptance, application-state threading and the complete message/failure grouping.
-/

namespace Pickles.Application.CertificationExamples

open Snarky Bulletproof CompElliptic.Fields.Pasta Kimchi.Verifier
open PicklesFixture.Application (compareIndices? compareIndices?_eq_none_iff)

variable {D : Shape} {L : Layout D}
variable {PD MD CD : Shape} {PL : Layout PD} {ML : Layout MD} {CL : Layout CD}

/-- The wrap proof read from connected matrices verifies under the accumulator check. -/
theorem stepWrap_accepts {C : Circuits D L} (cert : ApplicationCertified C)
    (I : ApplicationIndices D) (hI : compareIndices? I cert.indices = none)
    (b : D.Branch) (s : StepTable I b) (w : WrapTable I)
    (h : MatrixStepWrap C I b s w) (i : D.Slot b)
    (hm : CircuitType.Reads (stepValuation C I b s)
      ((stepCompilation C b).result.1.2.prevs i).mustVerify true)
    (hk : KeyReads IpaPallas.curve (stepValuation C I b s)
      ((C.wiring.sources b i).keyCells (stepCompilation C b).result.1.2.vk.points)
      (C.wiring.source b i).wrapKey.cvk)
    (hsg : SgOk C.setup.wrapSrs.σ (C.wiring.source b i).wrapKey.cvk
      (matrixWrapProof C I b s w i) (matrixWrapPub C I b s i)) :
    kimchiVerify IpaPallas.curve C.setup.wrapSrs.σ (C.wiring.source b i).wrapKey.cvk
      (matrixWrapProof C I b s w i) (matrixWrapPub C I b s i) = true := by
  have heq := compareIndices?_eq_none_iff.mp hI
  subst I
  exact (matrices_stepWrap cert b s w h i hm hk).2.2 hsg

/-- Compared matrices thread application state unless a message collides. -/
theorem wrapHandover_appState
    {P : Circuits PD PL} {C : Circuits CD CL}
    (pc : ApplicationCertified P) (cc : ApplicationCertified C)
    (PI : ApplicationIndices PD) (CI : ApplicationIndices CD)
    (hPI : compareIndices? PI pc.indices = none) (hCI : compareIndices? CI cc.indices = none)
    {pb : PD.Branch} {cb : CD.Branch} {pi : PD.Slot pb} {ci : CD.Slot cb}
    {ps : StepTable PI pb} {pw : WrapTable PI}
    {cs : StepTable CI cb} {cw : WrapTable CI}
    (conn : MatrixWrapHandover P C PI CI pb cb pi ci ps pw cs cw) :
    let nextVk := (C.wiring.source cb ci).wrapKey.cvk
    let r := matrixStepWrapRun P PI pb ps pw pi (matrixMask P PI pb ps pi)
    let r' := matrixStepWrapRun C CI cb cs cw ci (matrixMask C CI cb cs ci)
    kimchiVerify IpaPallas.curve P.setup.wrapSrs.σ nextVk
      (matrixWrapProof C CI cb cs cw ci) (matrixWrapPub C CI cb cs ci) = true →
    ((stepCompilation P pb).result.1.2.messagesForNextStepProof.appState.map
        (·.val (stepValuation P PI pb ps)) =
      (((stepCompilation C cb).result.1.2.prevs ci).appState.map
        (·.val (stepValuation C CI cb cs))).cast conn.sourceFor.prevSize) ∨
    r.WrapCollision r' P.setup.dummy ∨ r.StepCollision r' nextVk := by
  have hp := compareIndices?_eq_none_iff.mp hPI
  have hc := compareIndices?_eq_none_iff.mp hCI
  subst PI CI
  exact (matrices_wrap_handover pc cc pb cb pi ci ps pw cs cw conn).appState conn

/-- Compared matrices retain the whole-message, accumulator and collision alternatives. -/
theorem stepHandover_messages {P : Circuits PD PL} {M : Circuits MD ML}
    {C : Circuits CD CL} (pc : ApplicationCertified P) (mc : ApplicationCertified M)
    (cc : ApplicationCertified C) (PI : ApplicationIndices PD) (MI : ApplicationIndices MD)
    (CI : ApplicationIndices CD) (hPI : compareIndices? PI pc.indices = none)
    (hMI : compareIndices? MI mc.indices = none) (hCI : compareIndices? CI cc.indices = none)
    (pb : PD.Branch) (mb : MD.Branch) (cb : CD.Branch) (mi : MD.Slot mb) (ci : CD.Slot cb)
    (pw : WrapTable PI) (ms : StepTable MI mb)
    (mw : WrapTable MI) (cs : StepTable CI cb)
    (h : MatrixStepHandover P M C PI MI CI pb mb cb mi ci pw ms mw cs) :
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
  r.WrapCollision r' P.setup.dummy ∨ r.StepCollision r' M.wiring.backend.wrapKey.cvk := by
  have hp := compareIndices?_eq_none_iff.mp hPI
  have hm := compareIndices?_eq_none_iff.mp hMI
  have hc := compareIndices?_eq_none_iff.mp hCI
  subst PI MI CI
  exact matrices_step_handover pc mc cc pb mb cb mi ci pw ms mw cs h

end Pickles.Application.CertificationExamples
