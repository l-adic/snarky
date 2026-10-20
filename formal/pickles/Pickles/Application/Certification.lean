import Pickles.Application.MatrixRead
import Pickles.Application.Handover

/-!
# Matrix connections lift to the Pickles capstones

`ApplicationCertified.lift_step` and `lift_wrap` preserve the fixed matrix valuation as well
as the public statement. The lifted executions therefore preserve every observation of the
canonical compilation’s retained cells. Matrix connections are supplied before any execution
is constructed; the private link constructors carry them into the original capstones.

`matrices_stepWrap` and `matrices_wrapStep` expose the verification capstones.
`matrices_wrap_handover` and `matrices_step_handover` expose the four-execution handovers,
including whole-message equality, accumulator failure and collision alternatives.
All proof and message readings in their conclusions belong to the supplied matrices.
The certificates supply the static setup assumptions; source, key, mask and verification
conditions remain explicit. Nothing requires a cached prover execution or a witness-generation
argument.

The fixed interpretation need not recover arbitrary unused advice. It follows the
compiler’s labelled cells and equality classes; unrepresented variables read as zero.
The backend proves that this interpretation satisfies the source constraints.
-/

namespace Pickles.Application

open Snarky Snarky.Kimchi Bulletproof CompElliptic.Fields.Pasta Kimchi.Verifier
open scoped Kimchi

variable {D : Shape}
variable {PD MD CD : Shape}

/-- The source step execution with exactly the supplied matrix’s fixed reading. -/
private noncomputable def stepRunOf {C : Circuits D} (cert : ApplicationCertified C)
    (b : D.Branch) (t : StepTable cert.indices b) : StepRun C b :=
  { V := stepValuation C cert.indices b t
    advice := inertStepAdvice
    holds := by
      obtain ⟨r, _, hV⟩ := cert.lift_step b t
      have h := r.holds
      rw [C.stepBuilt_eq b r.advice, hV] at h
      exact h }

/-- The source wrap execution with exactly the supplied matrix’s fixed reading. -/
private noncomputable def wrapRunOf {C : Circuits D} (cert : ApplicationCertified C)
    (t : WrapTable cert.indices) : WrapRun C :=
  { V := wrapValuation C cert.indices t
    advice := inertWrapAdvice
    holds := by
      obtain ⟨r, _, hV⟩ := cert.lift_wrap t
      have h := r.holds
      rw [C.wrapBuilt_eq r.advice, hV] at h
      exact h }

/-- The lifted step reads the matrix’s public statement. -/
private theorem stepRunOf_public {C : Circuits D} (cert : ApplicationCertified C)
    (b : D.Branch) (t : StepTable cert.indices b) :
    CircuitType.Reads (stepRunOf cert b t).V (stepRunOf cert b t).cells.out t.statement := by
  obtain ⟨r, h, hV⟩ := cert.lift_step b t
  rw [hV, StepRun.cells_eq] at h
  exact h

/-- The lifted wrap reads the matrix’s public statement. -/
private theorem wrapRunOf_public {C : Circuits D} (cert : ApplicationCertified C)
    (t : WrapTable cert.indices) :
    CircuitType.Reads (wrapRunOf cert t).V wrapStatement t.statement := by
  obtain ⟨r, h, hV⟩ := cert.lift_wrap t
  rw [hV] at h
  exact h

/-- Connected matrices give a connected step/wrap execution pair. -/
private noncomputable def stepWrapOf {C : Circuits D} (cert : ApplicationCertified C)
    (b : D.Branch) (s : StepTable cert.indices b) (w : WrapTable cert.indices)
    (h : MatrixStepWrap C cert.indices b s w) : StepWrapLink C b where
  step := stepRunOf cert b s
  wrap := wrapRunOf cert w
  branch := by simpa only [WrapRun.cells_eq] using! h.1
  publicInput := by
    simpa only [wrapRunOf, WrapRun.cells_eq, h.2] using stepRunOf_public cert b s

/-- Connected matrices give a connected wrap/step execution pair. -/
private noncomputable def wrapStepOf {P : Circuits PD} {C : Circuits CD}
    (pc : ApplicationCertified P) (cc : ApplicationCertified C)
    (pb : PD.Branch) (cb : CD.Branch) (i : CD.Slot cb)
    (w : WrapTable pc.indices) (s : StepTable cc.indices cb)
    (h : MatrixWrapStep P C pc.indices cc.indices pb cb i w s) :
    WrapStepLink P C pb cb i where
  sourceFor := h.sourceFor
  wrap := wrapRunOf pc w
  step := stepRunOf cc cb s
  branch := by simpa only [WrapRun.cells_eq] using! h.branch
  mustVerify := by simpa only [StepRun.cells_eq] using! h.mustVerify
  mask := h.mask
  maskReads := by
    simpa only [StepRun.inp, StepRun.cells_eq, matrixInp] using! h.maskReads
  publicInput := by
    have hp := wrapRunOf_public pc w
    rw [h.publicInput] at hp
    simpa only [StepRun.inp, StepRun.cells_eq, matrixInp] using! hp

/-- Matrix connections give the native wrap-proof handover record. -/
private noncomputable def wrapHandoverOf {P : Circuits PD} {C : Circuits CD}
    (pc : ApplicationCertified P) (cc : ApplicationCertified C)
    (pb : PD.Branch) (cb : CD.Branch) (pi : PD.Slot pb) (ci : CD.Slot cb)
    (ps : StepTable pc.indices pb) (pw : WrapTable pc.indices)
    (cs : StepTable cc.indices cb) (cw : WrapTable cc.indices)
    (h : MatrixWrapHandover P C pc.indices cc.indices pb cb pi ci ps pw cs cw) :
    WrapProofHandover P C pb cb pi ci where
  producer := stepWrapOf pc pb ps pw h.producerPair
  consumer := stepWrapOf cc cb cs cw h.consumerPair
  sourceFor := h.sourceFor
  mustVerifyProducer := by
    simpa only [stepWrapOf, StepRun.cells_eq] using! h.mustVerifyProducer
  keyProducer := by
    simpa only [StepRun.KeyBound, stepWrapOf, StepRun.cells_eq] using! h.keyProducer
  mustVerifyConsumer := by
    simpa only [stepWrapOf, StepRun.cells_eq] using! h.mustVerifyConsumer
  keyConsumer := by
    simpa only [StepRun.KeyBound, stepWrapOf, StepRun.cells_eq] using! h.keyConsumer
  middlePublicInput := by
    have hp := wrapRunOf_public pc pw
    rw [h.middlePublicInput] at hp
    simpa only [stepWrapOf, StepWrapLink.mask, StepRun.inp, StepRun.cells_eq,
      matrixInp, matrixMask] using! hp

/-- Matrix connections give the native step-proof handover record. -/
private noncomputable def stepHandoverOf {P : Circuits PD} {M : Circuits MD}
    {C : Circuits CD}
    (pc : ApplicationCertified P) (mc : ApplicationCertified M) (cc : ApplicationCertified C)
    (pb : PD.Branch) (mb : MD.Branch) (cb : CD.Branch) (mi : MD.Slot mb) (ci : CD.Slot cb)
    (pw : WrapTable pc.indices) (ms : StepTable mc.indices mb)
    (mw : WrapTable mc.indices) (cs : StepTable cc.indices cb)
    (h : MatrixStepHandover P M C pc.indices mc.indices cc.indices pb mb cb mi ci pw ms mw cs) :
    StepProofHandover P M C pb mb cb mi ci where
  producer := wrapStepOf pc mc pb mb mi pw ms h.producerPair
  consumer := wrapStepOf mc cc mb cb ci mw cs h.consumerPair
  middlePublicInput := by
    simpa only [wrapStepOf, wrapRunOf, WrapRun.cells_eq, h.middlePublicInput]
      using stepRunOf_public mc mb ms

/-- Connected accepted matrices satisfy the original handover capstone’s implication. -/
theorem matrices_wrap_handover {P : Circuits PD} {C : Circuits CD}
    (pc : ApplicationCertified P) (cc : ApplicationCertified C)
    (pb : PD.Branch) (cb : CD.Branch) (pi : PD.Slot pb) (ci : CD.Slot cb)
    (ps : StepTable pc.indices pb) (pw : WrapTable pc.indices)
    (cs : StepTable cc.indices cb) (cw : WrapTable cc.indices)
    (h : MatrixWrapHandover P C pc.indices cc.indices pb cb pi ci ps pw cs cw) :
    WrapHandoverConclusion P C pc.indices cc.indices pb cb pi ci ps pw cs cw := by
  exact (wrapHandoverOf pc cc pb cb pi ci ps pw cs cw h).handover_or_collision
    (pc.stepWrapSetup pb pi) (cc.stepWrapSetup cb ci)

/-- Connected accepted matrices satisfy the original handover capstone’s implication. -/
theorem matrices_step_handover {P : Circuits PD} {M : Circuits MD} {C : Circuits CD}
    (pc : ApplicationCertified P) (mc : ApplicationCertified M) (cc : ApplicationCertified C)
    (pb : PD.Branch) (mb : MD.Branch) (cb : CD.Branch) (mi : MD.Slot mb) (ci : CD.Slot cb)
    (pw : WrapTable pc.indices) (ms : StepTable mc.indices mb)
    (mw : WrapTable mc.indices) (cs : StepTable cc.indices cb)
    (h : MatrixStepHandover P M C pc.indices mc.indices cc.indices pb mb cb mi ci pw ms mw cs) :
    StepHandoverConclusion P M C pc.indices mc.indices cc.indices pb mb cb mi ci pw ms mw cs h := by
  exact (stepHandoverOf pc mc cc pb mb cb mi ci pw ms mw cs h).handover_or_collision
    (pc.wrapStepSetup pb) (mc.wrapStepSetup mb)

/-- Connected step/wrap matrices satisfy the verification and accumulator capstone. -/
theorem matrices_stepWrap {C : Circuits D} (cert : ApplicationCertified C)
    (b : D.Branch) (s : StepTable cert.indices b) (w : WrapTable cert.indices)
    (h : MatrixStepWrap C cert.indices b s w) (i : D.Slot b)
    (hm : CircuitType.Reads (stepValuation C cert.indices b s)
      ((stepCompilation C b).result.1.2.prevs i).mustVerify true)
    (hk : KeyReads IpaPallas.curve (stepValuation C cert.indices b s)
      ((C.wiring.sources b i).keyCells (stepCompilation C b).result.1.2.vk.points)
      (C.wiring.source b i).wrapKey) : StepWrapConclusion C cert.indices b s w i := by
  have hm' : CircuitType.Reads (stepWrapOf cert b s w h).step.V
      ((stepWrapOf cert b s w h).step.cells.prevs i).mustVerify true := by
    simpa only [stepWrapOf, StepRun.cells_eq] using! hm
  have hk' : (stepWrapOf cert b s w h).step.KeyBound i := by
    simpa only [StepRun.KeyBound, stepWrapOf, StepRun.cells_eq] using! hk
  exact (stepWrapOf cert b s w h).verifies_proof i (cert.stepWrapSetup b i) hm' hk'

/-- Connected wrap/step matrices satisfy the verification, mask and accumulator capstone. -/
theorem matrices_wrapStep {P : Circuits PD} {C : Circuits CD}
    (pc : ApplicationCertified P) (cc : ApplicationCertified C)
    (pb : PD.Branch) (cb : CD.Branch) (i : CD.Slot cb)
    (w : WrapTable pc.indices) (s : StepTable cc.indices cb)
    (h : MatrixWrapStep P C pc.indices cc.indices pb cb i w s) :
    WrapStepConclusion P C pc.indices cc.indices pb cb i w s h :=
  (wrapStepOf pc cc pb cb i w s h).verifies_proof (pc.wrapStepSetup pb)

variable {PI : ApplicationIndices PD} {CI : ApplicationIndices CD}

/-- Application-state threading follows by projecting whole-message equality. -/
theorem WrapHandoverConclusion.appState
    {P : Circuits PD} {C : Circuits CD}
    {pb : PD.Branch} {cb : CD.Branch} {pi : PD.Slot pb} {ci : CD.Slot cb}
    {ps : StepTable PI pb} {pw : WrapTable PI} {cs : StepTable CI cb} {cw : WrapTable CI}
    (conn : MatrixWrapHandover P C PI CI pb cb pi ci ps pw cs cw)
    (h : WrapHandoverConclusion P C PI CI pb cb pi ci ps pw cs cw) :
    let nextVk := (C.wiring.source cb ci).wrapKey
    let r := matrixStepWrapRun P PI pb ps pw pi (matrixMask P PI pb ps pi)
    let r' := matrixStepWrapRun C CI cb cs cw ci (matrixMask C CI cb cs ci)
    kimchiVerify IpaPallas.curve P.setup.wrapSrs nextVk
      (matrixWrapProof C CI cb cs cw ci) (matrixWrapPub C CI cb cs ci) = true →
    ((stepCompilation P pb).result.1.2.messagesForNextStepProof.appState.map
        (·.val (stepValuation P PI pb ps)) =
      (((stepCompilation C cb).result.1.2.prevs ci).appState.map
        (·.val (stepValuation C CI cb cs))).cast conn.sourceFor.prevSize) ∨
    r.WrapCollision r' P.setup.dummy ∨ r.StepCollision r' nextVk := by
  intro nextVk r r' hAccept
  rcases h hAccept with hm | hf
  · left
    apply Vector.toList_inj.mp
    simpa only [Vector.toList_map, Vector.toList_cast] using!
      congrArg (fun m ↦ m.appState) hm.1
  · exact Or.inr hf

end Pickles.Application
