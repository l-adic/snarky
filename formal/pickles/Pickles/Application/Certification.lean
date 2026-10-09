import Pickles.Application.MatrixRead
import Pickles.Application.Handover

/-!
# Matrix connections lift to the Pickles capstones

`PicklesCorrect` preserves the fixed matrix valuation as well as the public statement.
Its executions therefore preserve every observation of the canonical compilation’s
retained cells. Matrix connections are supplied before any execution is constructed;
the link constructors carry those same connections into the original capstones.

`matrices_stepWrap` and `matrices_wrapStep` expose the verification capstones.
`matrices_wrap_handover` and `matrices_step_handover` expose the four-execution handovers,
including whole-message equality, accumulator failure and collision alternatives.
All proof and message readings in their conclusions belong to the supplied matrices.
The original setup, source, key, mask and verification assumptions remain explicit.
Nothing requires a cached prover execution or a witness-generation argument.

The fixed interpretation need not recover arbitrary unused advice. It follows the
compiler’s labelled cells and equality classes; unrepresented variables read as zero.
The backend proves that this interpretation satisfies the source constraints.
-/

namespace Pickles.Application

open Snarky Snarky.Kimchi Bulletproof CompElliptic.Fields.Pasta Kimchi.Verifier
open scoped Kimchi

variable {D : Shape} {L : Layout D}
variable {PD MD CD : Shape} {PL : Layout PD} {ML : Layout MD} {CL : Layout CD}
variable {I : ApplicationIndices D} {PI : ApplicationIndices PD}
  {MI : ApplicationIndices MD} {CI : ApplicationIndices CD}

/-- Every accepted matrix has a source execution at its statement and fixed matrix reading. -/
structure PicklesCorrect (C : Circuits D L) (I : ApplicationIndices D) : Prop where
  /-- Every step table lifts with its public and retained readings. -/
  step : ∀ (b : D.Branch) (t : StepTable I b),
    ∃ r : StepRun C b, CircuitType.Reads r.V r.cells.out t.statement ∧ r.V = stepValuation C I b t
  /-- Every wrap table lifts with its public and retained readings. -/
  wrap : ∀ (t : WrapTable I),
    ∃ r : WrapRun C, CircuitType.Reads r.V wrapStatement t.statement ∧ r.V = wrapValuation C I t

/-- A checked application’s indices preserve matrix readings when lifted to executions. -/
theorem checkedApplication_picklesCorrect (C : Circuits D L) (checked : CheckedApplication C) :
    PicklesCorrect C checked.indices :=
  ⟨checked.lift_step, checked.lift_wrap⟩

/-- The source step execution with exactly the supplied matrix’s fixed reading. -/
noncomputable def PicklesCorrect.stepRun {C : Circuits D L} (checked : PicklesCorrect C I)
    (b : D.Branch) (t : StepTable I b) : StepRun C b :=
  { V := stepValuation C I b t
    advice := inertStepAdvice
    holds := by
      let r := (checked.step b t).choose
      have h := r.holds
      rw [C.stepBuilt_eq b r.advice, (checked.step b t).choose_spec.2] at h
      exact h }

/-- The source wrap execution with exactly the supplied matrix’s fixed reading. -/
noncomputable def PicklesCorrect.wrapRun {C : Circuits D L} (checked : PicklesCorrect C I)
    (t : WrapTable I) : WrapRun C :=
  { V := wrapValuation C I t
    advice := inertWrapAdvice
    holds := by
      let r := (checked.wrap t).choose
      have h := r.holds
      rw [C.wrapBuilt_eq r.advice, (checked.wrap t).choose_spec.2] at h
      exact h }

/-- The lifted step uses the fixed matrix valuation. -/
private theorem stepRunOf_V {C : Circuits D L} (checked : PicklesCorrect C I)
    (b : D.Branch) (t : StepTable I b) :
    (PicklesCorrect.stepRun checked b t).V = stepValuation C I b t :=
  rfl

/-- The lifted wrap uses the fixed matrix valuation. -/
private theorem wrapRunOf_V {C : Circuits D L} (checked : PicklesCorrect C I)
    (t : WrapTable I) :
    (PicklesCorrect.wrapRun checked t).V = wrapValuation C I t :=
  rfl

/-- The lifted step reads the matrix’s public statement. -/
private theorem stepRunOf_public {C : Circuits D L} (checked : PicklesCorrect C I)
    (b : D.Branch) (t : StepTable I b) :
    CircuitType.Reads (PicklesCorrect.stepRun checked b t).V
      (PicklesCorrect.stepRun checked b t).cells.out t.statement := by
  have h := (checked.step b t).choose_spec.1
  rw [(checked.step b t).choose_spec.2, StepRun.cells_eq] at h
  exact h

/-- The lifted wrap reads the matrix’s public statement. -/
private theorem wrapRunOf_public {C : Circuits D L} (checked : PicklesCorrect C I)
    (t : WrapTable I) :
    CircuitType.Reads (PicklesCorrect.wrapRun checked t).V wrapStatement t.statement := by
  have h := (checked.wrap t).choose_spec.1
  rw [(checked.wrap t).choose_spec.2] at h
  exact h

/-- Every observation of retained step cells agrees with its fixed matrix reading. -/
theorem PicklesCorrect.stepRun_reads {C : Circuits D L} (checked : PicklesCorrect C I)
    (b : D.Branch) (t : StepTable I b) {α : Sort _}
    (read : Valuation Fp → C.StepCells b → α) :
    read (PicklesCorrect.stepRun checked b t).V (PicklesCorrect.stepRun checked b t).cells =
      read (stepValuation C I b t) (stepCompilation C b).result.1.2 := by
  rw [stepRunOf_V, StepRun.cells_eq]

/-- Every observation of retained wrap cells agrees with its fixed matrix reading. -/
theorem PicklesCorrect.wrapRun_reads {C : Circuits D L} (checked : PicklesCorrect C I)
    (t : WrapTable I) {α : Sort _}
    (read : Valuation Fq → C.WrapCells → α) :
    read (PicklesCorrect.wrapRun checked t).V (PicklesCorrect.wrapRun checked t).cells =
      read (wrapValuation C I t) (wrapCompilation C).result.1.2 := by
  rw [wrapRunOf_V, WrapRun.cells_eq]

/-- Connected matrices give a connected step/wrap execution pair. -/
private noncomputable def stepWrapOf {C : Circuits D L} (checked : PicklesCorrect C I)
    (b : D.Branch) (s : StepTable I b) (w : WrapTable I)
    (h : MatrixStepWrap C I b s w) : StepWrapLink C b where
  step := PicklesCorrect.stepRun checked b s
  wrap := PicklesCorrect.wrapRun checked w
  branch := by simpa only [wrapRunOf_V, WrapRun.cells_eq] using h.1
  publicInput := by
    simpa only [wrapRunOf_V, WrapRun.cells_eq, h.2] using stepRunOf_public checked b s

/-- Connected matrices give a connected wrap/step execution pair. -/
private noncomputable def wrapStepOf {P : Circuits PD PL} {C : Circuits CD CL}
    (pc : PicklesCorrect P PI) (cc : PicklesCorrect C CI)
    (pb : PD.Branch) (cb : CD.Branch) (i : CD.Slot cb)
    (w : WrapTable PI) (s : StepTable CI cb)
    (h : MatrixWrapStep P C PI CI pb cb i w s) :
    WrapStepLink P C pb cb i where
  sourceFor := h.sourceFor
  wrap := PicklesCorrect.wrapRun pc w
  step := PicklesCorrect.stepRun cc cb s
  branch := by simpa only [wrapRunOf_V, WrapRun.cells_eq] using h.branch
  mustVerify := by simpa only [stepRunOf_V, StepRun.cells_eq] using h.mustVerify
  mask := h.mask
  maskReads := by
    simpa only [StepRun.inp, StepRun.cells_eq, stepRunOf_V, matrixInp] using h.maskReads
  publicInput := by
    have hp := wrapRunOf_public pc w
    rw [h.publicInput] at hp
    simpa only [StepRun.inp, StepRun.cells_eq, stepRunOf_V, matrixInp] using hp

/-- Matrix connections give the native wrap-proof handover record. -/
private noncomputable def wrapHandoverOf {P : Circuits PD PL} {C : Circuits CD CL}
    (pc : PicklesCorrect P PI) (cc : PicklesCorrect C CI)
    (pb : PD.Branch) (cb : CD.Branch) (pi : PD.Slot pb) (ci : CD.Slot cb)
    (ps : StepTable PI pb) (pw : WrapTable PI)
    (cs : StepTable CI cb) (cw : WrapTable CI)
    (h : MatrixWrapHandover P C PI CI pb cb pi ci ps pw cs cw) :
    WrapProofHandover P C pb cb pi ci where
  producer := stepWrapOf pc pb ps pw h.producerPair
  consumer := stepWrapOf cc cb cs cw h.consumerPair
  sourceFor := h.sourceFor
  mustVerifyProducer := by
    simpa only [stepWrapOf, stepRunOf_V, StepRun.cells_eq] using h.mustVerifyProducer
  keyProducer := by
    simpa only [StepRun.KeyBound, stepWrapOf, stepRunOf_V, StepRun.cells_eq] using h.keyProducer
  mustVerifyConsumer := by
    simpa only [stepWrapOf, stepRunOf_V, StepRun.cells_eq] using h.mustVerifyConsumer
  keyConsumer := by
    simpa only [StepRun.KeyBound, stepWrapOf, stepRunOf_V, StepRun.cells_eq] using h.keyConsumer
  middlePublicInput := by
    have hp := wrapRunOf_public pc pw
    rw [h.middlePublicInput] at hp
    simpa only [stepWrapOf, StepWrapLink.mask, StepRun.inp, StepRun.cells_eq, stepRunOf_V,
      matrixInp, matrixMask] using hp

/-- Matrix connections give the native step-proof handover record. -/
private noncomputable def stepHandoverOf {P : Circuits PD PL} {M : Circuits MD ML}
    {C : Circuits CD CL}
    (pc : PicklesCorrect P PI) (mc : PicklesCorrect M MI) (cc : PicklesCorrect C CI)
    (pb : PD.Branch) (mb : MD.Branch) (cb : CD.Branch) (mi : MD.Slot mb) (ci : CD.Slot cb)
    (pw : WrapTable PI) (ms : StepTable MI mb)
    (mw : WrapTable MI) (cs : StepTable CI cb)
    (h : MatrixStepHandover P M C PI MI CI pb mb cb mi ci pw ms mw cs) :
    StepProofHandover P M C pb mb cb mi ci where
  producer := wrapStepOf pc mc pb mb mi pw ms h.producerPair
  consumer := wrapStepOf mc cc mb cb ci mw cs h.consumerPair
  middlePublicInput := by
    simpa only [wrapStepOf, wrapRunOf_V, WrapRun.cells_eq, h.middlePublicInput]
      using stepRunOf_public mc mb ms

/-- Connected accepted matrices satisfy the original handover capstone’s implication. -/
theorem matrices_wrap_handover {P : Circuits PD PL} {C : Circuits CD CL}
    (pc : PicklesCorrect P PI) (cc : PicklesCorrect C CI)
    (pb : PD.Branch) (cb : CD.Branch) (pi : PD.Slot pb) (ci : CD.Slot cb)
    (ps : StepTable PI pb) (pw : WrapTable PI)
    (cs : StepTable CI cb) (cw : WrapTable CI)
    (h : MatrixWrapHandover P C PI CI pb cb pi ci ps pw cs cw)
    (hp : StepWrapAssumptions P pb pi) (hc : StepWrapAssumptions C cb ci) :
    WrapHandoverConclusion P C PI CI pb cb pi ci ps pw cs cw := by
  exact (wrapHandoverOf pc cc pb cb pi ci ps pw cs cw h).handover_or_collision hp hc

/-- Connected accepted matrices satisfy the original handover capstone’s implication. -/
theorem matrices_step_handover {P : Circuits PD PL} {M : Circuits MD ML} {C : Circuits CD CL}
    (pc : PicklesCorrect P PI) (mc : PicklesCorrect M MI) (cc : PicklesCorrect C CI)
    (pb : PD.Branch) (mb : MD.Branch) (cb : CD.Branch) (mi : MD.Slot mb) (ci : CD.Slot cb)
    (pw : WrapTable PI) (ms : StepTable MI mb)
    (mw : WrapTable MI) (cs : StepTable CI cb)
    (h : MatrixStepHandover P M C PI MI CI pb mb cb mi ci pw ms mw cs)
    (hp : WrapStepAssumptions P pb) (hc : WrapStepAssumptions M mb) :
    StepHandoverConclusion P M C PI MI CI pb mb cb mi ci pw ms mw cs h := by
  exact (stepHandoverOf pc mc cc pb mb cb mi ci pw ms mw cs h).handover_or_collision hp hc


/-- Connected step/wrap matrices satisfy the verification and accumulator capstone. -/
theorem matrices_stepWrap {C : Circuits D L} (correct : PicklesCorrect C I)
    (b : D.Branch) (s : StepTable I b) (w : WrapTable I)
    (h : MatrixStepWrap C I b s w) (i : D.Slot b)
    (ha : StepWrapAssumptions C b i)
    (hm : CircuitType.Reads (stepValuation C I b s)
      ((stepCompilation C b).result.1.2.prevs i).mustVerify true)
    (hk : KeyReads IpaPallas.curve (stepValuation C I b s)
      ((C.wiring.sources b i).keyCells (stepCompilation C b).result.1.2.vk.points)
      (C.wiring.source b i).wrapKey.cvk) : StepWrapConclusion C I b s w i := by
  have hm' : CircuitType.Reads (stepWrapOf correct b s w h).step.V
      ((stepWrapOf correct b s w h).step.cells.prevs i).mustVerify true := by
    simpa only [stepWrapOf, stepRunOf_V, StepRun.cells_eq] using hm
  have hk' : (stepWrapOf correct b s w h).step.KeyBound i := by
    simpa only [StepRun.KeyBound, stepWrapOf, stepRunOf_V, StepRun.cells_eq] using hk
  exact (stepWrapOf correct b s w h).verifies_proof i ha hm' hk'

/-- Connected wrap/step matrices satisfy the verification, mask and accumulator capstone. -/
theorem matrices_wrapStep {P : Circuits PD PL} {C : Circuits CD CL}
    (pc : PicklesCorrect P PI) (cc : PicklesCorrect C CI)
    (pb : PD.Branch) (cb : CD.Branch) (i : CD.Slot cb)
    (w : WrapTable PI) (s : StepTable CI cb)
    (h : MatrixWrapStep P C PI CI pb cb i w s) (ha : WrapStepAssumptions P pb) :
    WrapStepConclusion P C PI CI pb cb i w s h :=
  (wrapStepOf pc cc pb cb i w s h).verifies_proof ha

/-- Application-state threading follows by projecting whole-message equality. -/
theorem WrapHandoverConclusion.appState
    {P : Circuits PD PL} {C : Circuits CD CL}
    {pb : PD.Branch} {cb : CD.Branch} {pi : PD.Slot pb} {ci : CD.Slot cb}
    {ps : StepTable PI pb} {pw : WrapTable PI} {cs : StepTable CI cb} {cw : WrapTable CI}
    (conn : MatrixWrapHandover P C PI CI pb cb pi ci ps pw cs cw)
    (h : WrapHandoverConclusion P C PI CI pb cb pi ci ps pw cs cw) :
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
  intro nextVk r r' hAccept
  rcases h hAccept with hm | hf
  · left
    apply Vector.toList_inj.mp
    simpa only [Vector.toList_map, Vector.toList_cast] using
      congrArg (fun m ↦ m.appState) hm.1
  · exact Or.inr hf

end Pickles.Application
