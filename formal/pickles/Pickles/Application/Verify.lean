import Pickles.Application.Run
import Pickles.Application.Proof

/-!
# Verification across application executions

The application wiring supplies key layouts, domain pins, widths and chunk counts to the
step-wrap and wrap-step circuit capstones. Their SRS correspondence and avoidance premises
remain explicit, as do the connections between independently supplied executions.
-/

namespace Pickles.Application

open Snarky Snarky.Kimchi Bulletproof CompElliptic.Fields.Pasta Kimchi.Verifier

variable {D : Shape} {L : Layout D}
variable {producerD consumerD : Shape}
  {producerL : Layout producerD} {consumerL : Layout consumerD}

private instance (D : Shape) : NeZero D.branches := ⟨Nat.ne_of_gt D.branches_pos⟩

/-- The SRS-dependent premises for a branch slot's wrap-proof verification. -/
structure StepWrapAssumptions (C : Circuits D L) (b : D.Branch) (i : D.Slot b) : Prop where
  /-- The padding commitment is finite. -/
  dummy_ne : C.setup.dummySg ≠ 0
  /-- The source's table contains its key's SRS Lagrange commitments. -/
  lagrange : (C.wiring.sources b i).lagrange =
    (C.wiring.source b i).wrapKey.cvk.lagrangePoints C.setup.wrapSrs.σ
      (CircuitType.size Fp (PackedWrapStatement StepIPARounds (Type1 Fp) Fp))
  /-- The SRS avoids the relations named by every slot statement. -/
  avoids : ∀ (inp : VerifyOneInput (D.prevSize b i) StepIPARounds WrapIPARounds
      1 (C.wiring.sourceChunks b i) (SlotSource.widths D.width (C.wiring.sources b) i))
      msg, C.setup.wrapSrs.σ.Avoids
        (stepRelationsAt C.setup.wrapSrs.σ (C.wiring.source b i).wrapKey.cvk
          (inp.statement msg))

/-- The SRS-dependent premises for a selected branch's step-proof verification. -/
structure WrapStepAssumptions
    (producer : Circuits producerD producerL)
    (producerBranch : producerD.Branch) : Prop where
  /-- The branch's table contains its key's SRS Lagrange commitments. -/
  lagrange : producer.stepLagrange producer.wiring.backend.stepKeys[producerBranch].cvk.domainLog2 =
    producer.wiring.backend.stepKeys[producerBranch].cvk.lagrangePoints producer.setup.stepSrs.σ
      (CircuitType.size Fp (StepStatement (UnfVal WrapIPARounds) Fp producerD.width))
  /-- The selected key's commitments are finite. -/
  points_ne : ∀ P ∈ producer.wiring.backend.stepKeys[producerBranch].cvk.comms.indexPoints, P ≠ 0
  /-- The SRS avoids the selected key's Lagrange relations. -/
  avoids : producer.setup.stepSrs.σ.Avoids
    (producer.wiring.backend.stepKeys[producerBranch].cvk.lagrangeRelations StepIPARounds
      (CircuitType.size Fp (StepStatement (UnfVal WrapIPARounds) Fp producerD.width)))

/-- The retained slot pins agree with the application's assembled pins. -/
private theorem WrapRun.pins {C : Circuits D L} (r : WrapRun C) (j : Fin D.width) :
    r.cells.1.slots[j].pins = C.wiring.pins[j] := by
  dsimp only [WrapRun.cells, Circuits.wrapBuilt, Circuits.wrapCircuit]
  rw [compileWith_wrapMainCircuit_cells]
  exact ((builder_spec_iff _ _).mp (wrapMain_pins
    (FopParams.of IpaPallas.curve 1 WrapIPARounds Linearization.fqTokens) r.V
    D.widths (stepDomainLog2s C.wiring.stepKeys) (stepKeyCells C.wiring.stepKeys)
    C.wiring.pins C.stepLagrange C.setup.step.σ.h C.setup.dummy L.wrapWidths r.advice
    wrapStatement) _ (fun con hc => r.holds con
      (mem_compileWith_wrapMainCircuit _ _ _ _ _ _ _ _ _ _ hc))) j

/-- The source's public-input table fits its checked wrap domain. -/
private theorem source_size (C : Circuits D L) (b : D.Branch) (i : D.Slot b) :
    CircuitType.size Fp (PackedWrapStatement StepIPARounds (Type1 Fp) Fp) ≤
      (C.wiring.source b i).wrapKey.cvk.n := by
  calc
    _ ≤ CircuitType.size Fq (StatementPacked StepIPARounds (Type1 Fq) Fq) := by decide
    _ = (C.wiring.source b i).wrapKey.cvk.publicCount :=
      (C.wiring.source b i).wrapLayout.publicCount_eq.symm
    _ ≤ _ := (C.wiring.source b i).wrapKey.cvk.publicCount_le

-- Preserve the shared compiled circuit terms in the capstone's conclusion.
set_option cleanup.letToHave false in
/-- Connected application executions verify the slot's wrap proof up to its deferred equation. -/
private theorem StepWrapLink.verifies {C : Circuits D L} {b : D.Branch} (e : StepWrapLink C b)
    (i : D.Slot b) (hAssumptions : StepWrapAssumptions C b i)
    (hmv : CircuitType.Reads e.step.V (e.step.cells.prevs i).mustVerify true)
    (hkey : e.step.KeyBound i) :
    ∃ (cp : KimchiProof IpaPallas.curve 1 WrapIPARounds)
      (ms : Vector Bool (SlotSource.widths D.width (C.wiring.sources b) i)),
      let r := e.run i ms
      let σ := C.setup.wrapSrs.σ
      let vk := (C.wiring.source b i).wrapKey.cvk
      let pub := r.inp.publicInputAt vk e.step.V ms
      let sl := e.wrap.cells.1.slots[r.jf]
      r.inp.WireReads vk e.step.V
        ((C.wiring.sources b i).keyCells e.step.cells.vk.points) cp ms ∧
      FopTies σ vk cp pub
        (ScalarHalf.wrap e.wrap.V sl.unfinalized sl.evals sl.prevChallenges) ∧
      r.Produces C.setup.dummy ⟨cp.opening.sg, wireChallenges σ vk cp pub⟩ ∧
      r.Consumes C.setup.dummy cp.olds.toList ∧
      (SgOk σ vk cp pub → kimchiVerify IpaPallas.curve σ vk cp pub = true) := by
  letI : CheckedType Fp (Builder e.step.V (KimchiConstraint Fp))
      D.schema.Input D.schema.InputVar := D.schema.inputCheck
  have hpin : e.wrap.cells.1.slots[D.paddedSlot b i].pins[b] =
      some (C.wiring.source b i).wrapIndex := by
    rw [e.wrap.pins]
    exact C.wiring.pins_at_slot b i
  have cap := Pickles.stepWrap_kimchiVerify
    (inVal := D.schema.Input) (outVal := D.schema.Output)
    C.setup.wrapSrs rfl
    (fun i => FopParams.of IpaVesta.curve (C.wiring.sourceChunks b i)
      StepIPARounds Linearization.fpTokens)
    C.wiring.backend.stepDomains.list (D.slots_le_width b) L.width_le
    C.setup.dummySg hAssumptions.dummy_ne C.setup.dummyUnf (C.wiring.sources b)
    (C.source_bound b) e.step.V (C.rules b) e.step.advice e.wrap.V D.widths
    C.setup.step.σ C.stepLagrange C.wiring.stepKeys C.wiring.pins C.setup.dummy
    L.wrapWidths e.wrap.advice C.wiring.valid.branches_le b
    e.step.holds e.wrap.holds e.branch e.publicInput i hmv
    (C.wiring.source b i).wrapKey (C.wiring.source b i).wrapChunks
    (C.wiring.source b i).wrapLayout ⟨source_size C b i, hAssumptions.lagrange⟩ hkey
    hAssumptions.avoids (C.wiring.source b i).wrapIndex
    (by convert hpin using 1)
    (C.wiring.pin_domain b i _ (C.wiring.pins_at_slot b i))
  obtain ⟨cp, ms, hwire, hf, he, hc, hhS, hhW, hv⟩ := cap
  have htie := e.publicInput
  dsimp only [StepWrapRun.Produces, StepWrapRun.Consumes, StepWrapRun.Hashes,
    StepWrapLink.run, StepWrapRun.inp, StepWrapRun.jf, StepRun.cells, WrapRun.cells,
    Circuits.stepBuilt, Circuits.wrapBuilt, Circuits.stepCircuit, Circuits.wrapCircuit,
    Setup.wrapSrs] at *
  exact ⟨cp, ms, hwire, hf, ⟨⟨htie, hhS, hhW⟩, he⟩,
    ⟨⟨htie, hhS, hhW⟩, hc, hwire.1⟩, hv⟩

-- Preserve the shared compiled circuit terms in the capstone's conclusion.
set_option cleanup.letToHave false in
/-- Connected application executions verify the selected step proof up to its deferred equation. -/
private theorem WrapStepLink.verifies
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {producerBranch : producerD.Branch} {consumerBranch : consumerD.Branch}
    {slot : consumerD.Slot consumerBranch}
    (e : WrapStepLink producer consumer producerBranch consumerBranch slot)
    (hAssumptions : WrapStepAssumptions producer producerBranch) :
    ∃ (cp : KimchiProof IpaVesta.curve producer.wiring.backend.stepChunks StepIPARounds)
      (oldsW : Vector (IpaVesta.curve.Point × Bool) producerD.width),
      let r := e.run
      let σ := producer.setup.stepSrs.σ
      let vk := producer.wiring.backend.stepKeys[producerBranch].cvk
      let pub := wrapPublicInput σ vk e.wrap.V e.wrap.cells.2.statement
      ProofReads (wrapSide e.wrap.V) e.wrap.cells.2.cells.wComm e.wrap.cells.2.cells.zComm
        e.wrap.cells.2.cells.tComm e.wrap.cells.2.cells.opening cp ∧
      OldsRead e.wrap.V e.wrap.cells.2.cells.sgOld cp oldsW ∧
      FopTies σ vk cp pub
        ((e.sourceFor.chunks ▸ r.inp :
            VerifyOneInput (consumerD.prevSize consumerBranch slot)
              StepIPARounds WrapIPARounds 1 producer.wiring.backend.stepChunks
              (SlotSource.widths consumerD.width
                (consumer.wiring.sources consumerBranch) slot)).finalizedHalf e.step.V) ∧
      r.Produces producer.wiring.backend.wrapKey.cvk producer.setup.dummy
        ⟨cp.opening.sg, wireChallenges σ vk cp pub⟩ ∧
      r.Consumes producer.wiring.backend.wrapKey.cvk producer.setup.dummy cp.olds.toList ∧
      (∀ (j : Nat)
          (hj : j <
            SlotSource.widths consumerD.width (consumer.wiring.sources consumerBranch) slot),
        e.mask[j] = decide (producerD.width - producerD.slots producerBranch ≤ j)) ∧
      (SgOk σ vk cp pub → kimchiVerify IpaVesta.curve σ vk cp pub = true) := by
  letI : CheckedType Fp (Builder e.step.V (KimchiConstraint Fp))
      consumerD.schema.Input consumerD.schema.InputVar := consumerD.schema.inputCheck
  have hsetup := e.sourceFor.setup
  have hstep := e.step.holds
  simp only [Circuits.stepBuilt, Circuits.stepCircuit] at hstep
  rw [← hsetup] at hstep
  have cap := Pickles.wrapStep_kimchiVerify
    (inVal := consumerD.schema.Input) (outVal := consumerD.schema.Output)
    producer.setup.wrapSrs.σ producer.wiring.backend.wrapKey.cvk rfl producer.setup.stepSrs rfl
    producer.wiring.stepKeys producerBranch producer.wiring.backend.stepKeys[producerBranch]
    (by simp [Wiring.stepKeys]) (producer.wiring.valid.stepChunks producerBranch)
    producer.stepLagrange hAssumptions.lagrange e.wrap.V producerD.widths
    (by simpa [Wiring.stepKeys] using producer.wiring.step_key_layout producerBranch)
    producer.wiring.pins producer.setup.dummy producerL.wrapWidths e.wrap.advice
    producer.wiring.valid.branches_le
    (by simpa [Wiring.stepKeys] using hAssumptions.points_ne)
    (by simpa [Wiring.stepKeys] using hAssumptions.avoids)
    consumer.wiring.backend.stepDomains.list producer.wiring.backend.stepDomains
    ((consumerD.slots_le_width consumerBranch).trans consumerL.width_le) producerL.width_le
    (consumer.wiring.sources consumerBranch) (consumer.source_bound consumerBranch)
    (constPt producer.setup.dummySg) producer.setup.dummyUnf e.step.V
    (consumer.rules consumerBranch) e.step.advice
    e.wrap.holds hstep e.branch slot e.sourceFor.chunks
    (by simpa only [StepRun.cells, Circuits.stepBuilt, Circuits.stepCircuit, hsetup]
      using e.mustVerify)
    e.sourceFor.domains e.sourceFor.width e.mask
    (by simpa only [StepRun.inp, StepRun.cells, Circuits.stepBuilt, Circuits.stepCircuit,
      hsetup] using e.maskReads)
    (by simpa only [StepRun.inp, StepRun.cells, Circuits.stepBuilt, Circuits.stepCircuit,
      hsetup, wrapStatement] using e.publicInput)
  obtain ⟨cp, oldsW, hpr, hol, hf, he, hc, hk, hhW, hhS, hv⟩ := cap
  simp only [Wiring.stepKeys, Fin.getElem_fin, Vector.getElem_map] at hf he hv
  have htie := e.publicInput
  dsimp only [WrapStepRun.Produces, WrapStepRun.Consumes, WrapStepRun.Hashes,
    WrapStepLink.run, WrapStepRun.inp, StepRun.inp, StepRun.cells, WrapRun.cells,
    Circuits.stepBuilt, Circuits.wrapBuilt, Circuits.stepCircuit, Circuits.wrapCircuit,
    Setup.wrapSrs, Setup.stepSrs] at *
  simp only [hsetup] at *
  refine ⟨cp, oldsW, hpr, hol, hf, ⟨⟨htie, hhW, hhS⟩, he⟩,
    ⟨⟨htie, hhW, hhS⟩, hc, producerD.slots producerBranch,
      producerD.slots_le_width producerBranch, ?_⟩, ?_, hv⟩
  all_goals simpa [Shape.widths] using hk

set_option cleanup.letToHave false in
/-- The reconstructed step proof inherits the capstone's accumulator and verification facts. -/
theorem WrapStepLink.verifies_proof
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {producerBranch : producerD.Branch} {consumerBranch : consumerD.Branch}
    {slot : consumerD.Slot consumerBranch}
    (e : WrapStepLink producer consumer producerBranch consumerBranch slot)
    (hAssumptions : WrapStepAssumptions producer producerBranch) :
    let σ := producer.setup.stepSrs.σ
    let vk := producer.wiring.backend.stepKeys[producerBranch].cvk
    e.run.Produces producer.wiring.backend.wrapKey.cvk producer.setup.dummy
      ⟨e.proof.opening.sg, wireChallenges σ vk e.proof e.proofPublicInput⟩ ∧
    e.run.Consumes producer.wiring.backend.wrapKey.cvk producer.setup.dummy e.proof.olds.toList ∧
    (∀ (j : Nat)
        (hj : j < SlotSource.widths consumerD.width (consumer.wiring.sources consumerBranch) slot),
      e.mask[j] = decide (producerD.width - producerD.slots producerBranch ≤ j)) ∧
    (SgOk σ vk e.proof e.proofPublicInput →
      kimchiVerify IpaVesta.curve σ vk e.proof e.proofPublicInput = true) := by
  obtain ⟨cp, _, hp, _, hf, he, hc, hk, hv⟩ := e.verifies hAssumptions
  let cells := e.wrap.cells.2.cells
  let pr : IvpProof StepIPARounds producer.wiring.backend.stepChunks
      (FVar Fq) (Type1 (FVar Fq)) :=
    ⟨cells.wComm, cells.zComm, cells.tComm, cells.opening⟩
  have hr := readProof_verification (wrapSide e.wrap.V)
    producer.setup.stepSrs.σ producer.wiring.backend.stepKeys[producerBranch].cvk
    pr cp e.proofPublicInput
    _ _ _ _ hp hf.evals hf.pubEvals hf.ftEval1
    (show (WrapStep.consumedAccumulators e.wrap.V e.step.V e.wrap.cells.1
      e.run.inp.prevChallenges e.sourceFor.width e.mask).toArray = cp.olds by
        simpa only [WrapStepLink.run, Array.toArray_toList] using
          congrArg List.toArray hc.2.1)
  dsimp only [WrapStepLink.proof, VerifyOneInput.finalizedHalf, ScalarHalf.step, pr, cells] at hr ⊢
  obtain ⟨hsg, ho, hch, hSg, hkv⟩ := hr
  refine ⟨?_, ?_, hk, fun hs => hkv.trans (hv (hSg.mp hs))⟩
  · exact ⟨he.1, he.2.trans (congrArg₂ Accumulator.mk hsg.symm hch.symm)⟩
  · exact ⟨hc.1, hc.2.1.trans (congrArg Array.toList ho.symm), hc.2.2⟩

/-- The consumer slot's mask keeps exactly the producer branch's slots: a reading of cells across
the public-input tie, with no Lagrange-table premise. -/
theorem WrapStepLink.mask_keeps
    {producer : Circuits producerD producerL} {consumer : Circuits consumerD consumerL}
    {producerBranch : producerD.Branch} {consumerBranch : consumerD.Branch}
    {slot : consumerD.Slot consumerBranch}
    (e : WrapStepLink producer consumer producerBranch consumerBranch slot) :
    ∀ (j : ℕ)
      (hj : j < SlotSource.widths consumerD.width (consumer.wiring.sources consumerBranch) slot),
      e.mask[j] = decide (producerD.width - producerD.slots producerBranch ≤ j) := by
  letI : CheckedType Fp (Builder e.step.V (KimchiConstraint Fp))
      consumerD.schema.Input consumerD.schema.InputVar := consumerD.schema.inputCheck
  have hsetup := e.sourceFor.setup
  have hstep := e.step.holds
  simp only [Circuits.stepBuilt, Circuits.stepCircuit] at hstep
  rw [← hsetup] at hstep
  have hk := Pickles.wrapStep_mask
    (inVal := consumerD.schema.Input) (outVal := consumerD.schema.Output)
    producer.setup.wrapSrs.σ producer.wiring.backend.wrapKey.cvk rfl producer.setup.stepSrs rfl
    producer.wiring.stepKeys producerBranch
    (by simpa [Wiring.stepKeys] using
      producer.wiring.backend.stepKeys[producerBranch].domainLog2_le.trans_lt (by decide))
    producer.stepLagrange e.wrap.V producerD.widths producer.wiring.pins producer.setup.dummy
    producerL.wrapWidths e.wrap.advice producer.wiring.valid.branches_le
    consumer.wiring.backend.stepDomains.list
    ((consumerD.slots_le_width consumerBranch).trans consumerL.width_le) producerL.width_le
    (consumer.wiring.sources consumerBranch) (consumer.source_bound consumerBranch)
    (constPt producer.setup.dummySg) producer.setup.dummyUnf e.step.V
    (consumer.rules consumerBranch) e.step.advice
    e.wrap.holds hstep e.branch slot
    (by simpa only [StepRun.cells, Circuits.stepBuilt, Circuits.stepCircuit, hsetup]
      using e.mustVerify)
    e.sourceFor.width e.mask
    (by simpa only [StepRun.inp, StepRun.cells, Circuits.stepBuilt, Circuits.stepCircuit,
      hsetup] using e.maskReads)
    (by simpa only [StepRun.inp, StepRun.cells, Circuits.stepBuilt, Circuits.stepCircuit,
      hsetup, wrapStatement] using e.publicInput)
  simpa [Shape.widths] using hk

set_option cleanup.letToHave false in
/-- The reconstructed wrap proof inherits the capstone's accumulator and verification facts. -/
theorem StepWrapLink.verifies_proof {C : Circuits D L} {b : D.Branch} (e : StepWrapLink C b)
    (i : D.Slot b) (hAssumptions : StepWrapAssumptions C b i)
    (hmv : CircuitType.Reads e.step.V (e.step.cells.prevs i).mustVerify true)
    (hkey : e.step.KeyBound i) :
    let σ := C.setup.wrapSrs.σ
    let vk := (C.wiring.source b i).wrapKey.cvk
    let r := e.run i (e.mask i)
    r.Produces C.setup.dummy
      ⟨(e.proof i).opening.sg, wireChallenges σ vk (e.proof i) (e.proofPublicInput i)⟩ ∧
    r.Consumes C.setup.dummy (e.proof i).olds.toList ∧
    (SgOk σ vk (e.proof i) (e.proofPublicInput i) →
      kimchiVerify IpaPallas.curve σ vk (e.proof i) (e.proofPublicInput i) = true) := by
  obtain ⟨cp, ms, hp, hf, he, hc, hv⟩ := e.verifies i hAssumptions hmv hkey
  have hm : ms = e.mask i := (CircuitType.reads_iff.mp hp.1).2.symm
  subst ms
  have hr := readProof_verification (stepSide e.step.V)
    C.setup.wrapSrs.σ (C.wiring.source b i).wrapKey.cvk
    (e.step.inp i).proof cp (e.proofPublicInput i) _ _ _ _ hp.2.2.1
    hf.evals hf.pubEvals hf.ftEval1
    (show (StepWrap.consumedAccumulators e.step.V e.wrap.V (e.step.inp i)
      C.setup.dummy e.wrap.cells.1 (D.paddedSlot b i)).toArray = cp.olds by
        simpa only [StepWrapLink.run, StepWrapRun.inp, StepRun.inp, StepWrapRun.jf,
          Shape.paddedSlot, Array.toArray_toList] using congrArg List.toArray hc.2.1)
  dsimp only [StepWrapLink.proof, ScalarHalf.wrap, StepWrapLink.run, StepWrapRun.inp,
    StepRun.inp, StepWrapRun.jf, Shape.paddedSlot] at hr ⊢
  obtain ⟨hsg, ho, hch, hSg, hkv⟩ := hr
  refine ⟨?_, ?_, fun hs => hkv.trans (hv (hSg.mp hs))⟩
  · exact ⟨he.1, he.2.trans (congrArg₂ Accumulator.mk hsg.symm hch.symm)⟩
  · exact ⟨hc.1, hc.2.1.trans (congrArg Array.toList ho.symm), hc.2.2⟩

end Pickles.Application
