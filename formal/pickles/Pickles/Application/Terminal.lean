import Pickles.Application.Verify
import Pickles.Application.ProofCorrectness

/-!
# Terminal verification after a final Wrap proof

The terminal verifier recomputes the carried Step scalars and checks its deferred commitment
outside a circuit. Acceptance of the final Wrap proof either gives a satisfying Wrap execution
through certified compilation, or witnesses `KimchiFailure`. The execution supplies the group
check; no subsequent Step execution is assumed. The carried commitment is bound to the Wrap
witness by its public message digest; a disagreement exhibits a message-hash collision.

This completes verification of the reconstructed inner Step proof. Agreement with a native
terminal verifier, reconstruction of the application statement, and whole-chain soundness
are separate results.
-/

namespace Pickles.Application

open Snarky Snarky.Kimchi Bulletproof Bulletproof.Ipa Kimchi.Verifier CompElliptic.Fields.Pasta
open Poseidon.FqSponge
open scoped Kimchi

variable {D : Shape}

/-- Value-level terminal Wrap public input. -/
private def terminalPacked {k : ℕ} (dv : DeferredValues k Prechallenge Fp)
    (digest : Fp) (wrapDigest : Fq) (stepDigest : Fp) (branchData : Fq) :
    StatementPacked k (Type1 Fq) Fq :=
  let shift (x : Fp) : Type1 Fq := ⟨redFq (Pasta.Shifted.shiftType1 255 x)⟩
  let pre (x : SizedF 128 Prechallenge) : Fq := (x.val.val : Fq)
  { fpFields := #v[shift dv.combinedInnerProduct, shift dv.b, shift dv.plonk.zetaToSrsLength,
      shift dv.plonk.zetaToDomainSize, shift dv.plonk.perm]
    challenges := #v[pre dv.plonk.beta, pre dv.plonk.gamma]
    scalarChallenges := #v[pre dv.plonk.alpha, pre dv.plonk.zeta, pre dv.xi]
    digests := #v[redFq digest, wrapDigest, redFq stepDigest]
    bulletproofChallenges := dv.bulletproofChallenges.map pre
    branchData := branchData
    featureFlags := Vector.replicate 8 0
    lookupOptFlag := 0
    lookupOptScalarChallenge := 0 }

private theorem wrapDecode_shift {V : Valuation Fq} {c : Type1 (FVar Fq)} {x : Fp}
    (h : c.val.val V = redFq (Pasta.Shifted.shiftType1 255 x)) :
    (wrapSide V).decode c = x := by
  simp only [wrapSide, wrapDecode, h, val_redFq, ZMod.natCast_zmod_val]
  exact Pasta.Shifted.unshiftType1_shiftType1 (by decide : (2 : Fp) ≠ 0) 255 x

/-- Packed public-input agreement fixes every deferred scalar claim. -/
private theorem terminalPacked_dvReads {k : ℕ} {V : Valuation Fq}
    (stmt : StatementPacked k (Type1 (FVar Fq)) (FVar Fq))
    (dv : DeferredValues k Prechallenge Fp)
    (digest : Fp) (wrapDigest : Fq) (stepDigest : Fp) (branchData : Fq)
    (h : CircuitType.Reads V stmt (terminalPacked dv digest wrapDigest stepDigest branchData)) :
    DvReads V (wrapSide V).decode stmt.claims.deferredValues dv := by
  simp only [CircuitType.reads_ofEquiv, StatementPacked.equivProd, Equiv.coe_fn_mk,
    CircuitType.reads_prod, CircuitType.reads_vector] at h
  obtain ⟨hfp, hch, hsc, hdg, hbp, -⟩ := h
  simp only [CircuitType.reads_fvar] at hfp hch hsc hdg hbp
  have f0 := hfp 0 (by decide)
  have f1 := hfp 1 (by decide)
  have f2 := hfp 2 (by decide)
  have f3 := hfp 3 (by decide)
  have f4 := hfp 4 (by decide)
  have c0 := hch 0 (by decide)
  have c1 := hch 1 (by decide)
  have s0 := hsc 0 (by decide)
  have s1 := hsc 1 (by decide)
  have s2 := hsc 2 (by decide)
  simp only [terminalPacked, Type1.equivCarrier, Equiv.coe_fn_mk] at f0 f1 f2 f3 f4
  simp only [terminalPacked] at c0 c1 s0 s1 s2
  refine ⟨s0, c0, c1, s1, wrapDecode_shift f4, wrapDecode_shift f2,
    wrapDecode_shift f3, wrapDecode_shift f0, s2, ?_, wrapDecode_shift f1⟩
  intro i
  have hi := hbp i i.isLt
  simp only [Reads128, StatementPacked.claims, Fin.getElem_fin, Vector.getElem_map]
  simpa only [terminalPacked, Fin.getElem_fin, Vector.getElem_map] using hi

/-- The terminal digest uses the same cross-field conversion as the group verifier. -/
private theorem terminalPacked_digest {k : ℕ} {V : Valuation Fq}
    (stmt : StatementPacked k (Type1 (FVar Fq)) (FVar Fq))
    (dv : DeferredValues k Prechallenge Fp)
    (digest : Fp) (wrapDigest : Fq) (stepDigest : Fp) (branchData : Fq)
    (h : CircuitType.Reads V stmt (terminalPacked dv digest wrapDigest stepDigest branchData)) :
    castDigest IpaVesta.curve (stmt.claims.spongeDigestBeforeEvaluations.val V) = digest := by
  simp only [CircuitType.reads_ofEquiv, StatementPacked.equivProd, Equiv.coe_fn_mk,
    CircuitType.reads_prod, CircuitType.reads_vector] at h
  have hd := h.2.2.2.1 0 (by decide)
  simp only [CircuitType.reads_fvar, terminalPacked] at hd
  change stmt.digests[0].val V = redFq digest at hd
  change castDigest IpaVesta.curve (stmt.digests[0].val V) = digest
  rw [hd]
  simp only [castDigest, val_redFq, if_pos (ZMod.val_lt digest), ZMod.natCast_zmod_val]

/-- Packed public-input agreement fixes the outgoing Wrap-message digest. -/
private theorem terminalPacked_wrapDigest {k : ℕ} {V : Valuation Fq}
    (stmt : StatementPacked k (Type1 (FVar Fq)) (FVar Fq))
    (dv : DeferredValues k Prechallenge Fp)
    (digest : Fp) (wrapDigest : Fq) (stepDigest : Fp) (branchData : Fq)
    (h : CircuitType.Reads V stmt (terminalPacked dv digest wrapDigest stepDigest branchData)) :
    stmt.digests[1].val V = wrapDigest := by
  simp only [CircuitType.reads_ofEquiv, StatementPacked.equivProd, Equiv.coe_fn_mk,
    CircuitType.reads_prod, CircuitType.reads_vector] at h
  exact CircuitType.reads_fvar.mp (h.2.2.2.1 1 (by decide))

/-- Equal wrap digests fix the commitment unless their absorbed inputs collide. -/
private theorem wrapMsgDigest_sg_eq_or_collision {w k : ℕ}
    (p : Poseidon.Params Fq) (dummy : Vector Fq k)
    (m m' : MessagesForNextWrapProof (AffinePoint Fq) (Vector (Vector Fq k) w))
    (h : wrapMsgDigest p dummy m = wrapMsgDigest p dummy m') :
    m.challengePolynomialCommitment = m'.challengePolynomialCommitment ∨
      Collision p (wrapMsgInput dummy m) (wrapMsgInput dummy m') := by
  by_cases hi : wrapMsgInput dummy m = wrapMsgInput dummy m'
  · left
    have hsg := (List.append_inj' hi rfl).2
    have hc : m.challengePolynomialCommitment.x = m'.challengePolynomialCommitment.x ∧
        m.challengePolynomialCommitment.y = m'.challengePolynomialCommitment.y := by
      simpa only [List.cons.injEq, and_true] using hsg
    cases m with | mk sg ch =>
      cases m' with | mk sg' ch' =>
        cases sg
        cases sg'
        simpa only [AffinePoint.mk.injEq] using hc
  · right
    apply Collision.of_length_eq (by simp [wrapMsgInput]) hi
    simpa only [Poseidon.RandomOracle.hash_eq_squeeze] using h

private instance (D : Shape) : NeZero D.branches := ⟨Nat.ne_of_gt D.branches_pos⟩

/-- Every constraint of the Wrap body is present in the satisfying compiled execution. -/
private theorem WrapRun.terminal_body_holds {C : Circuits D} (r : WrapRun C) :
    ∀ con ∈ (build (wrapMain (c := Builder r.V (KimchiConstraint Fq))
      (FopParams.of IpaPallas.curve 1 WrapIPARounds Linearization.fqTokens)
      D.widths (stepDomainLog2s C.wiring.stepKeys) (stepKeyCells C.wiring.stepKeys)
      C.wiring.pins C.stepLagrange C.setup.step.h C.setup.dummy D.wrapWidths r.advice
      wrapStatement)
      (bodyStart (F := Fq) (c := Builder r.V (KimchiConstraint Fq))
        (a := StatementPacked StepIPARounds (Type1 Fq) Fq))).constraints,
      ConstraintHolds.Holds r.V con := fun con hc =>
    r.holds con (mem_compileWith_wrapMainCircuit _ _ _ _ _ _ _ _ _ _ hc)

set_option cleanup.letToHave false in
/-- A satisfying Wrap execution supplies the successful group half of its inner Step proof. -/
private theorem WrapRun.terminal_group {C : Circuits D} (r : WrapRun C) (b : D.Branch)
    (hAssumptions : WrapStepAssumptions C b)
    (hb : r.cells.1.whichBranch.val r.V = (b : Fq))
    (cp : KimchiProof IpaVesta.curve C.wiring.backend.stepChunks StepIPARounds)
    (oldsW : Vector (IpaVesta.curve.Point × Bool) D.width)
    (hproof : ProofReads (wrapSide r.V) r.cells.2.cells.wComm r.cells.2.cells.zComm
      r.cells.2.cells.tComm r.cells.2.cells.opening cp)
    (holds : OldsRead r.V r.cells.2.cells.sgOld cp oldsW) :
    ∃ success : BoolVar Fq,
      GroupHalf.Reads C.setup.stepSrs C.wiring.backend.stepKeys[b] cp
        (wrapPublicInput C.setup.stepSrs C.wiring.backend.stepKeys[b] r.V
          r.cells.2.statement)
        (GroupHalf.wrap r.V wrapStatement.claims) success ∧
      (↑success : CVar Fq).val r.V = 1 := by
  have hg := (builder_spec_iff _ _).mp
    (wrapMain_verifyReads C.setup.wrapSrs C.setup.stepSrs
      C.wiring.backend.stepKeys[b] (C.wiring.valid.stepChunks b) r.V D.widths
      (stepDomainLog2s C.wiring.stepKeys) (stepKeyCells C.wiring.stepKeys)
      C.wiring.pins C.stepLagrange C.setup.step.h C.setup.dummy D.wrapWidths r.advice
      wrapStatement D.width_le C.wiring.valid.branches_le rfl
      hAssumptions.points_ne hAssumptions.avoids) _ r.terminal_body_holds
  have hc : r.cells = _ := compileWith_wrapMainCircuit_cells
    (V := r.V) (FopParams.of IpaPallas.curve 1 WrapIPARounds Linearization.fqTokens)
    D.widths (stepDomainLog2s C.wiring.stepKeys) (stepKeyCells C.wiring.stepKeys)
    C.wiring.pins C.stepLagrange C.setup.step.h C.setup.dummy D.wrapWidths r.advice
  rw [hc] at hb hproof holds ⊢
  exact (hg b hb
    (by simp [stepKeyCells, Wiring.stepKeys])
    (by simpa [stepDomainLog2s, Wiring.stepKeys] using hAssumptions.lagrange)).2.2.2
      cp oldsW hproof holds

/-- The inner Step proof's commitments and opening cells retained by Wrap. -/
private def WrapRun.proofCells {C : Circuits D} (r : WrapRun C) :
    IvpProof StepIPARounds C.wiring.backend.stepChunks (FVar Fq) (Type1 (FVar Fq)) :=
  ⟨r.cells.2.cells.wComm, r.cells.2.cells.zComm, r.cells.2.cells.tComm,
    r.cells.2.cells.opening⟩

open CompElliptic.CurveForms.ShortWeierstrass in
set_option cleanup.letToHave false in
/-- The retained proof and old-accumulator cells are the allocated, checked curve points. -/
private theorem WrapRun.terminal_cells {C : Circuits D} (r : WrapRun C) :
    (∀ j : Fin D.width, OnCurve IpaVesta.curve.E.A IpaVesta.curve.E.B
      (r.cells.1.stepAccs[j].pt.x.val r.V, r.cells.1.stepAccs[j].pt.y.val r.V)) ∧
    r.cells.2.cells = ivpInputOf wrapStatement.claims.deferredValues
      r.cells.1.sgOld r.cells.1.key r.proofCells ∧
    (∀ p ∈ r.proofCells.points,
      OnCurve IpaVesta.curve.E.A IpaVesta.curve.E.B (p.x.val r.V, p.y.val r.V)) := by
  have h := (builder_spec_iff _ _).mp
    (wrapMain_cells
      (FopParams.of IpaPallas.curve 1 WrapIPARounds Linearization.fqTokens)
      r.V D.widths (stepDomainLog2s C.wiring.stepKeys) (stepKeyCells C.wiring.stepKeys)
      C.wiring.pins C.stepLagrange C.setup.step.h C.setup.dummy D.wrapWidths r.advice
      wrapStatement) _ r.terminal_body_holds
  have hc : r.cells = _ := compileWith_wrapMainCircuit_cells
    (V := r.V) (FopParams.of IpaPallas.curve 1 WrapIPARounds Linearization.fqTokens)
    D.widths (stepDomainLog2s C.wiring.stepKeys) (stepKeyCells C.wiring.stepKeys)
    C.wiring.pins C.stepLagrange C.setup.step.h C.setup.dummy D.wrapWidths r.advice
  erw [← hc] at h
  obtain ⟨hacc, pr, hcells, hon⟩ := h
  have hp : r.proofCells = pr := by
    simp only [proofCells, hcells, ivpInputOf]
  exact ⟨hacc, hp ▸ hcells, hp ▸ hon⟩

/-- The old commitment points and the keep bits selected by the Step branch. -/
private def WrapRun.terminalOldsW {C : Circuits D} (r : WrapRun C) (b : D.Branch) :
    Vector (IpaVesta.curve.Point × Bool) D.width :=
  Vector.ofFn fun j ↦ (readPt (C := IpaVesta.curve) r.V r.cells.1.stepAccs[j].pt,
    decide (D.width - D.slots b ≤ j.val))

/-- The Step proof's old accumulators, pairing kept Wrap cells with carried Step challenges. -/
private def WrapRun.terminalOlds {C : Circuits D} (r : WrapRun C) (b : D.Branch)
    (challenges : Vector (Vector Fp StepIPARounds) D.width) :
    Array (Accumulator IpaVesta.curve StepIPARounds) :=
  (((List.finRange D.width).filter fun j ↦ decide (D.width - D.slots b ≤ j.val)).map
    fun j ↦ (⟨readPt r.V r.cells.1.stepAccs[j].pt, challenges[j]⟩ :
      Accumulator IpaVesta.curve StepIPARounds)).toArray

/-- The inner Step proof reconstructed from Wrap cells and its carried scalar data. -/
private def WrapRun.terminalProof {C : Circuits D} (r : WrapRun C) (b : D.Branch)
    (evals : ProofEvaluations (Vector Fp C.wiring.backend.stepChunks))
    (pubEvals : PubEvalSrc IpaVesta.curve C.wiring.backend.stepChunks) (ftEval1 : Fp)
    (challenges : Vector (Vector Fp StepIPARounds) D.width) :
    KimchiProof IpaVesta.curve C.wiring.backend.stepChunks StepIPARounds :=
  r.proofCells.read (wrapSide r.V) evals pubEvals ftEval1 (r.terminalOlds b challenges)

set_option cleanup.letToHave false in
/-- The reconstructed Step proof agrees with the retained proof and old-accumulator cells. -/
private theorem WrapRun.terminal_proofReads {C : Circuits D} (r : WrapRun C) (b : D.Branch)
    (hmask : CircuitType.Reads r.V r.cells.1.mask
      (Vector.ofFn fun i : Fin D.width ↦ decide (i.val < D.slots b)))
    (evals : ProofEvaluations (Vector Fp C.wiring.backend.stepChunks))
    (pubEvals : PubEvalSrc IpaVesta.curve C.wiring.backend.stepChunks) (ftEval1 : Fp)
    (challenges : Vector (Vector Fp StepIPARounds) D.width) :
    let cp := r.terminalProof b evals pubEvals ftEval1 challenges
    ProofReads (wrapSide r.V) r.cells.2.cells.wComm r.cells.2.cells.zComm
      r.cells.2.cells.tComm r.cells.2.cells.opening cp ∧
    OldsRead r.V r.cells.2.cells.sgOld cp (r.terminalOldsW b) := by
  intro cp
  obtain ⟨hacc, hcells, hon⟩ := r.terminal_cells
  constructor
  · exact IvpProof.read_proofReads (wrapSide r.V) r.proofCells evals pubEvals ftEval1
      (r.terminalOlds b challenges) hon
  · rw [hcells]
    apply OldsRead.of_readPt
    · intro m hm
      simp only [ivpInputOf, WrapMainFinalizeOut.sgOld, Vector.mem_toList_iff,
        Vector.mem_ofFn] at hm
      obtain ⟨j, rfl⟩ := hm
      exact hacc j
    · ext j
      simp [ivpInputOf, WrapMainFinalizeOut.sgOld, terminalOldsW]
    · intro j
      simp only [ivpInputOf, WrapMainFinalizeOut.sgOld, Fin.getElem_fin,
        Vector.getElem_ofFn, terminalOldsW]
      have h := CircuitType.reads_boolVar.mp
        (CircuitType.reads_vector.mp hmask (D.width - 1 - j) (by omega))
      simp only [Vector.getElem_ofFn] at h
      rw [Vector.getElem_reverse, h]
      congr 1
      simp only [decide_eq_decide]
      omega
    · simp [cp, terminalProof, IvpProof.read, terminalOlds, terminalOldsW,
        Vector.toList_ofFn, List.ofFn_eq_map, List.filter_map, Function.comp_def]

/-- The reconstructed Step proof has the accumulator count and input size of its branch key. -/
private theorem WrapRun.terminal_guards {C : Circuits D} (r : WrapRun C) (b : D.Branch)
    (evals : ProofEvaluations (Vector Fp C.wiring.backend.stepChunks))
    (pubEvals : PubEvalSrc IpaVesta.curve C.wiring.backend.stepChunks) (ftEval1 : Fp)
    (challenges : Vector (Vector Fp StepIPARounds) D.width) :
    Guards IpaVesta.curve C.wiring.backend.stepKeys[b]
      (r.terminalProof b evals pubEvals ftEval1 challenges)
      (wrapPublicInput C.setup.stepSrs C.wiring.backend.stepKeys[b] r.V
        r.cells.2.statement) := by
  have hlayout : StepKeyLayout C.wiring.backend.stepKeys[b] D.width (D.slots b) := by
    simpa [Wiring.stepKeys, Shape.widths] using C.wiring.step_key_layout b
  constructor
  · rw [hlayout.prevChallenges_eq]
    have hlen := WrapStep.consumedAccumulators_length r.V (fun _ ↦ 0) r.cells.1
      (Vector.replicate D.width (Vector.replicate StepIPARounds (.const 0 : FVar Fp))) rfl
      (Vector.ofFn fun j : Fin D.width ↦ decide (D.width - D.slots b ≤ j.val))
      (⟨D.slots b, Nat.lt_succ_of_le (D.slots_le_width b)⟩ : Fin (D.width + 1))
      (by intro j hj; simp)
    simpa [terminalProof, IvpProof.read, terminalOlds, WrapStep.consumedAccumulators] using hlen
  · rw [hlayout.publicCount_eq, wrapPublicInput_size]

set_option cleanup.letToHave false in
/-- A satisfying Wrap execution selects a branch whose width and domain match the public data. -/
private theorem WrapRun.terminal_branchData {C : Circuits D} (r : WrapRun C) :
    ∃ b : D.Branch,
      r.cells.1.whichBranch.val r.V = (b : Fq) ∧
      CircuitType.Reads r.V r.cells.1.mask
        (Vector.ofFn fun i : Fin D.width ↦ decide (i.val < D.slots b)) ∧
      wrapStatement.branchData.val r.V =
        4 * (C.wiring.backend.stepKeys[b].domainLog2 : Fq) +
          ((List.range D.width).map fun i ↦
            ((2 ^ (1 - i) : ℕ) : Fq) * bit (decide (i < D.slots b))).sum := by
  obtain ⟨b, hb, hbranch, _, hmask, _, hbd, _⟩ := (builder_spec_iff _ _).mp
    (wrapMain_reads C.setup.wrapSrs r.V D.widths
      (stepDomainLog2s C.wiring.stepKeys) (stepKeyCells C.wiring.stepKeys)
      C.wiring.pins C.stepLagrange C.setup.step.h C.setup.dummy D.wrapWidths r.advice
      wrapStatement D.width_le C.wiring.valid.branches_le) _ r.terminal_body_holds
  refine ⟨⟨b, hb⟩, ?_, ?_, ?_⟩
  · dsimp only [WrapRun.cells, Circuits.wrapBuilt, Circuits.wrapCircuit]
    erw [compileWith_wrapMainCircuit_cells (V := r.V)]
    exact hbranch
  · dsimp only [WrapRun.cells, Circuits.wrapBuilt, Circuits.wrapCircuit]
    erw [compileWith_wrapMainCircuit_cells (V := r.V)]
    simpa [Shape.widths] using hmask
  · simpa [stepDomainLog2s, Wiring.stepKeys, Shape.widths] using hbd

set_option cleanup.letToHave false in
/-- A satisfying Wrap execution binds its outgoing and reconstructed incoming messages. -/
private theorem WrapRun.terminal_hashes {C : Circuits D} (r : WrapRun C) :
    r.cells.2.HashesMessages r.V C.setup.dummy wrapStatement r.cells.1 := by
  have h := ((builder_spec_iff _ _).mp
    (wrapMain_statement
      (FopParams.of IpaPallas.curve 1 WrapIPARounds Linearization.fqTokens)
      r.V D.widths (stepDomainLog2s C.wiring.stepKeys) (stepKeyCells C.wiring.stepKeys)
      C.wiring.pins C.stepLagrange C.setup.step.h C.setup.dummy D.wrapWidths r.advice
      wrapStatement C.wiring.backend.stepKeys[(⟨0, D.branches_pos⟩ : D.Branch)].nc_pos)
      _ r.terminal_body_holds).2.2.2.2
  dsimp only [WrapRun.cells, Circuits.wrapBuilt, Circuits.wrapCircuit]
  erw [compileWith_wrapMainCircuit_cells (V := r.V)]
  exact h

/-- The outgoing Wrap digest binds the inner Step commitment and the finalized Wrap challenges. -/
private theorem WrapRun.terminal_messageHash {C : Circuits D} (r : WrapRun C) :
    wrapStatement.digests[1].val r.V =
      wrapMsgDigest IpaVesta.curve.sponge.params C.setup.dummy
        ⟨readPoint r.V r.cells.2.cells.opening.sg,
          (r.cells.1.outs.map (·.expandedChallenges)).map (·.map (·.val r.V))⟩ := by
  apply r.terminal_hashes.1
  · exact reads_affinePoint.mpr ⟨rfl, rfl⟩
  · apply CircuitType.reads_vector.mpr
    intro i hi
    rw [Vector.getElem_map]
    apply CircuitType.reads_vector.mpr
    intro j hj
    simp only [Vector.getElem_map]
    exact CircuitType.reads_fvar.mpr rfl

/-- A terminal message's affine coordinates interpreted as a group point. -/
def terminalSg (sg : AffinePoint Fq) : IpaVesta.curve.Point :=
  readPt (fun _ ↦ 0) ⟨.const sg.x, .const sg.y⟩

/-- Binding the message's affine coordinates also binds the group's interpreted point. -/
private theorem terminalSg_of_readPoint {V : Valuation Fq} (cells : AffinePoint (FVar Fq))
    (sg : AffinePoint Fq) (h : readPoint V cells = sg) :
    readPt (C := IpaVesta.curve) V cells = terminalSg sg := by
  have hx : cells.x.val V = sg.x := congrArg AffinePoint.x h
  have hy : cells.y.val V = sg.y := congrArg AffinePoint.y h
  simp only [readPt, terminalSg, CVar.val, hx, hy]

/-- Data carried alongside the final Wrap proof, independent of any circuit witness. -/
structure TerminalData (C : Circuits D) where
  /-- The Step scalar claims packed into the Wrap public input. -/
  deferred : DeferredValues StepIPARounds Prechallenge Fp
  /-- The Step group transcript's digest, before absorbing evaluations. -/
  spongeDigest : Fp
  /-- The Step polynomial evaluations supplied to scalar recomputation. -/
  evals : ChunkedEvals C.wiring.backend.stepChunks Fp
  /-- Old Step IPA challenges, including the unused prefix before the active suffix. -/
  oldChallenges : Vector (Vector Fp StepIPARounds) D.width
  /-- The number of predecessor entries in the unpadded Step message. -/
  width : Fin (D.width + 1)
  /-- The application statement, encoded as its input fields followed by its output fields. -/
  appState : Vector Fp D.schema.size
  /-- The unpadded commitment points in the Step message. -/
  prevSgs : Vector (AffinePoint Fp) width.val
  /-- The outgoing message: this Step's commitment and the prior Wrap challenges. -/
  message : MessagesForNextWrapProof (AffinePoint Fq)
    (Vector (Vector Fq WrapIPARounds) D.width)
  /-- The selected Step domain and predecessor mask, packed as in Wrap. -/
  branchData : Fq

/-- The complete Step message, with the application's key and the active challenge suffix. -/
def TerminalData.stepMessage {C : Circuits D} (d : TerminalData C) :
    MessagesForNextStepProof (VkComms 1 (AffinePoint Fp)) (Vector Fp D.schema.size)
      (Vector (AffinePoint Fp) d.width.val) (Vector (Vector Fp StepIPARounds) d.width.val) where
  appState := d.appState
  dlogPlonkIndex := C.wiring.backend.wrapKey.comms.map fun p ↦ ⟨p.x, p.y⟩
  challengePolynomialCommitments := d.prevSgs
  oldBulletproofChallenges := (d.oldChallenges.drop (D.width - d.width.val)).cast
    (Nat.sub_sub_self (Nat.le_of_lt_succ d.width.isLt))

/-- Recompute the Step digest from the carried message and the application's own Wrap key. -/
def TerminalData.stepDigest {C : Circuits D} (d : TerminalData C) : Fp :=
  stepMsgDigest IpaPallas.curve.sponge.params d.stepMessage

/-- The final Wrap proof's old accumulators, reconstructed from the carried messages.
Step supplies their points and Wrap their challenges; both are front-padded to protocol width. -/
def TerminalData.wrapAccumulators {C : Circuits D} (d : TerminalData C) :
    Vector (Accumulator IpaPallas.curve WrapIPARounds) MaxProofsVerified :=
  let sgs : Vector IpaPallas.curve.Point MaxProofsVerified :=
    (Vector.replicate (MaxProofsVerified - d.width.val) C.setup.dummySg ++
      d.prevSgs.map (fun sg ↦
        readPt (C := IpaPallas.curve) (fun _ ↦ 0) ⟨.const sg.x, .const sg.y⟩)).cast
      (Nat.sub_add_cancel ((Nat.le_of_lt_succ d.width.isLt).trans D.width_le))
  let challenges : Vector (Vector Fq WrapIPARounds) MaxProofsVerified :=
    (Vector.replicate (MaxProofsVerified - D.width) C.setup.dummy ++
      d.message.oldBulletproofChallenges).cast (Nat.sub_add_cancel D.width_le)
  sgs.zipWith (fun sg u ↦ ⟨sg, u⟩) challenges

/-- The final Wrap public statement determined by the carried data. -/
def TerminalData.statement {C : Circuits D} (d : TerminalData C) : WrapPublic :=
  terminalPacked d.deferred d.spongeDigest
    (wrapMsgDigest IpaVesta.curve.sponge.params C.setup.dummy d.message)
    d.stepDigest d.branchData

/-- The domain and mask that Wrap publicly binds for a selected branch. -/
def terminalBranchData (C : Circuits D) (b : D.Branch) : Fq :=
  4 * (C.wiring.backend.stepKeys[b].domainLog2 : Fq) +
    ((List.range D.width).map fun i ↦
      ((2 ^ (1 - i) : ℕ) : Fq) * bit (decide (i < D.slots b))).sum

/-- The scalar half uses only the active suffix of old Step accumulators. -/
def TerminalData.activeChallenges {C : Circuits D} (d : TerminalData C)
    (b : D.Branch) : Array (Vector Fp StepIPARounds) :=
  (((List.finRange D.width).filter fun j ↦ decide (D.width - D.slots b ≤ j.val)).map
    fun j ↦ d.oldChallenges[j]).toArray

/-- The Step proof read from a certified Wrap witness and the carried scalar data. -/
def TerminalData.proof {C : Circuits D} (d : TerminalData C)
    (r : WrapRun C) (b : D.Branch) :=
  r.terminalProof b d.evals.evals (.carried d.evals.pub) d.evals.ftEval1 d.oldChallenges

/-- A collision between the Wrap witness's outgoing message and the supplied message. -/
def TerminalData.Collision {C : Circuits D} (d : TerminalData C) (r : WrapRun C) : Prop :=
  Pickles.Collision IpaVesta.curve.sponge.params
    (wrapMsgInput C.setup.dummy
      ⟨readPoint r.V r.cells.2.cells.opening.sg,
        (r.cells.1.outs.map (·.expandedChallenges)).map (·.map (·.val r.V))⟩)
    (wrapMsgInput C.setup.dummy d.message)

private theorem TerminalData.branchData_reads {C : Circuits D} (d : TerminalData C)
    (r : WrapRun C) (h : CircuitType.Reads r.V wrapStatement d.statement) :
    wrapStatement.branchData.val r.V = d.branchData := by
  simp only [CircuitType.reads_ofEquiv, StatementPacked.equivProd, Equiv.coe_fn_mk,
    CircuitType.reads_prod, CircuitType.reads_vector] at h
  exact CircuitType.reads_fvar.mp h.2.2.2.2.2.1

private theorem TerminalData.proof_oldChallenges {C : Circuits D} (d : TerminalData C)
    (r : WrapRun C) (b : D.Branch) :
    (d.proof r b).olds.map (·.u) = d.activeChallenges b := by
  simp [proof, WrapRun.terminalProof, IvpProof.read, WrapRun.terminalOlds,
    activeChallenges, List.map_map, Function.comp_def]

private theorem TerminalData.commitment_eq_or_collision {C : Circuits D}
    (d : TerminalData C) (r : WrapRun C)
    (h : CircuitType.Reads r.V wrapStatement d.statement) (b : D.Branch) :
    (d.proof r b).opening.sg = terminalSg d.message.challengePolynomialCommitment ∨
      d.Collision r := by
  have hd := terminalPacked_wrapDigest wrapStatement d.deferred d.spongeDigest
    (wrapMsgDigest IpaVesta.curve.sponge.params C.setup.dummy d.message)
    d.stepDigest d.branchData h
  have he := r.terminal_messageHash.symm.trans hd
  obtain hs | hc := wrapMsgDigest_sg_eq_or_collision
    IpaVesta.curve.sponge.params C.setup.dummy _ d.message he
  · left
    exact terminalSg_of_readPoint r.cells.2.cells.opening.sg _ hs
  · exact Or.inr hc

/-- The terminal checks are equalities on carried values. The public input fixes a domain
and mask, not a branch identity, so the scalar check is stated for each compatible key.
There is no assumed group check, inner proof acceptance, or subsequent circuit execution. -/
structure TerminalData.Checks {C : Circuits D} (d : TerminalData C) : Prop where
  /-- Recompute the deferred scalars for the Step domain and active old accumulators. -/
  scalars : ∀ b : D.Branch, d.branchData = terminalBranchData C b →
    terminalScalarChecks IpaVesta.curve C.wiring.backend.stepKeys[b]
      d.deferred d.spongeDigest d.evals (d.activeChallenges b)
  /-- Check the remaining Step opening commitment directly. -/
  sg : terminalSg d.message.challengePolynomialCommitment =
    msm IpaVesta.curve C.setup.stepSrs.g
      (bPolyCoefficients fun i ↦
        endoExpand IpaVesta.curve.lam d.deferred.bulletproofChallenges[i].val.val)

/-- Wrap satisfaction supplies the inner Step group check. Scalar recomputation and the
terminal commitment check finish that proof, unless the carried message's digest collides
with the message read from the Wrap witness. No further Step circuit is needed. -/
private theorem WrapRun.terminal_verifies {C : Circuits D} (r : WrapRun C)
    (d : TerminalData C) (hreads : CircuitType.Reads r.V wrapStatement d.statement)
    (hsetup : ∀ b : D.Branch, WrapStepAssumptions C b) (hchecks : d.Checks) :
    ∃ b : D.Branch, r.cells.1.whichBranch.val r.V = (b : Fq) ∧
      (kimchiVerify IpaVesta.curve C.setup.stepSrs C.wiring.backend.stepKeys[b]
        (d.proof r b)
        (wrapPublicInput C.setup.stepSrs C.wiring.backend.stepKeys[b] r.V
          r.cells.2.statement) = true ∨ d.Collision r) := by
  obtain ⟨b, hb, hmask, hbranch⟩ := r.terminal_branchData
  refine ⟨b, hb, ?_⟩
  obtain hsg | hcollision := d.commitment_eq_or_collision r hreads b
  · left
    obtain ⟨hproof, holds⟩ := r.terminal_proofReads b hmask
      d.evals.evals (.carried d.evals.pub) d.evals.ftEval1 d.oldChallenges
    obtain ⟨success, hg, hs⟩ := r.terminal_group b (hsetup b) hb
      (d.proof r b) (r.terminalOldsW b) hproof holds
    have hdv := terminalPacked_dvReads wrapStatement d.deferred d.spongeDigest
      (wrapMsgDigest IpaVesta.curve.sponge.params C.setup.dummy d.message)
      d.stepDigest d.branchData hreads
    have hdigest := terminalPacked_digest wrapStatement d.deferred d.spongeDigest
      (wrapMsgDigest IpaVesta.curve.sponge.params C.setup.dummy d.message)
      d.stepDigest d.branchData hreads
    apply terminal_kimchiVerify C.setup.stepSrs C.wiring.backend.stepKeys[b]
      (d.proof r b) _ (GroupHalf.wrap r.V wrapStatement.claims) success hg hs
      (by change 2 ^ 128 < PALLAS_SCALAR_CARD; norm_num [PALLAS_SCALAR_CARD])
      (r.terminal_guards b d.evals.evals (.carried d.evals.pub)
        d.evals.ftEval1 d.oldChallenges)
      d.deferred hdv d.spongeDigest hdigest.symm d.evals rfl rfl rfl
      (d.activeChallenges b) (d.proof_oldChallenges r b)
      (hchecks.scalars b ((d.branchData_reads r hreads).symm.trans hbranch))
    exact hsg.trans hchecks.sg
  · exact Or.inr hcollision

/-- Terminal acceptance closes the final Step proof's outstanding work, or witnesses Kimchi
failure at the final Wrap proof. In the satisfying-execution case, certified compilation
supplies the group check, while `checks` supplies scalar recomputation and the directly checked
commitment. A mismatched carried commitment exhibits a collision. -/
theorem terminal_kimchiVerify {C : Circuits D} (cert : ApplicationCertified C)
    (p : KimchiProof IpaPallas.curve 1 WrapIPARounds) (d : TerminalData C)
    (haccept : kimchiVerify IpaPallas.curve C.setup.wrapSrs C.wiring.backend.wrapKey
      { p with olds := d.wrapAccumulators.toArray }
      (CircuitType.valueToFields d.statement).toArray = true)
    (checks : d.Checks) :
    (∃ r : WrapRun C, CircuitType.Reads r.V wrapStatement d.statement ∧
      ∃ b : D.Branch, r.cells.1.whichBranch.val r.V = (b : Fq) ∧
        (kimchiVerify IpaVesta.curve C.setup.stepSrs C.wiring.backend.stepKeys[b]
          (d.proof r b)
          (wrapPublicInput C.setup.stepSrs C.wiring.backend.stepKeys[b] r.V
            r.cells.2.statement) = true ∨ d.Collision r)) ∨
      KimchiFailure C.setup.wrapSrs cert.wrap.index C.wiring.backend.wrapKey
        { p with olds := d.wrapAccumulators.toArray }
        ((CircuitType.valueToFields d.statement).cast cert.indices.wrapPublicCount.symm) := by
  obtain ⟨V, holds, hreads⟩ | failure := cert.wrap_valuation_or_failure
    { p with olds := d.wrapAccumulators.toArray } d.statement haccept
  · let r : WrapRun C := ⟨V, inertWrapAdvice, holds⟩
    exact Or.inl ⟨r, hreads, r.terminal_verifies d hreads cert.wrapStepSetup checks⟩
  · exact Or.inr failure

/-- The inner Step public input encodes the statement decoded from the Wrap execution. -/
private theorem WrapRun.terminal_publicInput {C : Circuits D} (r : WrapRun C)
    (b : D.Branch) :
    (CircuitType.valueToFields (F := Fp)
      (StepStatement.ofWrap r.V r.cells.2.statement)).toArray =
      wrapPublicInput C.setup.stepSrs C.wiring.backend.stepKeys[b] r.V
        r.cells.2.statement := by
  apply Array.toList_inj.mp
  apply StepStatement.ofWrap_toFields
  have h := ((builder_spec_iff _ _).mp
    (wrapMain_statement
      (FopParams.of IpaPallas.curve 1 WrapIPARounds Linearization.fqTokens)
      r.V D.widths (stepDomainLog2s C.wiring.stepKeys) (stepKeyCells C.wiring.stepKeys)
      C.wiring.pins C.stepLagrange C.setup.step.h C.setup.dummy D.wrapWidths r.advice
      wrapStatement C.wiring.backend.stepKeys[b].nc_pos)
      _ r.terminal_body_holds).2.2.1
  dsimp only [WrapRun.cells, Circuits.wrapBuilt, Circuits.wrapCircuit]
  erw [compileWith_wrapMainCircuit_cells (V := r.V)]
  simpa only [Vector.mem_toList_iff] using h

/-- Terminal acceptance supplies a satisfying Step/Wrap pair connected at its public
statement, or a carried-message collision or Kimchi failure at one of the two fixed SRSs. -/
theorem terminal_stepWrap {C : Circuits D} (cert : ApplicationCertified C)
    (p : KimchiProof IpaPallas.curve 1 WrapIPARounds) (d : TerminalData C)
    (haccept : kimchiVerify IpaPallas.curve C.setup.wrapSrs C.wiring.backend.wrapKey
      { p with olds := d.wrapAccumulators.toArray }
      (CircuitType.valueToFields d.statement).toArray = true)
    (checks : d.Checks) :
    (∃ r : WrapRun C, CircuitType.Reads r.V wrapStatement d.statement ∧
      ((∃ (b : D.Branch) (e : StepWrapLink C b), e.wrap = r) ∨ d.Collision r)) ∨
      SomeKimchiFailure C.setup.wrapSrs ∨ SomeKimchiFailure C.setup.stepSrs := by
  obtain ⟨r, hreads, b, hb, hstep⟩ | failure :=
    terminal_kimchiVerify cert p d haccept checks
  · obtain hstep | collision := hstep
    · rw [← r.terminal_publicInput b] at hstep
      obtain ⟨V, holds, hpublic⟩ | failure := cert.step_valuation_or_failure b (d.proof r b)
        (StepStatement.ofWrap r.V r.cells.2.statement) hstep
      · let step : StepRun C b := ⟨V, inertStepAdvice, holds⟩
        let e : StepWrapLink C b :=
          { step, wrap := r, branch := hb, publicInput := hpublic }
        exact Or.inl ⟨r, hreads, Or.inl ⟨b, e, rfl⟩⟩
      · exact Or.inr <| Or.inr ⟨_, _, _, _, _, _, failure⟩
    · exact Or.inl ⟨r, hreads, Or.inr collision⟩
  · exact Or.inr <| Or.inl ⟨_, _, _, _, _, _, failure⟩

private theorem chunks_injective {α : Type} {k : Nat} :
    ∀ {xs ys : List (Vector α k)}, xs.length = ys.length →
      (xs.flatMap Vector.toList) = ys.flatMap Vector.toList → xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hl, he => by
    obtain ⟨hxy, ht⟩ := List.append_inj he (by simp)
    rw [Vector.toList_inj.mp hxy, chunks_injective (by simpa using hl) ht]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

private theorem stepInput_length {n sa : Nat}
    (m : MessagesForNextStepProof (VkComms 1 (AffinePoint Fp)) (Vector Fp sa)
      (Vector (AffinePoint Fp) n) (Vector (Vector Fp StepIPARounds) n)) :
    (stepMsgInput m).length = 56 + sa + n * 18 := by
  simp [stepMsgInput, MessagesForNextStepProof.proofs, VkComms.indexPoints,
    VkComms.selectors, List.length_flatMap, StepIPARounds]
  omega

private theorem stepInput_eq_or_collision {n n' sa : Nat}
    (m : MessagesForNextStepProof (VkComms 1 (AffinePoint Fp)) (Vector Fp sa)
      (Vector (AffinePoint Fp) n) (Vector (Vector Fp StepIPARounds) n))
    (m' : MessagesForNextStepProof (VkComms 1 (AffinePoint Fp)) (Vector Fp sa)
      (Vector (AffinePoint Fp) n') (Vector (Vector Fp StepIPARounds) n'))
    (hh : stepMsgDigest IpaPallas.curve.sponge.params m =
      stepMsgDigest IpaPallas.curve.sponge.params m') :
    (n = n' ∧ stepMsgInput m = stepMsgInput m') ∨
      Collision IpaPallas.curve.sponge.params (stepMsgInput m) (stepMsgInput m') := by
  have hh' : Poseidon.RandomOracle.hash IpaPallas.curve.sponge.params (stepMsgInput m) =
      Poseidon.RandomOracle.hash IpaPallas.curve.sponge.params (stepMsgInput m') := by
    simpa only [Poseidon.RandomOracle.hash_eq_squeeze] using hh
  by_cases hn : n = n'
  · by_cases he : stepMsgInput m = stepMsgInput m'
    · exact Or.inl ⟨hn, he⟩
    · exact Or.inr (Collision.of_length_eq (by rw [stepInput_length, stepInput_length, hn])
        he hh')
  · apply Or.inr
    apply Collision.of_length_apart ?_ ?_ ?_ hh'
    · have := stepInput_length m; intro he; simp [he] at this; omega
    · have := stepInput_length m'; intro he; simp [he] at this; omega
    · rw [stepInput_length, stepInput_length]
      omega

private theorem stepInput_points {n n' sa : Nat}
    (m : MessagesForNextStepProof (VkComms 1 (AffinePoint Fp)) (Vector Fp sa)
      (Vector (AffinePoint Fp) n) (Vector (Vector Fp StepIPARounds) n))
    (m' : MessagesForNextStepProof (VkComms 1 (AffinePoint Fp)) (Vector Fp sa)
      (Vector (AffinePoint Fp) n') (Vector (Vector Fp StepIPARounds) n'))
    (hn : n = n') (he : stepMsgInput m = stepMsgInput m') (i : Fin n) :
    m.challengePolynomialCommitments[i] =
      m'.challengePolynomialCommitments[i.val]'(hn ▸ i.isLt) := by
  subst n'
  have htail := (List.append_inj he (by
    simp [VkComms.indexPoints, VkComms.selectors, List.length_flatMap])).2
  let chunk := fun q : AffinePoint Fp × Vector Fp StepIPARounds ↦
    (#v[q.1.x, q.1.y] ++ q.2)
  have hc : (m.proofs.toList.map chunk) = m'.proofs.toList.map chunk :=
    chunks_injective (by simp) (by simpa [chunk, List.flatMap_map, Function.comp_def] using htail)
  have hi := List.getElem_of_eq hc (i := i.val) (by simp)
  have hx := congrArg (fun v : Vector Fp (2 + StepIPARounds) ↦ v[0]) hi
  have hy := congrArg (fun v : Vector Fp (2 + StepIPARounds) ↦ v[1]) hi
  apply congrArg₂ AffinePoint.mk
  · simpa [chunk, MessagesForNextStepProof.proofs] using hx
  · simpa [chunk, MessagesForNextStepProof.proofs] using hy

/-- The Step message read from a satisfying execution, retaining its static dimensions. -/
private def StepRun.terminalMessage {C : Circuits D} {b : D.Branch} (s : StepRun C b) :
    MessagesForNextStepProof (VkComms 1 (AffinePoint Fp)) (Vector Fp D.schema.size)
      (Vector (AffinePoint Fp) (D.slots b))
      (Vector (Vector Fp StepIPARounds) (D.slots b)) :=
  let m := s.cells.messagesForNextStepProof
  { appState := m.appState.map (·.val s.V)
    dlogPlonkIndex := m.dlogPlonkIndex.map (readPoint s.V)
    challengePolynomialCommitments := m.challengePolynomialCommitments.map (readPoint s.V)
    oldBulletproofChallenges := m.oldBulletproofChallenges.map (·.map (·.val s.V)) }

/-- A collision between the Step execution's outgoing message and the carried Step message. -/
def TerminalData.StepCollision {C : Circuits D} (d : TerminalData C)
    {b : D.Branch} (s : StepRun C b) : Prop :=
  Pickles.Collision IpaPallas.curve.sponge.params
    (stepMsgInput s.terminalMessage) (stepMsgInput d.stepMessage)

set_option cleanup.letToHave false in
private theorem StepWrapLink.terminal_stepDigest {C : Circuits D} {b : D.Branch}
    (e : StepWrapLink C b) (d : TerminalData C)
    (hreads : CircuitType.Reads e.wrap.V wrapStatement d.statement)
    (hashes : e.step.cells.HashesMessages e.step.V) :
    stepMsgDigest IpaPallas.curve.sponge.params e.step.terminalMessage = d.stepDigest := by
  have hs := hashes.1 e.step.terminalMessage.dlogPlonkIndex
    e.step.terminalMessage.challengePolynomialCommitments
    e.step.terminalMessage.oldBulletproofChallenges
  have hpts : ∀ {n : Nat} (ps : Vector (AffinePoint (FVar Fp)) n),
      CircuitType.Reads e.step.V ps (ps.map (readPoint e.step.V)) := by
    intro n ps
    apply CircuitType.reads_vector.mpr
    intro i hi
    simp only [Vector.getElem_map]
    exact reads_affinePoint.mpr ⟨rfl, rfl⟩
  have hk : ∀ (key : VkComms 1 (AffinePoint (FVar Fp))),
      CircuitType.Reads e.step.V key (key.map (readPoint e.step.V)) := by
    intro key
    rw [CircuitType.reads_ofEquiv]
    simp only [VkComms.equivProd, VkComms.map, Equiv.coe_fn_mk,
      CircuitType.reads_prod]
    have hcols : ∀ {n : Nat} (ps : Vector (Vector (AffinePoint (FVar Fp)) 1) n),
        CircuitType.Reads e.step.V ps (ps.map (·.map (readPoint e.step.V))) := by
      intro n ps
      exact CircuitType.reads_vector.mpr fun i hi ↦ by
        rw [Vector.getElem_map]; exact hpts _
    exact ⟨hcols _, hcols _, hpts _, hpts _, hpts _, hpts _, hpts _, hpts _⟩
  have hc : CircuitType.Reads e.step.V
      e.step.cells.messagesForNextStepProof.oldBulletproofChallenges
      e.step.terminalMessage.oldBulletproofChallenges :=
    CircuitType.reads_vector.mpr fun i hi ↦
      CircuitType.reads_vector.mpr fun j hj ↦ by simp [StepRun.terminalMessage]
  have hhash := hs (hk _) (hpts _) hc
  have hp := e.publicInput
  rw [CircuitType.reads_ofEquiv] at hp
  simp only [StepStatement.equivProd, Equiv.coe_fn_mk, CircuitType.reads_prod] at hp
  have hp := hp.1
  rw [CircuitType.reads_ofEquiv] at hp
  simp only [StepProofState.equivProd, Equiv.coe_fn_mk, CircuitType.reads_prod] at hp
  have hp := CircuitType.reads_fvar.mp hp.2
  change e.step.cells.out.proofState.messagesForNextStepProof.val e.step.V =
    (ZMod.val (e.wrap.cells.2.statement.proofState.messagesForNextStepProof.val e.wrap.V) : Fp)
      at hp
  have hd : wrapStatement.digests[2].val e.wrap.V = redFq d.stepDigest := by
    rw [CircuitType.reads_ofEquiv] at hreads
    simp only [StatementPacked.equivProd, Equiv.coe_fn_mk,
      CircuitType.reads_prod, CircuitType.reads_vector] at hreads
    exact CircuitType.reads_fvar.mp (hreads.2.2.2.1 2 (by decide))
  rw [← e.wrap.terminal_hashes.2.2.1, hd, val_redFq, ZMod.natCast_zmod_val] at hp
  exact hhash.symm.trans hp

private theorem TerminalData.wrapChallenges_eq_or_collision {C : Circuits D}
    (d : TerminalData C) (r : WrapRun C)
    (hreads : CircuitType.Reads r.V wrapStatement d.statement) :
    (r.cells.1.outs.map (·.expandedChallenges)).map (·.map (·.val r.V)) =
      d.message.oldBulletproofChallenges ∨ d.Collision r := by
  have hd := terminalPacked_wrapDigest wrapStatement d.deferred d.spongeDigest
    (wrapMsgDigest IpaVesta.curve.sponge.params C.setup.dummy d.message)
    d.stepDigest d.branchData hreads
  have hh := r.terminal_messageHash.symm.trans hd
  let m := (⟨readPoint r.V r.cells.2.cells.opening.sg,
    (r.cells.1.outs.map (·.expandedChallenges)).map (·.map (·.val r.V))⟩ :
    MessagesForNextWrapProof (AffinePoint Fq) (Vector (Vector Fq WrapIPARounds) D.width))
  by_cases he : wrapMsgInput C.setup.dummy m = wrapMsgInput C.setup.dummy d.message
  · left
    have hc := (List.append_inj' he rfl).1
    have hc := List.append_cancel_left hc
    apply Vector.toList_inj.mp
    apply chunks_injective (by simp)
    simpa only [toList_flatten', List.flatMap_def] using hc
  · right
    exact Collision.of_length_eq (by simp [wrapMsgInput]) he
      (by simpa only [Poseidon.RandomOracle.hash_eq_squeeze] using hh)

private theorem TerminalData.accumulator_mem_or_collision {C : Circuits D}
    (d : TerminalData C) {b : D.Branch} (e : StepWrapLink C b) (i : D.Slot b)
    (hreads : CircuitType.Reads e.wrap.V wrapStatement d.statement)
    (A : Accumulator IpaPallas.curve WrapIPARounds)
    (he : (e.run i (e.mask i)).Produces C.setup.dummy A) :
    A ∈ d.wrapAccumulators.toList ∨ d.StepCollision e.step ∨ d.Collision e.wrap := by
  have hd := e.terminal_stepDigest d hreads he.1.2.1
  obtain ⟨hn, hs⟩ | collision := stepInput_eq_or_collision
    e.step.terminalMessage d.stepMessage hd
  swap
  · exact Or.inr (Or.inl collision)
  obtain hw | collision := d.wrapChallenges_eq_or_collision e.wrap hreads
  swap
  · exact Or.inr (Or.inr collision)
  have hsg := stepInput_points e.step.terminalMessage d.stepMessage hn hs i
  have hn' : D.slots b = d.width.val := hn
  have hwidth := D.slots_le_width b
  have hmax := D.width_le
  left
  rw [← he.2]
  refine List.mem_iff_getElem.mpr ⟨MaxProofsVerified - D.slots b + i.val,
    by simp; omega, ?_⟩
  simp only [wrapAccumulators, Vector.getElem_toList, Vector.getElem_zipWith,
    Vector.getElem_cast, StepWrap.emittedAccumulator, Accumulator.ofCells, StepWrapLink.run]
  rw [Accumulator.mk.injEq]
  constructor
  · rw [Vector.getElem_append_right (by omega) (by omega)]
    have hidx : MaxProofsVerified - D.slots b + i.val - (MaxProofsVerified - d.width.val) =
        i.val := by omega
    simp only [Vector.getElem_map, hidx]
    have hx := congrArg AffinePoint.x hsg
    have hy := congrArg AffinePoint.y hsg
    simp only [StepRun.terminalMessage, TerminalData.stepMessage, Vector.getElem_map,
      Fin.getElem_fin, readPoint] at hx hy
    simp only [readPt, CVar.val, Fin.getElem_fin, hx, hy]
  · rw [Vector.getElem_append_right (by omega) (by omega)]
    have hidx : MaxProofsVerified - D.slots b + i.val - (MaxProofsVerified - D.width) =
        D.width - D.slots b + i.val := by omega
    simp only [hidx]
    rw [← hw]
    simp [StepWrapRun.jf]

/-- Terminal acceptance closes every required slot proof whose key is bound to its source.
The certificate supplies the static verifier setup. The final proof is checked with the
accumulators reconstructed from the carried messages; disagreement with the recovered executions
exhibits a hash collision.
Kimchi witness failures and accumulator-validity failures remain explicit alternatives. -/
theorem terminal_requiredProofs {C : Circuits D} (cert : ApplicationCertified C)
    (p : KimchiProof IpaPallas.curve 1 WrapIPARounds) (d : TerminalData C)
    (haccept : kimchiVerify IpaPallas.curve C.setup.wrapSrs C.wiring.backend.wrapKey
      { p with olds := d.wrapAccumulators.toArray }
      (CircuitType.valueToFields d.statement).toArray = true)
    (checks : d.Checks) :
    (∃ (b : D.Branch) (e : StepWrapLink C b),
      CircuitType.Reads e.wrap.V wrapStatement d.statement ∧
      ∀ i : D.Slot b,
        CircuitType.Reads e.step.V (e.step.cells.prevs i).mustVerify true →
        e.step.KeyBound i →
        kimchiVerify IpaPallas.curve C.setup.wrapSrs (C.wiring.source b i).wrapKey
          (e.proof i) (e.proofPublicInput i) = true) ∨
      (∃ r : WrapRun C, d.Collision r) ∨
      (∃ (b : D.Branch) (s : StepRun C b), d.StepCollision s) ∨
      SomeKimchiFailure C.setup.wrapSrs ∨ SomeKimchiFailure C.setup.stepSrs ∨
      AccumulatorFailure C.setup.wrapSrs C.wiring.backend.wrapKey
        { p with olds := d.wrapAccumulators.toArray }
        (CircuitType.valueToFields d.statement).toArray := by
  classical
  obtain ⟨r, hreads, linked | collision⟩ | failure :=
    terminal_stepWrap cert p d haccept checks
  · obtain ⟨b, e, rfl⟩ := linked
    by_cases hw : d.Collision e.wrap
    · exact Or.inr (Or.inl ⟨e.wrap, hw⟩)
    by_cases hs : d.StepCollision e.step
    · exact Or.inr (Or.inr (Or.inl ⟨b, e.step, hs⟩))
    by_cases ha : AccumulatorFailure C.setup.wrapSrs C.wiring.backend.wrapKey
        { p with olds := d.wrapAccumulators.toArray }
        (CircuitType.valueToFields d.statement).toArray
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ha))))
    refine Or.inl ⟨b, e, hreads, ?_⟩
    intro i hm hk
    obtain ⟨he, _, hv⟩ := e.verifies_proof i (cert.stepWrapSetup b i) hm hk
    obtain hmem | collision := d.accumulator_mem_or_collision e i hreads _ he
    · have h := accepts_or_accumulatorFailure C.setup.wrapSrs
        (C.wiring.source b i).wrapKey (e.proof i) (e.proofPublicInput i)
        C.wiring.backend.wrapKey { p with olds := d.wrapAccumulators.toArray }
        (CircuitType.valueToFields d.statement).toArray
        (by simpa only [Vector.toList_toArray] using hmem) haccept hv
      exact h.resolve_right ha
    · exact False.elim (collision.elim hs hw)
  · exact Or.inr (Or.inl ⟨r, collision⟩)
  · rcases failure with failure | failure
    · exact Or.inr (Or.inr (Or.inr (Or.inl failure)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl failure))))

end Pickles.Application
