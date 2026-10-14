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

variable {D : Shape} {L : Layout D}

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
private theorem WrapRun.terminal_body_holds {C : Circuits D L} (r : WrapRun C) :
    ∀ con ∈ (build (wrapMain (c := Builder r.V (KimchiConstraint Fq))
      (FopParams.of IpaPallas.curve 1 WrapIPARounds Linearization.fqTokens)
      D.widths (stepDomainLog2s C.wiring.stepKeys) (stepKeyCells C.wiring.stepKeys)
      C.wiring.pins C.stepLagrange C.setup.step.σ.h C.setup.dummy L.wrapWidths r.advice
      wrapStatement)
      (bodyStart (F := Fq) (c := Builder r.V (KimchiConstraint Fq))
        (a := StatementPacked StepIPARounds (Type1 Fq) Fq))).constraints,
      ConstraintHolds.Holds r.V con := fun con hc =>
    r.holds con (mem_compileWith_wrapMainCircuit _ _ _ _ _ _ _ _ _ _ hc)

set_option cleanup.letToHave false in
/-- A satisfying Wrap execution supplies the successful group half of its inner Step proof. -/
private theorem WrapRun.terminal_group {C : Circuits D L} (r : WrapRun C) (b : D.Branch)
    (hAssumptions : WrapStepAssumptions C b)
    (hb : r.cells.1.whichBranch.val r.V = (b : Fq))
    (cp : KimchiProof IpaVesta.curve C.wiring.backend.stepChunks StepIPARounds)
    (oldsW : Vector (IpaVesta.curve.Point × Bool) D.width)
    (hproof : ProofReads (wrapSide r.V) r.cells.2.cells.wComm r.cells.2.cells.zComm
      r.cells.2.cells.tComm r.cells.2.cells.opening cp)
    (holds : OldsRead r.V r.cells.2.cells.sgOld cp oldsW) :
    ∃ success : BoolVar Fq,
      GroupHalf.Reads C.setup.stepSrs.σ C.wiring.backend.stepKeys[b].cvk cp
        (wrapPublicInput C.setup.stepSrs.σ C.wiring.backend.stepKeys[b].cvk r.V
          r.cells.2.statement)
        (GroupHalf.wrap r.V wrapStatement.claims) success ∧
      (↑success : CVar Fq).val r.V = 1 := by
  have hg := (builder_spec_iff _ _).mp
    (wrapMain_verifyReads C.setup.wrapSrs.σ C.setup.stepSrs
      C.wiring.backend.stepKeys[b] (C.wiring.valid.stepChunks b) r.V D.widths
      (stepDomainLog2s C.wiring.stepKeys) (stepKeyCells C.wiring.stepKeys)
      C.wiring.pins C.stepLagrange C.setup.step.σ.h C.setup.dummy L.wrapWidths r.advice
      wrapStatement L.width_le C.wiring.valid.branches_le rfl
      hAssumptions.points_ne hAssumptions.avoids) _ r.terminal_body_holds
  have hc : r.cells = _ := compileWith_wrapMainCircuit_cells
    (V := r.V) (FopParams.of IpaPallas.curve 1 WrapIPARounds Linearization.fqTokens)
    D.widths (stepDomainLog2s C.wiring.stepKeys) (stepKeyCells C.wiring.stepKeys)
    C.wiring.pins C.stepLagrange C.setup.step.σ.h C.setup.dummy L.wrapWidths r.advice
  rw [hc] at hb hproof holds ⊢
  exact (hg b hb
    (by simp [stepKeyCells, Wiring.stepKeys])
    (by simpa [stepDomainLog2s, Wiring.stepKeys] using hAssumptions.lagrange)).2.2.2
      cp oldsW hproof holds

/-- The inner Step proof's commitments and opening cells retained by Wrap. -/
private def WrapRun.proofCells {C : Circuits D L} (r : WrapRun C) :
    IvpProof StepIPARounds C.wiring.backend.stepChunks (FVar Fq) (Type1 (FVar Fq)) :=
  ⟨r.cells.2.cells.wComm, r.cells.2.cells.zComm, r.cells.2.cells.tComm,
    r.cells.2.cells.opening⟩

open CompElliptic.CurveForms.ShortWeierstrass in
set_option cleanup.letToHave false in
/-- The retained proof and old-accumulator cells are the allocated, checked curve points. -/
private theorem WrapRun.terminal_cells {C : Circuits D L} (r : WrapRun C) :
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
      C.wiring.pins C.stepLagrange C.setup.step.σ.h C.setup.dummy L.wrapWidths r.advice
      wrapStatement) _ r.terminal_body_holds
  have hc : r.cells = _ := compileWith_wrapMainCircuit_cells
    (V := r.V) (FopParams.of IpaPallas.curve 1 WrapIPARounds Linearization.fqTokens)
    D.widths (stepDomainLog2s C.wiring.stepKeys) (stepKeyCells C.wiring.stepKeys)
    C.wiring.pins C.stepLagrange C.setup.step.σ.h C.setup.dummy L.wrapWidths r.advice
  erw [← hc] at h
  obtain ⟨hacc, pr, hcells, hon⟩ := h
  have hp : r.proofCells = pr := by
    simp only [proofCells, hcells, ivpInputOf]
  exact ⟨hacc, hp ▸ hcells, hp ▸ hon⟩

/-- The old commitment points and the keep bits selected by the Step branch. -/
private def WrapRun.terminalOldsW {C : Circuits D L} (r : WrapRun C) (b : D.Branch) :
    Vector (IpaVesta.curve.Point × Bool) D.width :=
  Vector.ofFn fun j ↦ (readPt (C := IpaVesta.curve) r.V r.cells.1.stepAccs[j].pt,
    decide (D.width - D.slots b ≤ j.val))

/-- The Step proof's old accumulators, pairing kept Wrap cells with carried Step challenges. -/
private def WrapRun.terminalOlds {C : Circuits D L} (r : WrapRun C) (b : D.Branch)
    (challenges : Vector (Vector Fp StepIPARounds) D.width) :
    Array (Accumulator IpaVesta.curve StepIPARounds) :=
  (((List.finRange D.width).filter fun j ↦ decide (D.width - D.slots b ≤ j.val)).map
    fun j ↦ (⟨readPt r.V r.cells.1.stepAccs[j].pt, challenges[j]⟩ :
      Accumulator IpaVesta.curve StepIPARounds)).toArray

/-- The inner Step proof reconstructed from Wrap cells and its carried scalar data. -/
private def WrapRun.terminalProof {C : Circuits D L} (r : WrapRun C) (b : D.Branch)
    (evals : ProofEvaluations (Vector Fp C.wiring.backend.stepChunks))
    (pubEvals : PubEvalSrc IpaVesta.curve C.wiring.backend.stepChunks) (ftEval1 : Fp)
    (challenges : Vector (Vector Fp StepIPARounds) D.width) :
    KimchiProof IpaVesta.curve C.wiring.backend.stepChunks StepIPARounds :=
  r.proofCells.read (wrapSide r.V) evals pubEvals ftEval1 (r.terminalOlds b challenges)

set_option cleanup.letToHave false in
/-- The reconstructed Step proof agrees with the retained proof and old-accumulator cells. -/
private theorem WrapRun.terminal_proofReads {C : Circuits D L} (r : WrapRun C) (b : D.Branch)
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
private theorem WrapRun.terminal_guards {C : Circuits D L} (r : WrapRun C) (b : D.Branch)
    (evals : ProofEvaluations (Vector Fp C.wiring.backend.stepChunks))
    (pubEvals : PubEvalSrc IpaVesta.curve C.wiring.backend.stepChunks) (ftEval1 : Fp)
    (challenges : Vector (Vector Fp StepIPARounds) D.width) :
    Guards IpaVesta.curve C.wiring.backend.stepKeys[b].cvk
      (r.terminalProof b evals pubEvals ftEval1 challenges)
      (wrapPublicInput C.setup.stepSrs.σ C.wiring.backend.stepKeys[b].cvk r.V
        r.cells.2.statement) := by
  have hlayout : StepKeyLayout C.wiring.backend.stepKeys[b].cvk D.width (D.slots b) := by
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
private theorem WrapRun.terminal_branchData {C : Circuits D L} (r : WrapRun C) :
    ∃ b : D.Branch,
      r.cells.1.whichBranch.val r.V = (b : Fq) ∧
      CircuitType.Reads r.V r.cells.1.mask
        (Vector.ofFn fun i : Fin D.width ↦ decide (i.val < D.slots b)) ∧
      wrapStatement.branchData.val r.V =
        4 * (C.wiring.backend.stepKeys[b].cvk.domainLog2 : Fq) +
          ((List.range D.width).map fun i ↦
            ((2 ^ (1 - i) : ℕ) : Fq) * bit (decide (i < D.slots b))).sum := by
  obtain ⟨b, hb, hbranch, _, hmask, _, hbd, _⟩ := (builder_spec_iff _ _).mp
    (wrapMain_reads C.setup.wrapSrs.σ r.V D.widths
      (stepDomainLog2s C.wiring.stepKeys) (stepKeyCells C.wiring.stepKeys)
      C.wiring.pins C.stepLagrange C.setup.step.σ.h C.setup.dummy L.wrapWidths r.advice
      wrapStatement L.width_le C.wiring.valid.branches_le) _ r.terminal_body_holds
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
private theorem WrapRun.terminal_hashes {C : Circuits D L} (r : WrapRun C) :
    r.cells.2.HashesMessages r.V C.setup.dummy wrapStatement r.cells.1 := by
  have h := ((builder_spec_iff _ _).mp
    (wrapMain_statement
      (FopParams.of IpaPallas.curve 1 WrapIPARounds Linearization.fqTokens)
      r.V D.widths (stepDomainLog2s C.wiring.stepKeys) (stepKeyCells C.wiring.stepKeys)
      C.wiring.pins C.stepLagrange C.setup.step.σ.h C.setup.dummy L.wrapWidths r.advice
      wrapStatement C.wiring.backend.stepKeys[(⟨0, D.branches_pos⟩ : D.Branch)].cvk.nc_pos)
      _ r.terminal_body_holds).2.2.2.2
  dsimp only [WrapRun.cells, Circuits.wrapBuilt, Circuits.wrapCircuit]
  erw [compileWith_wrapMainCircuit_cells (V := r.V)]
  exact h

/-- The outgoing Wrap digest binds the inner Step commitment and the finalized Wrap challenges. -/
private theorem WrapRun.terminal_messageHash {C : Circuits D L} (r : WrapRun C) :
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
structure TerminalData (C : Circuits D L) where
  /-- The Step scalar claims packed into the Wrap public input. -/
  deferred : DeferredValues StepIPARounds Prechallenge Fp
  /-- The Step group transcript's digest, before absorbing evaluations. -/
  spongeDigest : Fp
  /-- The Step polynomial evaluations supplied to scalar recomputation. -/
  evals : ChunkedEvals C.wiring.backend.stepChunks Fp
  /-- Old Step IPA challenges, including the unused prefix before the active suffix. -/
  oldChallenges : Vector (Vector Fp StepIPARounds) D.width
  /-- The outgoing message: this Step's commitment and the prior Wrap challenges. -/
  message : MessagesForNextWrapProof (AffinePoint Fq)
    (Vector (Vector Fq WrapIPARounds) D.width)
  /-- The digest carrying the application statement and Step-side messages. -/
  stepDigest : Fp
  /-- The selected Step domain and predecessor mask, packed as in Wrap. -/
  branchData : Fq

/-- The final Wrap public statement determined by the carried data. -/
def TerminalData.statement {C : Circuits D L} (d : TerminalData C) : WrapPublic :=
  terminalPacked d.deferred d.spongeDigest
    (wrapMsgDigest IpaVesta.curve.sponge.params C.setup.dummy d.message)
    d.stepDigest d.branchData

/-- The domain and mask that Wrap publicly binds for a selected branch. -/
def terminalBranchData (C : Circuits D L) (b : D.Branch) : Fq :=
  4 * (C.wiring.backend.stepKeys[b].cvk.domainLog2 : Fq) +
    ((List.range D.width).map fun i ↦
      ((2 ^ (1 - i) : ℕ) : Fq) * bit (decide (i < D.slots b))).sum

/-- The scalar half uses only the active suffix of old Step accumulators. -/
def TerminalData.activeChallenges {C : Circuits D L} (d : TerminalData C)
    (b : D.Branch) : Array (Vector Fp StepIPARounds) :=
  (((List.finRange D.width).filter fun j ↦ decide (D.width - D.slots b ≤ j.val)).map
    fun j ↦ d.oldChallenges[j]).toArray

/-- The Step proof read from a certified Wrap witness and the carried scalar data. -/
def TerminalData.proof {C : Circuits D L} (d : TerminalData C)
    (r : WrapRun C) (b : D.Branch) :=
  r.terminalProof b d.evals.evals (.carried d.evals.pub) d.evals.ftEval1 d.oldChallenges

/-- A collision between the Wrap witness's outgoing message and the supplied message. -/
def TerminalData.Collision {C : Circuits D L} (d : TerminalData C) (r : WrapRun C) : Prop :=
  Pickles.Collision IpaVesta.curve.sponge.params
    (wrapMsgInput C.setup.dummy
      ⟨readPoint r.V r.cells.2.cells.opening.sg,
        (r.cells.1.outs.map (·.expandedChallenges)).map (·.map (·.val r.V))⟩)
    (wrapMsgInput C.setup.dummy d.message)

private theorem TerminalData.branchData_reads {C : Circuits D L} (d : TerminalData C)
    (r : WrapRun C) (h : CircuitType.Reads r.V wrapStatement d.statement) :
    wrapStatement.branchData.val r.V = d.branchData := by
  simp only [CircuitType.reads_ofEquiv, StatementPacked.equivProd, Equiv.coe_fn_mk,
    CircuitType.reads_prod, CircuitType.reads_vector] at h
  exact CircuitType.reads_fvar.mp h.2.2.2.2.2.1

private theorem TerminalData.proof_oldChallenges {C : Circuits D L} (d : TerminalData C)
    (r : WrapRun C) (b : D.Branch) :
    (d.proof r b).olds.map (·.u) = d.activeChallenges b := by
  simp [proof, WrapRun.terminalProof, IvpProof.read, WrapRun.terminalOlds,
    activeChallenges, List.map_map, Function.comp_def]

private theorem TerminalData.commitment_eq_or_collision {C : Circuits D L}
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
structure TerminalData.Checks {C : Circuits D L} (d : TerminalData C) : Prop where
  /-- Recompute the deferred scalars for the Step domain and active old accumulators. -/
  scalars : ∀ b : D.Branch, d.branchData = terminalBranchData C b →
    terminalScalarChecks IpaVesta.curve C.wiring.backend.stepKeys[b].cvk
      d.deferred d.spongeDigest d.evals (d.activeChallenges b)
  /-- Check the remaining Step opening commitment directly. -/
  sg : terminalSg d.message.challengePolynomialCommitment =
    msm IpaVesta.curve C.setup.stepSrs.σ.g
      (bPolyCoefficients fun i ↦
        endoExpand IpaVesta.curve.lam d.deferred.bulletproofChallenges[i].val.val)

/-- Wrap satisfaction supplies the inner Step group check. Scalar recomputation and the
terminal commitment check finish that proof, unless the carried message's digest collides
with the message read from the Wrap witness. No further Step circuit is needed. -/
private theorem WrapRun.terminal_verifies {C : Circuits D L} (r : WrapRun C)
    (d : TerminalData C) (hreads : CircuitType.Reads r.V wrapStatement d.statement)
    (hsetup : ∀ b : D.Branch, WrapStepAssumptions C b) (hchecks : d.Checks) :
    ∃ b : D.Branch, r.cells.1.whichBranch.val r.V = (b : Fq) ∧
      (kimchiVerify IpaVesta.curve C.setup.stepSrs.σ C.wiring.backend.stepKeys[b].cvk
        (d.proof r b)
        (wrapPublicInput C.setup.stepSrs.σ C.wiring.backend.stepKeys[b].cvk r.V
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
    apply terminal_kimchiVerify C.setup.stepSrs.σ C.wiring.backend.stepKeys[b].cvk
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
theorem terminal_kimchiVerify {C : Circuits D L} (cert : ApplicationCertified C)
    (hsetup : ∀ b : D.Branch, WrapStepAssumptions C b)
    (p : KimchiProof IpaPallas.curve 1 WrapIPARounds) (d : TerminalData C)
    (haccept : kimchiVerify IpaPallas.curve C.setup.wrapSrs.σ C.wiring.backend.wrapKey.cvk
      p (CircuitType.valueToFields d.statement).toArray = true)
    (checks : d.Checks) :
    (∃ r : WrapRun C, CircuitType.Reads r.V wrapStatement d.statement ∧
      ∃ b : D.Branch, r.cells.1.whichBranch.val r.V = (b : Fq) ∧
        (kimchiVerify IpaVesta.curve C.setup.stepSrs.σ C.wiring.backend.stepKeys[b].cvk
          (d.proof r b)
          (wrapPublicInput C.setup.stepSrs.σ C.wiring.backend.stepKeys[b].cvk r.V
            r.cells.2.statement) = true ∨ d.Collision r)) ∨
      KimchiFailure C.setup.wrapSrs.σ cert.wrap.index C.wiring.backend.wrapKey p
        ((CircuitType.valueToFields d.statement).cast cert.indices.wrapPublicCount.symm) := by
  obtain ⟨V, holds, hreads⟩ | failure := cert.wrap_valuation_or_failure p d.statement haccept
  · let r : WrapRun C := ⟨V, inertWrapAdvice, holds⟩
    exact Or.inl ⟨r, hreads, r.terminal_verifies d hreads hsetup checks⟩
  · exact Or.inr failure

end Pickles.Application
