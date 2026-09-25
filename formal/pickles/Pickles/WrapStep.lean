import Pickles.StepMain
import Pickles.WrapMain

set_option mvcgen.warning false

/-!
# The wrap circuit's step proof verifies

A wrap circuit verifies one step proof across two circuits: its verify block checks the step
proof's group half, and the next step circuit's slot for the resulting wrap proof finalizes its
scalar half. This module joins the two reads. Under a valuation satisfying the wrap circuit's
constraints (`wrapMain`) and one satisfying the next step circuit's (`stepMain`), the step proof
the wrap circuit's cells read as is accepted by `kimchiVerify`, for every must-verify slot whose
wrap proof was made at the wrap circuit's public input.

## Main results

* `wrapStep_kimchiVerify`: the two circuits' runs, each satisfied under its own valuation, with
  the public-input tie between the wrap circuit and the slot and the readings, make
  `kimchiVerify` accept the wrapped step proof. That the two halves hold one set of claims is
  derived from the tie (`ClaimsCast`, `halvesTies_of_cast`).

## Implementation notes

The public-input tie says the wrap circuit's packed statement reads as the slot's statement
packed (`VerifyOneInput.packedAt`), which `WrapStatement.toPacked_toFields` identifies with the
public input the slot verifies the wrap proof at. The slot finalizes over the domain its branch
data names, and the finalize read needs that domain to be the step key's: the tie carries the
wrap statement's branch data, which `wrapMain_reads` reads as branch `b`'s domain and mask, to
the slot's packed branch data, whose `log2` and mask cells the slot check bounds.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta
open scoped Kimchi

/-- A step key's domain exponent is small: its size is the order of a root of unity of the
field, which divides `p − 1`. -/
private theorem KnownDomains.keyLog2_lt {nc : ℕ} {Es : Env IpaVesta.curve nc}
    (D : KnownDomains Es) : D.keyLog2 < 255 := by
  have hpos : 0 < Es.cvk.n := by have := Es.zkRows_ge; have := Es.zkRows_le; omega
  have hne : Es.cvk.omega ≠ 0 := Es.omega_prim.ne_zero (by omega)
  have hd : Es.cvk.n ∣ PALLAS_BASE_CARD - 1 :=
    Es.omega_prim.dvd_of_pow_eq_one _ (ZMod.pow_card_sub_one_eq_one hne)
  have hle := Nat.le_of_dvd (by norm_num [PALLAS_BASE_CARD]) hd
  rw [D.key_n] at hle
  by_contra hc
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.mp hc)
  norm_num [PALLAS_BASE_CARD] at hle this
  omega

/-- The mask part of the wrap circuit's branch data, at most two slots, is a small number. -/
private theorem maskSum_natCast {w : ℕ} (hw : w ≤ MaxProofsVerified) (p : ℕ → Bool) :
    ∃ s : ℕ, s ≤ 3 ∧ ((List.range w).map fun i =>
      ((2 ^ (1 - i) : ℕ) : Fq) * bit (p i)).sum = (s : Fq) := by
  simp only [MaxProofsVerified] at hw
  interval_cases w
  · exact ⟨0, by norm_num, by simp⟩
  · refine ⟨if p 0 then 2 else 0, by split <;> omega, ?_⟩
    cases h0 : p 0 <;> simp [bit, h0]
  · refine ⟨(if p 0 then 2 else 0) + (if p 1 then 1 else 0), by split <;> split <;> omega, ?_⟩
    cases h0 : p 0 <;> cases h1 : p 1 <;> norm_num [bit, List.range_succ, h0, h1]

/-- A branch data whose `log2` cell holds `n` and whose mask reads as bits packs to a number
`4·n + t` with `t ≤ 3`. -/
private theorem BranchData.packed_val {V : Valuation Fp} (bd : BranchData (FVar Fp) (BoolVar Fp))
    (n : ℕ) (ms : Vector Bool MaxProofsVerified) (hdv : bd.domainLog2.val V = (n : Fp))
    (hms : CircuitType.Reads V bd.proofsVerifiedMask ms) :
    ∃ t : ℕ, t ≤ 3 ∧ bd.packed.val V = ((4 * n + t : ℕ) : Fp) := by
  have h0 := CircuitType.reads_boolVar.mp (CircuitType.reads_vector.mp hms 0 (by decide))
  have h1 := CircuitType.reads_boolVar.mp (CircuitType.reads_vector.mp hms 1 (by decide))
  refine ⟨(if ms[0] then 1 else 0) + 2 * (if ms[1] then 1 else 0),
    by split <;> split <;> omega, ?_⟩
  have e0 : bd.proofsVerifiedMask.toList[0]? = some bd.proofsVerifiedMask[0] := by simp
  have e1 : bd.proofsVerifiedMask.toList[1]? = some bd.proofsVerifiedMask[1] := by simp
  simp only [BranchData.packed, e0, e1, CVar.val_add_, CVar.val_scale_, hdv, h0, h1]
  cases ms[0] <;> cases ms[1] <;> simp [bit]; ring

/-- A wrap statement reading as a step statement packed carries its claims across: the wrap
circuit's claim cells hold the step statement's, reduced into the wrap field. -/
private theorem claimsCast_of_reads {ks : ℕ} {Vw : Valuation Fq} {Vs : Valuation Fp}
    (stmt : StatementPacked ks (Type1 (FVar Fq)) (FVar Fq))
    (st : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (h : CircuitType.Reads Vw stmt (st.toPacked Vs)) :
    ClaimsCast Vw stmt.claims Vs ⟨st.proofState.deferredValues.toDeferredValues, true_,
      st.proofState.spongeDigestBeforeEvaluations⟩ := by
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
  have d0 := hdg 0 (by decide)
  simp only [WrapStatement.toPacked, Type1.equivCarrier, Equiv.coe_fn_mk] at f0 f1 f2 f3 f4
  simp only [WrapStatement.toPacked] at c0 c1 s0 s1 s2 d0
  unfold ClaimsCast
  refine ⟨?_, ?_⟩
  · simp only [StatementPacked.claims, List.map_cons, List.map_nil, f0, f1, f2, f3, f4, c0, c1,
      s0, s1, s2, d0]
    rfl
  · refine List.ext_getElem (by simp [StatementPacked.claims]) fun i h₁ h₂ => ?_
    simp only [StatementPacked.claims, List.getElem_map, Vector.getElem_toList,
      Vector.getElem_map]
    rw [hbp i (by simpa [StatementPacked.claims] using h₁)]
    simp only [WrapStatement.toPacked, Vector.getElem_map]
    rfl

/-- `wrapStep_kimchiVerify` over the wrap circuit's constants as given, tied to the step
environment `EsStep` by hypotheses. -/
private theorem wrapStep_kimchiVerify_core
    -- the next rule's `n` slots; the tag's `w`, the wrap circuit's slots; the wrap circuit's
    -- `branches`, the step proof it verifies at `ncStep` chunks
    {n w branches ncStep : ℕ} [NeZero branches]
    -- the next rule's input, as a value and as cells
    {inVal inVar : Type}
    [CircuitType Fp inVal inVar]
    -- the environment of the wrap proofs (key, SRS, domain)
    (E : Env IpaPallas.curve 1)
    -- the environment of the step proof the wrap circuit verifies
    (EsStep : Env IpaVesta.curve ncStep)
    -- the wrap circuit's valuation
    (Vw : Valuation Fq)
    -- the generator of the wrap domain of each `log2`, a constant of the circuit
    (gen : ℕ → Fq)
    -- the tag's branches: their slot counts, step domains and step keys
    (widths : Vector (Fin (w + 1)) branches) (log2s : Vector ℕ branches)
    (stepKeys : Vector (VkComms ncStep (AffinePoint (FVar Fq))) branches)
    -- each slot's compile-time wrap domain index per branch
    (pins : Vector (Vector (Option ℕ) branches) w)
    -- the Lagrange bases at a step domain, the blinding base, the padding challenges and each
    -- slot's challenge-stack height: constants of the wrap circuit
    (lagrange : ℕ → List (Vector IpaVesta.curve.Point ncStep)) (h : IpaVesta.curve.Point)
    (dummy : List Fq) (slotWidths : Vector ℕ w)
    -- the wrap circuit's advice
    (advW : WrapMainAdvice w ncStep E.σ.k EsStep.σ.k slotWidths.toList.sum)
    -- fewer branches than the field's characteristic
    (hbr : branches ≤ PALLAS_SCALAR_CARD)
    -- `Vw` satisfies every constraint of the compiled wrap circuit
    (hwrap : ∀ con ∈ (compile (a := StatementPacked EsStep.σ.k (Type1 Fq) Fq) (b := Unit)
        (wrapMainCircuit (c := Builder Vw (KimchiConstraint Fq))
          (FopParams.ofEnv E Linearization.fqTokens) gen widths log2s stepKeys pins lagrange h
          dummy slotWidths advW)).constraints,
        ConstraintHolds.Holds Vw con)
    -- the active branch: its key, Lagrange bases and blinding base are `EsStep`'s
    (b : Fin branches)
    (hkeyB : stepKeys[b] = keyCellsOf constPt EsStep.cvk)
    (hlag : lagrange log2s[b] = EsStep.cvk.lagrangeBasis.toList)
    (hh : h = EsStep.σ.h)
    -- the step statement fits the key's Lagrange basis, the key's points are finite, and the SRS
    -- avoids the key's Lagrange relations
    (hsize : w * (E.σ.k + 17) + 1 + w ≤ EsStep.cvk.lagrangeBasis.size)
    (hnz : ∀ P ∈ EsStep.cvk.comms.indexPoints, P ≠ 0)
    (havoidS : EsStep.σ.Avoids EsStep.lagrangeRelations)
    -- the step domains the next step circuit's finalize dispatches over; branch `b`'s is the key's
    (D : KnownDomains EsStep)
    (hlog : log2s[b] = D.keyLog2)
    -- the next rule verifies at most the tag's `w` slots, which is at most `MaxProofsVerified`
    (hn : n ≤ w) (hw : w ≤ MaxProofsVerified)
    -- the `sg` padding the missing accumulators, the unfinalized entry padding the statement
    (dummySg : AffinePoint (FVar Fp)) (dummyUnf : UnfVal E.σ.k)
    -- every slot statement packs into at most `2 ^ E.σ.k` cells, and its public-input
    -- commitment's relations are avoided
    (hsmall : ∀ (inp : VerifyOneInput EsStep.σ.k E.σ.k 1 ncStep w) msg,
      (inp.statement msg).packed.length ≤ 2 ^ E.σ.k)
    (havoid : ∀ (inp : VerifyOneInput EsStep.σ.k E.σ.k 1 ncStep w) msg,
      E.σ.Avoids (stepRelationsAt E (inp.statement msg)))
    -- the next step circuit's valuation
    (Vs : Valuation Fp)
    [CheckedType Fp (Builder Vs (KimchiConstraint Fp)) inVal inVar]
    -- the next rule, and the next step circuit's advice
    (rule : inVar →
      CircuitM Fp (Builder Vs (KimchiConstraint Fp)) (Vector PrevStatement n × List (FVar Fp)))
    (adv : StepMainAdvice n w 1 ncStep E.σ.k EsStep.σ.k inVal)
    -- `Vs` satisfies every constraint of the compiled next step circuit
    (hstep : ∀ con ∈ (compile (a := Unit) (b := Vector Fp (w * (E.σ.k + 17) + 1 + w))
        (stepMainCircuit (c := Builder Vs (KimchiConstraint Fp)) hw (verifyProofAt E)
          (FopParams.ofEnv EsStep Linearization.fpTokens) D.list dummySg dummyUnf rule
          adv)).constraints, ConstraintHolds.Holds Vs con) :
    let r := (build (stepMain (c := Builder Vs (KimchiConstraint Fp)) hw (verifyProofAt E)
      (FopParams.ofEnv EsStep Linearization.fpTokens) D.list dummySg dummyUnf rule adv) 0).result
    -- the wrap circuit's statement and cells
    let stmt := inputVar (F := Fq) (a := StatementPacked EsStep.σ.k (Type1 Fq) Fq)
    let hd := (build (wrapMain (c := Builder Vw (KimchiConstraint Fq))
      (FopParams.ofEnv E Linearization.fqTokens) gen widths log2s stepKeys pins lagrange h dummy
      slotWidths advW stmt)
      (bodyStart (F := Fq) (c := Builder Vw (KimchiConstraint Fq))
        (a := StatementPacked EsStep.σ.k (Type1 Fq) Fq))).result
    -- the wrap circuit's branch index reads as `b`
    hd.1.whichBranch.val Vw = (b : Fq) →
    -- slot `i` must verify
    ∀ i : Fin n, CircuitType.Reads Vs r.prevs[i].mustVerify true →
      let inp := slotInput hw dummySg r.prevs[i] r.slots[i] r.unfs[i] r.msgs[i]
      ∀ ms : List Bool, List.Forall₂ (CircuitType.Reads Vs) inp.proofMask.toList ms →
      -- its wrap proof was made at the wrap circuit's public input
      CircuitType.Reads Vw stmt (inp.packedAt E Vs ms) →
      ∀ (cp : KimchiProof IpaVesta.curve ncStep EsStep.σ.k)
        (oldsW : List (IpaVesta.curve.Point × Bool)),
        -- the step proof's public input: the wrap circuit's packed step statement
        let pub := wrapPublicInput EsStep Vw hd.2.statement
        -- the wrap circuit's cells hold `cp`
        ProofReads (wrapSide Vw) hd.2.cells.wComm hd.2.cells.zComm hd.2.cells.tComm
          hd.2.cells.opening cp →
        OldsRead Vw hd.2.cells.sgOld cp oldsW →
        -- of `cp` itself: the guards, the finalize ties and the deferred `sg` equation
        Guards IpaVesta.curve EsStep.cvk cp pub →
        FopTies EsStep cp pub (inp.finalizedHalf Vs) →
        SgOk EsStep.σ EsStep.cvk cp pub →
        kimchiVerify IpaVesta.curve EsStep.σ EsStep.cvk cp pub = true := by
  intro r stmt hd hb i hmv inp ms hms htie cp oldsW pub hpr hol hguard hf hsg
  -- the step side: slot `i` finalizes, over the domain its branch data names
  obtain ⟨-, -, hscal, n0, ms0, hn0, hdv, hmsR⟩ := (builder_spec_iff _ _).mp
    (stepMain_reads E EsStep D (hn.trans hw) hw dummySg dummyUnf rule adv hsmall havoid) 0
    (fun con hc => hstep con (mem_compile_stepMainCircuit hw _ _ _ _ _ _ _ hc)) i hmv
  -- the wrap side: the body's constraints hold, so its reads do
  have hbody : ∀ con ∈ (build (wrapMain (c := Builder Vw (KimchiConstraint Fq))
      (FopParams.ofEnv E Linearization.fqTokens) gen widths log2s stepKeys pins lagrange h dummy
      slotWidths advW stmt)
      (bodyStart (F := Fq) (c := Builder Vw (KimchiConstraint Fq))
        (a := StatementPacked EsStep.σ.k (Type1 Fq) Fq))
      ).constraints, ConstraintHolds.Holds Vw con := fun con hc =>
    hwrap con (mem_compile_of_mem_body (by
      simp only [wrapMainCircuit, build_bind]
      exact List.mem_append_left _ hc))
  obtain ⟨b', hb', hwb, -, -, hbd, -⟩ := (builder_spec_iff _ _).mp
    (wrapMain_reads E Vw gen widths log2s stepKeys pins lagrange h dummy slotWidths advW stmt hw
      hbr) _ hbody
  -- the circuit's branch is `b`: both are below the field's characteristic
  have hbb : b' = b.val := CharP.natCast_injOn_Iio Fq PALLAS_SCALAR_CARD
    (Set.mem_Iio.2 (by omega)) (Set.mem_Iio.2 (by omega)) (hwb.symm.trans hb)
  subst hbb
  obtain ⟨-, -, -, hgrp⟩ := (builder_spec_iff _ _).mp
    (wrapMain_verifyReads E EsStep Vw gen widths log2s stepKeys pins lagrange h dummy slotWidths
      advW stmt hw hbr hh hsize hnz havoidS) _ hbody b hb hkeyB hlag
  obtain ⟨v, hv, hv1⟩ := hgrp cp oldsW hpr hol
  -- the slot's domain is the key's: cell `29` carries the branch data across the tie
  have hdom : inp.branchData.domainLog2.val Vs = (D.keyLog2 : Fp) := by
    have hcell : stmt.branchData.val Vw
        = ((ToNat.toNat (inp.branchData.packed.val Vs) : ℕ) : Fq) := by
      simp only [CircuitType.reads_ofEquiv, StatementPacked.equivProd, Equiv.coe_fn_mk,
        CircuitType.reads_prod] at htie
      exact CircuitType.reads_fvar.mp htie.2.2.2.2.2.1
    rw [hcell] at hbd
    -- both sides are small numbers: `4·n₀ + t` and `4·log2s[b] + s`
    obtain ⟨t, ht3, hpk⟩ := BranchData.packed_val inp.branchData n0 ms0 hdv hmsR
    obtain ⟨sN, hs3, hsum⟩ := maskSum_natCast hw fun l => decide (l < (widths[b.val] : ℕ))
    have hL := D.keyLog2_lt
    have hn0p : 4 * n0 + t < PALLAS_BASE_CARD := by norm_num [PALLAS_BASE_CARD]; omega
    have hlog' : log2s[b.val] = D.keyLog2 := by simpa using hlog
    rw [hpk, hsum, hlog'] at hbd
    simp only [ToNat.toNat, ZMod.val_natCast_of_lt hn0p] at hbd
    have hnat : 4 * n0 + t = 4 * D.keyLog2 + sN := CharP.natCast_injOn_Iio Fq PALLAS_SCALAR_CARD
      (Set.mem_Iio.2 (by norm_num [PALLAS_SCALAR_CARD]; omega))
      (Set.mem_Iio.2 (by norm_num [PALLAS_SCALAR_CARD]; omega)) (by push_cast at hbd ⊢; exact hbd)
    rw [hdv, show n0 = D.keyLog2 by omega]
  exact hscal hdom cp pub hguard Vw stmt.claims v hv hv1
    (claimsCast_of_reads stmt _ htie) hf hsg

/-- **The wrap circuit's step proof verifies.** Let `Vw` satisfy the wrap circuit built from the
tag's step environments `stepEnvs`, over one SRS, with its branch index reading as branch `b`
whose table is `stepEnvs[b]`'s Lagrange basis, and let `Vs` satisfy the next step circuit, which
finalizes over `stepEnvs[b]`'s domains. For every must-verify slot whose wrap proof was made at
the wrap circuit's public input, each step proof the wrap circuit's cells read as is accepted by
`kimchiVerify`, under the guards, the finalize ties and `SgOk`. -/
theorem wrapStep_kimchiVerify
    -- the next rule's `n` slots; the tag's `w`, the wrap circuit's slots; the wrap circuit's
    -- `branches`, the step proof it verifies at `ncStep` chunks
    {n w branches ncStep : ℕ} [NeZero branches]
    -- the next rule's input, as a value and as cells
    {inVal inVar : Type}
    [CircuitType Fp inVal inVar]
    -- the environment of the wrap proofs (key, SRS, domain)
    (E : Env IpaPallas.curve 1)
    -- the tag's step circuits' environments, one per branch, over one SRS at the deployed round
    -- count
    (stepEnvs : Vector (Env IpaVesta.curve ncStep) branches)
    (σStep : SRS IpaVesta.curve.Point) (hσ : ∀ i : Fin branches, stepEnvs[i].σ = σStep)
    -- the branch the wrap circuit takes
    (b : Fin branches)
    -- the wrap circuit's valuation
    (Vw : Valuation Fq)
    -- the generator of the wrap domain of each `log2`, a constant of the circuit
    (gen : ℕ → Fq)
    -- the tag's branches' slot counts
    (widths : Vector (Fin (w + 1)) branches)
    -- each slot's compile-time wrap domain index per branch
    (pins : Vector (Vector (Option ℕ) branches) w)
    -- the Lagrange bases at a step domain, the padding challenges and each slot's
    -- challenge-stack height: constants of the wrap circuit
    (lagrange : ℕ → List (Vector IpaVesta.curve.Point ncStep))
    (dummy : List Fq) (slotWidths : Vector ℕ w)
    -- the wrap circuit's advice
    (advW : WrapMainAdvice w ncStep E.σ.k stepEnvs[b].σ.k slotWidths.toList.sum)
    -- fewer branches than the field's characteristic
    (hbr : branches ≤ PALLAS_SCALAR_CARD)
    -- `Vw` satisfies every constraint of the compiled wrap circuit, over the branches' keys and
    -- domains and the SRS's blinding base
    (hwrap : ∀ con ∈ (compile (a := StatementPacked stepEnvs[b].σ.k (Type1 Fq) Fq) (b := Unit)
        (wrapMainCircuit (c := Builder Vw (KimchiConstraint Fq))
          (FopParams.ofEnv E Linearization.fqTokens) gen widths
          (stepDomainLog2s stepEnvs) (stepKeyCells stepEnvs) pins
          lagrange σStep.h dummy slotWidths advW)).constraints,
        ConstraintHolds.Holds Vw con)
    -- the table at branch `b`'s domain is its key's Lagrange basis
    (hlag : lagrange stepEnvs[b].cvk.domainLog2 = stepEnvs[b].cvk.lagrangeBasis.toList)
    -- the step statement fits the key's Lagrange basis, the key's points are finite, and the SRS
    -- avoids the key's Lagrange relations
    (hsize : w * (E.σ.k + 17) + 1 + w ≤ stepEnvs[b].cvk.lagrangeBasis.size)
    (hnz : ∀ P ∈ stepEnvs[b].cvk.comms.indexPoints, P ≠ 0)
    (havoidS : stepEnvs[b].σ.Avoids stepEnvs[b].lagrangeRelations)
    -- the step domains the next step circuit's finalize dispatches over
    (D : KnownDomains stepEnvs[b])
    -- the next rule verifies at most the tag's `w` slots, which is at most `MaxProofsVerified`
    (hn : n ≤ w) (hw : w ≤ MaxProofsVerified)
    -- the `sg` padding the missing accumulators, the unfinalized entry padding the statement
    (dummySg : AffinePoint (FVar Fp)) (dummyUnf : UnfVal E.σ.k)
    -- every slot statement packs into at most `2 ^ E.σ.k` cells, and its public-input
    -- commitment's relations are avoided
    (hsmall : ∀ (inp : VerifyOneInput stepEnvs[b].σ.k E.σ.k 1 ncStep w) msg,
      (inp.statement msg).packed.length ≤ 2 ^ E.σ.k)
    (havoid : ∀ (inp : VerifyOneInput stepEnvs[b].σ.k E.σ.k 1 ncStep w) msg,
      E.σ.Avoids (stepRelationsAt E (inp.statement msg)))
    -- the next step circuit's valuation
    (Vs : Valuation Fp)
    [CheckedType Fp (Builder Vs (KimchiConstraint Fp)) inVal inVar]
    -- the next rule, and the next step circuit's advice
    (rule : inVar →
      CircuitM Fp (Builder Vs (KimchiConstraint Fp)) (Vector PrevStatement n × List (FVar Fp)))
    (adv : StepMainAdvice n w 1 ncStep E.σ.k stepEnvs[b].σ.k inVal)
    -- `Vs` satisfies every constraint of the compiled next step circuit
    (hstep : ∀ con ∈ (compile (a := Unit) (b := Vector Fp (w * (E.σ.k + 17) + 1 + w))
        (stepMainCircuit (c := Builder Vs (KimchiConstraint Fp)) hw (verifyProofAt E)
          (FopParams.ofEnv stepEnvs[b] Linearization.fpTokens) D.list dummySg dummyUnf rule
          adv)).constraints, ConstraintHolds.Holds Vs con) :
    let r := (build (stepMain (c := Builder Vs (KimchiConstraint Fp)) hw (verifyProofAt E)
      (FopParams.ofEnv stepEnvs[b] Linearization.fpTokens) D.list dummySg dummyUnf rule adv)
      0).result
    -- the wrap circuit's statement and cells
    let stmt := inputVar (F := Fq) (a := StatementPacked stepEnvs[b].σ.k (Type1 Fq) Fq)
    let hd := (build (wrapMain (c := Builder Vw (KimchiConstraint Fq))
      (FopParams.ofEnv E Linearization.fqTokens) gen widths
      (stepDomainLog2s stepEnvs) (stepKeyCells stepEnvs) pins
      lagrange σStep.h dummy
      slotWidths advW stmt)
      (bodyStart (F := Fq) (c := Builder Vw (KimchiConstraint Fq))
        (a := StatementPacked stepEnvs[b].σ.k (Type1 Fq) Fq))).result
    -- the wrap circuit's branch index reads as `b`
    hd.1.whichBranch.val Vw = (b : Fq) →
    -- slot `i` must verify
    ∀ i : Fin n, CircuitType.Reads Vs r.prevs[i].mustVerify true →
      let inp := slotInput hw dummySg r.prevs[i] r.slots[i] r.unfs[i] r.msgs[i]
      ∀ ms : List Bool, List.Forall₂ (CircuitType.Reads Vs) inp.proofMask.toList ms →
      -- its wrap proof was made at the wrap circuit's public input
      CircuitType.Reads Vw stmt (inp.packedAt E Vs ms) →
      ∀ (cp : KimchiProof IpaVesta.curve ncStep stepEnvs[b].σ.k)
        (oldsW : List (IpaVesta.curve.Point × Bool)),
        -- the step proof's public input: the wrap circuit's packed step statement
        let pub := wrapPublicInput stepEnvs[b] Vw hd.2.statement
        -- the wrap circuit's cells hold `cp`
        ProofReads (wrapSide Vw) hd.2.cells.wComm hd.2.cells.zComm hd.2.cells.tComm
          hd.2.cells.opening cp →
        OldsRead Vw hd.2.cells.sgOld cp oldsW →
        -- of `cp` itself: the guards, the finalize ties and the deferred `sg` equation
        Guards IpaVesta.curve stepEnvs[b].cvk cp pub →
        FopTies stepEnvs[b] cp pub (inp.finalizedHalf Vs) →
        SgOk stepEnvs[b].σ stepEnvs[b].cvk cp pub →
        kimchiVerify IpaVesta.curve stepEnvs[b].σ stepEnvs[b].cvk cp pub = true := by
  -- the key's domain exponent is `D`'s: both give its size as a power of two
  have hlog : (stepDomainLog2s stepEnvs)[b] = D.keyLog2 := by
    have := D.key_n
    simp only [KimchiVK.n] at this
    simpa [stepDomainLog2s] using Nat.pow_right_injective (le_refl 2) this
  intro r stmt hd hb i hmv inp ms hms htie cp oldsW pub hpr hol hguard hf hsg
  exact wrapStep_kimchiVerify_core E stepEnvs[b] Vw gen widths
    (stepDomainLog2s stepEnvs) (stepKeyCells stepEnvs) pins lagrange σStep.h dummy slotWidths
    advW hbr hwrap b (by simp [stepKeyCells]) (by simpa [stepDomainLog2s] using hlag)
    (by rw [hσ b]) hsize hnz havoidS D hlog hn hw dummySg dummyUnf hsmall havoid Vs rule adv hstep
    hb i hmv ms hms htie cp oldsW hpr hol hguard hf hsg

end Pickles
