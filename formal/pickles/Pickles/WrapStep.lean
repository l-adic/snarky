import Pickles.StepMain
import Pickles.WrapMain

set_option mvcgen.warning false

/-!
# The wrap circuit's step proof verifies

A wrap circuit verifies one step proof across two circuits: its verify block checks the step
proof's group half, and the next step circuit's slot for the resulting wrap proof finalizes its
scalar half. This module joins the two reads. Under a valuation satisfying the wrap circuit's
constraints (`wrapMain`) and one satisfying the next step circuit's (`stepMain`), the wrap
circuit's cells hold a step proof that `kimchiVerify` accepts, for every must-verify slot whose
wrap proof was made at the wrap circuit's public input.

## Main results

* `wrapStep_kimchiVerify`: the two circuits' runs, each satisfied under its own valuation, with
  the public-input tie between the wrap circuit and the slot, give a step proof the wrap
  circuit's cells hold, which `kimchiVerify` accepts. That the two halves hold one set of claims is
  derived from the tie (`ClaimsCast`, `halvesTies_of_cast`).

## Implementation notes

The public-input tie says the wrap circuit's packed statement reads as the slot's statement
packed (`VerifyOneInput.packedAt`), which `WrapStatement.toPacked_toFields` identifies with the
public input the slot verifies the wrap proof at. The slot finalizes over the domain its branch
data names, and the finalize read needs that domain to be the step key's: the tie carries the
wrap statement's branch data, which `wrapMain_reads` reads as branch `b`'s domain and mask, to
the slot's packed branch data, whose `log2` and mask cells the slot check bounds.

The step proof is read off the cells of both circuits: its commitments, opening and old
accumulators from the wrap circuit's (`wrapMain_cells`), its evaluations and old challenges
from the slot's. The two circuits pack the slot mask in opposite orders into the branch data,
so the same tie makes the wrap circuit's keep bits the slot's mask (`mask_rev`).
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta
open scoped Kimchi

/-- A step key's domain exponent is small: its size is the order of a root of unity of the
field, which divides `p − 1`. -/
private theorem Env.domainLog2_lt {nc : ℕ} (Es : Env IpaVesta.curve nc) :
    Es.cvk.domainLog2 < 255 := by
  have hpos : 0 < Es.cvk.n := by have := Es.zkRows_ge; have := Es.zkRows_le; omega
  have hne : Es.cvk.omega ≠ 0 := Es.omega_prim.ne_zero (by omega)
  have hd : Es.cvk.n ∣ PALLAS_BASE_CARD - 1 :=
    Es.omega_prim.dvd_of_pow_eq_one _ (ZMod.pow_card_sub_one_eq_one hne)
  have hle := Nat.le_of_dvd (by norm_num [PALLAS_BASE_CARD]) hd
  rw [KimchiVK.n] at hle
  by_contra hc
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.mp hc)
  norm_num [PALLAS_BASE_CARD] at hle this
  omega

/-- The mask part of the wrap circuit's branch data, at most two slots, is a small number:
`Σᵢ 2^(1−i)·maskᵢ ≤ 3`. -/
private theorem maskSum_natCast {w : ℕ} (hw : w ≤ MaxProofsVerified) (p : ℕ → Bool) :
    ((List.range w).map fun i => 2 ^ (1 - i) * (if p i then 1 else 0)).sum ≤ 3 ∧
      ((List.range w).map fun i => ((2 ^ (1 - i) : ℕ) : Fq) * bit (p i)).sum
        = ((((List.range w).map fun i => 2 ^ (1 - i) * (if p i then 1 else 0)).sum : ℕ) : Fq) := by
  simp only [MaxProofsVerified] at hw
  interval_cases w <;> cases h0 : p 0 <;> cases h1 : p 1 <;>
    norm_num [bit, List.range_succ, h0, h1]

/-- The step side's mask is the wrap side's reversed: the two pack as `ms[0] + 2·ms[1]` and
`Σᵢ 2^(1−i)·maskᵢ`, and agree. -/
private theorem mask_rev {w : ℕ} (hw : w ≤ MaxProofsVerified) (p : ℕ → Bool)
    (ms : Vector Bool MaxProofsVerified)
    (h : (if ms[0] then 1 else 0) + 2 * (if ms[1] then 1 else 0)
      = ((List.range w).map fun i => 2 ^ (1 - i) * (if p i then 1 else 0)).sum)
    (j : Fin w) : ms[MaxProofsVerified - w + j] = p (w - 1 - j) := by
  obtain ⟨⟨l⟩, hl⟩ := ms
  obtain ⟨j, hj⟩ := j
  simp only [MaxProofsVerified] at hw hl ⊢
  match l, hl with
  | [m0, m1], _ =>
    interval_cases w <;> interval_cases j <;> cases h0 : p 0 <;> cases h1 : p 1 <;>
      cases m0 <;> cases m1 <;> simp_all [List.range_succ]

/-- A mask's last `w` cells read as the last `w` bits of the mask's reading. -/
private theorem reads_drop {w : ℕ} {V : Valuation Fp} {c : Vector (BoolVar Fp) 2}
    {ms0 : Vector Bool 2} {ms : Vector Bool w} (hw : w ≤ 2) (h0 : CircuitType.Reads V c ms0)
    (h : CircuitType.Reads V ((c.drop (2 - w)).cast (by omega)) ms) (j : Fin w) :
    ms[j] = ms0[2 - w + j] := by
  have a := CircuitType.reads_boolVar.mp (CircuitType.reads_vector.mp h j j.isLt)
  have b := CircuitType.reads_boolVar.mp (CircuitType.reads_vector.mp h0 (2 - w + j) (by omega))
  simp only [Vector.getElem_cast, Vector.getElem_drop] at a
  rw [a] at b
  cases hm : ms[j] <;> cases hm0 : ms0[2 - w + j] <;> simp_all [bit]

/-- A branch data whose `log2` cell holds `n` and whose mask reads as bits `ms` packs to
`4·n + ms[0] + 2·ms[1]`. -/
private theorem BranchData.packed_val {V : Valuation Fp} (bd : BranchData (FVar Fp) (BoolVar Fp))
    (n : ℕ) (ms : Vector Bool MaxProofsVerified) (hdv : bd.domainLog2.val V = (n : Fp))
    (hms : CircuitType.Reads V bd.proofsVerifiedMask ms) :
    bd.packed.val V
      = ((4 * n + ((if ms[0] then 1 else 0) + 2 * (if ms[1] then 1 else 0)) : ℕ) : Fp) := by
  have h0 := CircuitType.reads_boolVar.mp (CircuitType.reads_vector.mp hms 0 (by decide))
  have h1 := CircuitType.reads_boolVar.mp (CircuitType.reads_vector.mp hms 1 (by decide))
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
    -- the tag's branches: their slot counts, step domains and step keys
    (widths : Vector (Fin (w + 1)) branches) (log2s : Vector ℕ branches)
    (stepKeys : Vector (VkComms ncStep (AffinePoint (FVar Fq))) branches)
    -- each slot's compile-time wrap domain index per branch
    (pins : Vector (Vector (Option ℕ) branches) w)
    -- the Lagrange bases at a step domain, the blinding base, the padding challenges and each
    -- slot's challenge-stack height: constants of the wrap circuit
    (lagrange : ℕ → List (Vector IpaVesta.curve.Point ncStep)) (h : IpaVesta.curve.Point)
    (dummy : Vector Fq E.σ.k) (slotWidths : Vector ℕ w)
    -- the wrap circuit's advice
    (advW : WrapMainAdvice w ncStep E.σ.k EsStep.σ.k slotWidths.toList.sum)
    -- fewer branches than the field's characteristic
    (hbr : branches ≤ PALLAS_SCALAR_CARD)
    -- `Vw` satisfies every constraint of the compiled wrap circuit
    (hwrap : ∀ con ∈ (compile (a := StatementPacked EsStep.σ.k (Type1 Fq) Fq) (b := Unit)
        (wrapMainCircuit (c := Builder Vw (KimchiConstraint Fq))
          (FopParams.ofEnv E Linearization.fqTokens) widths log2s stepKeys pins lagrange h
          dummy slotWidths advW)).constraints,
        ConstraintHolds.Holds Vw con)
    -- the active branch: its key, Lagrange bases and blinding base are `EsStep`'s
    (b : Fin branches)
    (hkeyB : stepKeys[b] = keyCellsOf constPt EsStep.cvk)
    (hlag : lagrange log2s[b]
      = EsStep.cvk.lagrangeBasis.toList.take (CircuitType.size Fp (StmtVal E.σ.k w)))
    (hh : h = EsStep.σ.h)
    -- the step statement fits the key's Lagrange basis, the key's points are finite, and the SRS
    -- avoids the key's Lagrange relations
    (hsize : CircuitType.size Fp (StmtVal E.σ.k w) ≤ EsStep.cvk.lagrangeBasis.size)
    (hnz : ∀ P ∈ EsStep.cvk.comms.indexPoints, P ≠ 0)
    (havoidS : EsStep.σ.Avoids EsStep.lagrangeRelations)
    -- the step domains the next step circuit's finalize dispatches over; branch `b`'s is the key's
    (D : KnownDomains EsStep)
    (hlog : log2s[b] = EsStep.cvk.domainLog2)
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
    (hstep : ∀ con ∈ (compile (a := Unit) (b := StmtVal E.σ.k w)
        (stepMainCircuit (c := Builder Vs (KimchiConstraint Fp)) hw (verifyProofAt E)
          (FopParams.ofEnv EsStep Linearization.fpTokens) D.list dummySg dummyUnf rule
          adv)).constraints, ConstraintHolds.Holds Vs con) :
    let r := (build (stepMain (c := Builder Vs (KimchiConstraint Fp)) hw (verifyProofAt E)
      (FopParams.ofEnv EsStep Linearization.fpTokens) D.list dummySg dummyUnf rule adv) 0).result
    -- the wrap circuit's statement and cells
    let stmt := inputVar (F := Fq) (a := StatementPacked EsStep.σ.k (Type1 Fq) Fq)
    let hd := (build (wrapMain (c := Builder Vw (KimchiConstraint Fq))
      (FopParams.ofEnv E Linearization.fqTokens) widths log2s stepKeys pins lagrange h dummy
      slotWidths advW stmt)
      (bodyStart (F := Fq) (c := Builder Vw (KimchiConstraint Fq))
        (a := StatementPacked EsStep.σ.k (Type1 Fq) Fq))).result
    -- the wrap circuit's branch index reads as `b`
    hd.1.whichBranch.val Vw = (b : Fq) →
    -- slot `i` must verify
    ∀ i : Fin n, CircuitType.Reads Vs r.prevs[i].mustVerify true →
      let inp := slotInput hw dummySg r.prevs[i] r.slots[i] r.unfs[i] r.msgs[i]
      ∀ ms : Vector Bool w, CircuitType.Reads Vs inp.proofMask ms →
      -- its wrap proof was made at the wrap circuit's public input
      CircuitType.Reads Vw stmt (inp.packedAt E Vs ms) →
      ∃ (cp : KimchiProof IpaVesta.curve ncStep EsStep.σ.k)
        (oldsW : List (IpaVesta.curve.Point × Bool)),
        -- the step proof's public input: the wrap circuit's packed step statement
        let pub := wrapPublicInput EsStep Vw hd.2.statement
        -- the wrap circuit's cells hold `cp`
        ProofReads (wrapSide Vw) hd.2.cells.wComm hd.2.cells.zComm hd.2.cells.tComm
          hd.2.cells.opening cp ∧
        OldsRead Vw hd.2.cells.sgOld cp oldsW ∧
        -- the next step circuit's finalize cells hold `cp`'s evaluations and old challenges
        FopTies EsStep cp pub (inp.finalizedHalf Vs) ∧
        -- of `cp` itself: the guards and the deferred `sg` equation
        (Guards IpaVesta.curve EsStep.cvk cp pub →
          SgOk EsStep.σ EsStep.cvk cp pub →
          kimchiVerify IpaVesta.curve EsStep.σ EsStep.cvk cp pub = true) := by
  intro r stmt hd hb i hmv inp ms hms htie
  -- the step side: slot `i` finalizes, over the domain its branch data names
  obtain ⟨-, -, hscal, -, -, n0, ms0, hn0, hdv, hmsR⟩ := (builder_spec_iff _ _).mp
    (stepMain_reads E (FopParams.ofEnv EsStep Linearization.fpTokens) D.list
      EsStep.rounds_small (fun inp => inp.ScalarReads EsStep Vs)
      (fun vk inp => verifyOne_scalarReads EsStep D hw (verifyProofAt E) vk inp) (hn.trans hw) hw
      dummySg dummyUnf rule adv hsmall havoid) 0
    (fun con hc => hstep con (mem_compile_stepMainCircuit hw _ _ _ _ _ _ _ hc)) i hmv
  -- the wrap side: the body's constraints hold, so its reads do
  have hbody : ∀ con ∈ (build (wrapMain (c := Builder Vw (KimchiConstraint Fq))
      (FopParams.ofEnv E Linearization.fqTokens) widths log2s stepKeys pins lagrange h dummy
      slotWidths advW stmt)
      (bodyStart (F := Fq) (c := Builder Vw (KimchiConstraint Fq))
        (a := StatementPacked EsStep.σ.k (Type1 Fq) Fq))
      ).constraints, ConstraintHolds.Holds Vw con := fun con hc =>
    hwrap con (mem_compile_of_mem_body (by
      simp only [wrapMainCircuit, build_bind]
      exact List.mem_append_left _ hc))
  obtain ⟨b', hb', hwb, -, hmask, -, hbd, -⟩ := (builder_spec_iff _ _).mp
    (wrapMain_reads E Vw widths log2s stepKeys pins lagrange h dummy slotWidths advW stmt hw
      hbr) _ hbody
  -- the circuit's branch is `b`: both are below the field's characteristic
  have hbb : b' = b.val := CharP.natCast_injOn_Iio Fq PALLAS_SCALAR_CARD
    (Set.mem_Iio.2 (by omega)) (Set.mem_Iio.2 (by omega)) (hwb.symm.trans hb)
  subst hbb
  obtain ⟨-, -, -, hgrp⟩ := (builder_spec_iff _ _).mp
    (wrapMain_verifyReads E EsStep Vw widths log2s stepKeys pins lagrange h dummy slotWidths
      advW stmt hw hbr hh (StmtVal.size E.σ.k w ▸ hsize) hnz havoidS) _ hbody b hb hkeyB
      (StmtVal.size E.σ.k w ▸ hlag)
  -- the wrap circuit's proof cells and accumulators, on the curve
  obtain ⟨hacc, pr, hcells, hon⟩ := (builder_spec_iff _ _).mp
    (wrapMain_cells (FopParams.ofEnv E Linearization.fqTokens) Vw widths log2s stepKeys pins
      lagrange h dummy slotWidths advW stmt) _ hbody
  -- cell `29` carries the branch data across the tie: `4·n₀ + ms₀[0] + 2·ms₀[1]` on the step
  -- side, `4·log2s[b] + Σᵢ 2^(1−i)·[i < widths[b]]` on the wrap side
  have hcell : stmt.branchData.val Vw
      = ((ToNat.toNat (inp.branchData.packed.val Vs) : ℕ) : Fq) := by
    simp only [CircuitType.reads_ofEquiv, StatementPacked.equivProd, Equiv.coe_fn_mk,
      CircuitType.reads_prod] at htie
    exact CircuitType.reads_fvar.mp htie.2.2.2.2.2.1
  rw [hcell, BranchData.packed_val inp.branchData n0 ms0 hdv hmsR] at hbd
  obtain ⟨hs3, hsum⟩ := maskSum_natCast hw fun l => decide (l < (widths[b.val] : ℕ))
  set t := (if ms0[0] then 1 else 0) + 2 * (if ms0[1] then 1 else 0) with htdef
  set sN := ((List.range w).map fun i =>
    2 ^ (1 - i) * (if decide (i < (widths[b.val] : ℕ)) then 1 else 0)).sum
  have ht3 : t ≤ 3 := by rw [htdef]; split <;> split <;> omega
  have hL := EsStep.domainLog2_lt
  have hn0p : 4 * n0 + t < PALLAS_BASE_CARD := by norm_num [PALLAS_BASE_CARD]; omega
  have hlog' : log2s[b.val] = EsStep.cvk.domainLog2 := by simpa using hlog
  rw [hsum, hlog'] at hbd
  simp only [ToNat.toNat, ZMod.val_natCast_of_lt hn0p] at hbd
  have hnat : 4 * n0 + t = 4 * EsStep.cvk.domainLog2 + sN :=
    CharP.natCast_injOn_Iio Fq PALLAS_SCALAR_CARD
    (Set.mem_Iio.2 (by norm_num [PALLAS_SCALAR_CARD]; omega))
    (Set.mem_Iio.2 (by norm_num [PALLAS_SCALAR_CARD]; omega)) (by push_cast at hbd ⊢; exact hbd)
  -- the slot's domain is the key's
  have hdom : inp.branchData.domainLog2.val Vs = (EsStep.cvk.domainLog2 : Fp) := by
    rw [hdv, show n0 = EsStep.cvk.domainLog2 by omega]
  -- the slot's mask is the wrap mask reversed
  have hrev := mask_rev hw _ ms0 (htdef ▸ (by omega : t = sN))
  have hmsj : ∀ j : Fin w, ms[j] = ms0[MaxProofsVerified - w + j] :=
    reads_drop (by simpa [MaxProofsVerified] using hw) hmsR hms
  -- so the wrap circuit's keep bit for slot `j` reads as `ms[j]`
  have hlen : hd.1.mask.length = w := by simpa using congrArg List.length hmask
  have hkeep : ∀ j : Fin w,
      (↑(hd.1.mask.reverse.getD j.val true_) : CVar Fq).val Vw = bit ms[j] := by
    intro j
    have h := List.getElem_of_eq hmask
      (show w - 1 - j < (hd.1.mask.map fun x : BoolVar Fq => (↑x : CVar Fq).val Vw).length by
        simp; omega)
    simp only [List.getElem_map, List.getElem_range] at h
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_reverse, hmsj j, hrev j]
    simpa [hlen] using h
  -- the step proof the cells hold: its group half from the wrap circuit's cells, its evaluations
  -- and kept old challenges from the next step circuit's
  have hcells' : hd.2.cells = ivpInputOf stmt.claims.deferredValues hd.1.sgOld hd.1.key pr := hcells
  let P : Fin w → IpaVesta.curve.Point := fun j =>
    readPt (C := IpaVesta.curve) Vw hd.1.stepAccs[j].pt
  let U : Fin w → Vector Fp EsStep.σ.k := fun j => inp.prevChallenges[j].map (·.val Vs)
  let cp := pr.read (wrapSide Vw) (inp.evals.evals.map fun v => v.map (·.val Vs))
    (.carried (inp.evals.pub.map fun v => v.map (·.val Vs))) (inp.evals.ftEval1.val Vs)
    (((List.finRange w).filter fun j => ms[j]).map fun j =>
      (⟨P j, U j⟩ : Accumulator IpaVesta.curve EsStep.σ.k)).toArray
  let oldsW := (List.finRange w).map fun j => (P j, ms[j])
  have hpr : ProofReads (wrapSide Vw) hd.2.cells.wComm hd.2.cells.zComm hd.2.cells.tComm
      hd.2.cells.opening cp := by
    rw [hcells']
    exact IvpProof.read_proofReads _ _ _ _ _ _ hon
  have hol : OldsRead Vw hd.2.cells.sgOld cp oldsW := by
    rw [hcells']
    refine ⟨?_, ?_⟩
    · simp only [ivpInputOf, WrapMainFinalizeOut.sgOld, oldsW, List.map_map,
        List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact List.forall₂_same.mpr fun j _ => ⟨onCurveAt_readPt (hacc j), hkeep j⟩
    · simp [cp, IvpProof.read, oldsW, List.filter_map, Function.comp_def]
  have hf : FopTies EsStep cp (wrapPublicInput EsStep Vw hd.2.statement)
      (inp.finalizedHalf Vs) := by
    refine ⟨?_, rfl, rfl, rfl⟩
    have hm : (inp.finalizedHalf Vs).maskVals = List.ofFn fun j : Fin w => ms[j] := by
      refine List.ext_getElem (by simp [ScalarHalf.maskVals]) fun j h₁ h₂ => ?_
      have hj : j < w := by simpa [ScalarHalf.maskVals] using h₁
      have h := CircuitType.reads_boolVar.mp (CircuitType.reads_vector.mp hms j hj)
      simp only [ScalarHalf.maskVals, VerifyOneInput.finalizedHalf, ScalarHalf.step,
        List.getElem_map, Vector.getElem_toList, List.getElem_ofFn, h]
      cases ms[j]'hj <;> simp [bit]
    have hp : (inp.finalizedHalf Vs).prevVals = List.ofFn fun j : Fin w => (U j).toList := by
      refine List.ext_getElem (by simp [ScalarHalf.prevVals]) fun j h₁ h₂ => ?_
      simp [ScalarHalf.prevVals, VerifyOneInput.finalizedHalf, ScalarHalf.step, U,
        Vector.toList_map]
    rw [hm, hp, flatten_zipWith_keep]
    simp [cp, IvpProof.read]
  refine ⟨cp, oldsW, hpr, hol, hf, fun hguard hsg => ?_⟩
  obtain ⟨v, hv, hv1⟩ := hgrp cp oldsW hpr hol
  have hcc := claimsCast_of_reads stmt _ htie
  clear_value oldsW cp U P
  exact hscal hdom cp (wrapPublicInput EsStep Vw hd.2.statement) hguard Vw stmt.claims v hv hv1
    hcc hf hsg

/-- **The wrap circuit's step proof verifies.** Let `Vw` satisfy the wrap circuit built from the
tag's step keys `stepKeys` over the step SRS `σStep`, with its branch index reading as branch
`b` whose table is key `b`'s Lagrange basis, and let `Vs` satisfy the next step circuit,
compiled with finalize constants `P` and candidate `domains` that fit key `b`. For every
must-verify slot whose wrap proof was made at the wrap circuit's public input, the wrap
circuit's cells hold a step proof; the slot's finalize cells hold its evaluations and old
challenges, and `kimchiVerify` accepts it under the guards and `SgOk`. -/
theorem wrapStep_kimchiVerify
    -- the next rule's `n` slots; the tag's `w`, the wrap circuit's slots; the wrap circuit's
    -- `branches`, the step proof it verifies at `ncStep` chunks
    {n w branches ncStep : ℕ}
    [NeZero branches]
    -- the next rule's input, as a value and as cells
    {inVal inVar : Type}
    [CircuitType Fp inVal inVar]
    -- the environment of the wrap proofs (key, SRS, domain)
    (E : Env IpaPallas.curve 1)
    -- the wrap SRS has the deployed size, `2 ^ WrapIPARounds` points
    (hE : E.σ.k = WrapIPARounds)
    -- the step SRS
    (σStep : SRS IpaVesta.curve.Point)
    -- the step SRS has the deployed size, `2 ^ StepIPARounds` points
    (hσk : σStep.k = StepIPARounds)
    -- the tag's step keys, one per branch
    (stepKeys : Vector (KimchiVK IpaVesta.curve ncStep) branches)
    -- each is a key over the step SRS
    (hkeys : ∀ i : Fin branches, Env.Invariants σStep stepKeys[i])
    -- the branch the wrap circuit takes
    (b : Fin branches)
    -- the wrap circuit's valuation
    (Vw : Valuation Fq)
    -- the tag's branches' slot counts
    (widths : Vector (Fin (w + 1)) branches)
    -- each slot's compile-time wrap domain index per branch
    (pins : Vector (Vector (Option ℕ) branches) w)
    -- the padding challenges
    (dummy : Vector Fq E.σ.k)
    -- each slot's challenge-stack height
    (slotWidths : Vector ℕ w)
    -- the wrap circuit's advice
    (advW : WrapMainAdvice w ncStep E.σ.k σStep.k slotWidths.toList.sum)
    -- fewer branches than the field's characteristic
    (hbr : branches ≤ PALLAS_SCALAR_CARD)
    -- `Vw` satisfies every constraint of the compiled wrap circuit, over the branches' keys and
    -- domains and the SRS's Lagrange points and blinding base
    (hwrap :
      ∀ con ∈
          (compile (a := StatementPacked σStep.k (Type1 Fq) Fq) (b := Unit)
            (wrapMainCircuit (c := Builder Vw (KimchiConstraint Fq))
              (FopParams.ofEnv E Linearization.fqTokens)
              widths
              (stepDomainLog2s stepKeys)
              (stepKeyCells stepKeys)
              pins
              (srsLagrangeTable σStep ncStep (CircuitType.size Fp (StmtVal E.σ.k w)))
              σStep.h
              dummy
              slotWidths
              advW)).constraints,
        ConstraintHolds.Holds Vw con)
    -- the step statement fits key `b`'s Lagrange basis
    (hsize : CircuitType.size Fp (StmtVal E.σ.k w) ≤ stepKeys[b].lagrangeBasis.size)
    -- key `b`'s points are finite
    (hnz : ∀ P ∈ stepKeys[b].comms.indexPoints, P ≠ 0)
    -- the step SRS avoids key `b`'s Lagrange relations
    (havoidS : σStep.Avoids (stepEnvAt σStep stepKeys hkeys b).lagrangeRelations)
    -- the next step circuit's finalize constants
    (P : FopParams Fp)
    -- the step domains the next step circuit's finalize dispatches over
    (domains : List (KnownDomain Fp))
    -- they are key `b`'s finalize constants
    (hP : FopParams.ofEnv (stepEnvAt σStep stepKeys hkeys b) Linearization.fpTokens = P)
    -- key `b`'s candidate domains: distinct, each holding its zero-knowledge rows, its own
    -- among them
    (D : KnownDomains (stepEnvAt σStep stepKeys hkeys b))
    -- they are the next step circuit's
    (hD : D.list = domains)
    -- the next rule verifies at most the tag's `w` slots
    (hn : n ≤ w)
    -- the tag verifies at most `MaxProofsVerified`
    (hw : w ≤ MaxProofsVerified)
    -- the `sg` padding the missing accumulators
    (dummySg : AffinePoint (FVar Fp))
    -- the unfinalized entry padding the statement
    (dummyUnf : UnfVal E.σ.k)
    -- the slot statements' public-input commitment's relations are avoided
    (havoid :
      ∀ (inp : VerifyOneInput σStep.k E.σ.k 1 ncStep w) msg,
        E.σ.Avoids (stepRelationsAt E (inp.statement msg)))
    -- the next step circuit's valuation
    (Vs : Valuation Fp)
    [CheckedType Fp (Builder Vs (KimchiConstraint Fp)) inVal inVar]
    -- the next rule
    (rule :
      inVar →
        CircuitM Fp (Builder Vs (KimchiConstraint Fp)) (Vector PrevStatement n × List (FVar Fp)))
    -- the next step circuit's advice
    (adv : StepMainAdvice n w 1 ncStep E.σ.k σStep.k inVal)
    -- `Vs` satisfies every constraint of the compiled next step circuit
    (hstep :
      ∀ con ∈
          (compile (a := Unit) (b := StmtVal E.σ.k w)
            (stepMainCircuit (c := Builder Vs (KimchiConstraint Fp))
              hw
              (verifyProofAt E)
              P
              domains
              dummySg
              dummyUnf
              rule
              adv)).constraints,
        ConstraintHolds.Holds Vs con) :
    -- the next step circuit's run
    let r :=
      (build
        (stepMain (c := Builder Vs (KimchiConstraint Fp))
          hw
          (verifyProofAt E)
          P
          domains
          dummySg
          dummyUnf
          rule
          adv)
        0).result
    -- the wrap circuit's statement
    let stmt := inputVar (F := Fq) (a := StatementPacked σStep.k (Type1 Fq) Fq)
    -- the wrap circuit's cells over it
    let hd :=
      (build
        (wrapMain (c := Builder Vw (KimchiConstraint Fq))
          (FopParams.ofEnv E Linearization.fqTokens)
          widths
          (stepDomainLog2s stepKeys)
          (stepKeyCells stepKeys)
          pins
          (srsLagrangeTable σStep ncStep (CircuitType.size Fp (StmtVal E.σ.k w)))
          σStep.h
          dummy
          slotWidths
          advW
          stmt)
        (bodyStart (F := Fq) (c := Builder Vw (KimchiConstraint Fq))
          (a := StatementPacked σStep.k (Type1 Fq) Fq))).result
    -- the wrap circuit's branch index reads as `b`
    hd.1.whichBranch.val Vw = (b : Fq) →
    -- slot `i` must verify
    ∀ i : Fin n,
      CircuitType.Reads Vs r.prevs[i].mustVerify true →
      let inp := slotInput hw dummySg r.prevs[i] r.slots[i] r.unfs[i] r.msgs[i]
      -- its masks
      ∀ ms : Vector Bool w,
        CircuitType.Reads Vs inp.proofMask ms →
        -- its wrap proof was made at the wrap circuit's public input
        CircuitType.Reads Vw stmt (inp.packedAt E Vs ms) →
        ∃ (cp : KimchiProof IpaVesta.curve ncStep σStep.k)
          (oldsW : List (IpaVesta.curve.Point × Bool)),
          -- the step proof's public input: the wrap circuit's packed step statement
          let pub := wrapPublicInput (stepEnvAt σStep stepKeys hkeys b) Vw hd.2.statement
          -- the wrap circuit's cells hold `cp`, with keep bits `oldsW`
          ProofReads (wrapSide Vw)
            hd.2.cells.wComm
            hd.2.cells.zComm
            hd.2.cells.tComm
            hd.2.cells.opening
            cp ∧
          OldsRead Vw hd.2.cells.sgOld cp oldsW ∧
          -- the next step circuit's finalize cells hold `cp`'s evaluations and old challenges
          FopTies (stepEnvAt σStep stepKeys hkeys b) cp pub (inp.finalizedHalf Vs) ∧
          -- of `cp` itself: the guards and the deferred `sg` equation
          (Guards IpaVesta.curve stepKeys[b] cp pub →
            SgOk σStep stepKeys[b] cp pub →
            kimchiVerify IpaVesta.curve σStep stepKeys[b] cp pub = true) := by
  subst hP hD
  -- branch `b`'s environment: its key over the step SRS
  let Eb := stepEnvAt σStep stepKeys hkeys b
  -- branch `b`'s domain exponent is its key's
  have hlog : (stepDomainLog2s stepKeys)[b] = Eb.cvk.domainLog2 := by
    simp [Eb, stepDomainLog2s, stepEnvAt, Env.ofInvariants]
  -- branch `b`'s table is its key's Lagrange points: both are the SRS's over the key's domain
  have hlag : srsLagrangeTable σStep ncStep (CircuitType.size Fp (StmtVal E.σ.k w))
      (stepDomainLog2s stepKeys)[b]
      = Eb.cvk.lagrangeBasis.toList.take (CircuitType.size Fp (StmtVal E.σ.k w)) := by
    rw [hlog, Eb.lagrange_eq,
      Ipa.lagrangeBasis_toList_take (N := Eb.cvk.lagrangeBasis.size) _ _ _ _ _ hsize,
      srsLagrangeTable, Eb.omega_eq]
    rfl
  intro r stmt hd hb i hmv inp ms hms htie
  exact wrapStep_kimchiVerify_core E Eb Vw widths
    (stepDomainLog2s stepKeys) (stepKeyCells stepKeys) pins
    (srsLagrangeTable σStep ncStep (CircuitType.size Fp (StmtVal E.σ.k w))) σStep.h dummy
    slotWidths advW hbr hwrap b (by simp [Eb, stepKeyCells, stepEnvAt, Env.ofInvariants]) hlag
    rfl hsize hnz havoidS D hlog hn hw dummySg dummyUnf
    (fun _ _ => (WrapStatement.packed_length _).trans_le
      (show 14 + σStep.k ≤ 2 ^ E.σ.k by rw [hσk, hE]; norm_num [StepIPARounds, WrapIPARounds]))
    havoid Vs rule adv hstep hb i hmv ms hms htie

end Pickles
