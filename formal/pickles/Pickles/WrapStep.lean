import Pickles.StepMain
import Pickles.WrapMain
import Pickles.KeyLayout

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
packed (`VerifyOneInput.packedAt`), whose flattening is the public input the slot verifies the
wrap proof at (`stepPublicInput`). The slot finalizes over the domain its branch
data names, and the finalize read needs that domain to be the step key's: the tie carries the
wrap statement's branch data, which `wrapMain_reads` reads as branch `b`'s domain and mask, to
the slot's packed branch data, whose `log2` and mask cells the slot check bounds. The next step
circuit may be of any tag, its slots from any sources: the slot need only sit at this tag's width
and finalize over the step key's candidate domains.

The step proof is read off the cells of both circuits: its commitments, opening and old
accumulators from the wrap circuit's (`wrapMain_cells`), its evaluations and old challenges
from the slot's. The two circuits pack the slot mask in opposite orders into the branch data,
so the same tie makes the wrap circuit's keep bits the slot's mask (`mask_rev`).
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta
open scoped Kimchi

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
  simp only [BranchData.packed, Fin.getElem_fin, CVar.val_add_, CVar.val_scale_, hdv, h0, h1]
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
  · intro i
    simp only [StatementPacked.claims, Fin.getElem_fin, Vector.getElem_map]
    rw [hbp i i.isLt]
    simp only [WrapStatement.toPacked, Vector.getElem_map]
    rfl

/-- The accumulator a wrap circuit and the next step circuit emit for the step proof they
verify: the wrap message's commitment, with the step message's challenges at slot `i`. -/
def WrapStep.emittedAccumulator {branches mpv ncStep kw ks n wNext sa ncw k : ℕ} {ncs : Fin n → ℕ}
    {slotWidths : Vector (Fin (MaxProofsVerified + 1)) mpv} {ws ss : Fin n → ℕ}
    (Vw : Valuation Fq) (Vs : Valuation Fp) (i : Fin n)
    (verifyOut : WrapMainVerifyOut mpv ncStep kw ks)
    (finalizeOut : WrapMainFinalizeOut branches mpv ncStep kw slotWidths)
    (stepOut : StepMainOut n wNext ws ss sa ncw ncs k ks) : Accumulator IpaVesta.curve ks :=
  Accumulator.ofCells Vw Vs
    (verifyOut.messagesForNextWrapProof finalizeOut).challengePolynomialCommitment
    stepOut.messagesForNextStepProof.oldBulletproofChallenges[i]

/-- The accumulators a wrap circuit and the next step circuit consume: each slot the mask keeps,
its rebuilt wrap message's commitment with the slot's challenges `chals`. -/
def WrapStep.consumedAccumulators {branches w ncStep kw ks n : ℕ}
    {slotWidths : Vector (Fin (MaxProofsVerified + 1)) w}
    (Vw : Valuation Fq) (Vs : Valuation Fp)
    (finalizeOut : WrapMainFinalizeOut branches w ncStep kw slotWidths)
    (chals : Vector (Vector (FVar Fp) ks) n) (hn : n = w) (ms : Vector Bool n) :
    List (Accumulator IpaVesta.curve ks) :=
  ((List.finRange n).filter (ms[·])).map fun j => Accumulator.ofCells Vw Vs
    (finalizeOut.messagesForNextWrapProof (j.cast hn)).challengePolynomialCommitment chals[j]

/-- Filtering a finite range by a lower bound keeps its suffix. -/
private theorem length_kept_finRange (w start : ℕ) :
    ((List.finRange w).filter fun j => decide (start ≤ j.val)).length = w - start := by
  induction w with
  | zero => simp
  | succ w ih =>
    simp only [List.finRange_succ_last, List.filter_append, List.filter_map, List.length_append,
      List.length_map, Function.comp_def, Fin.val_castSucc, List.filter_cons,
      Fin.val_last, List.filter_nil]
    change ((List.finRange w).filter fun j => decide (start ≤ j.val)).length +
      (if decide (start ≤ w) = true then [Fin.last w] else []).length = w + 1 - start
    rw [ih]
    split <;> simp_all <;> omega

/-- A mask keeping the selected branch's suffix consumes exactly that branch's slot count. -/
theorem WrapStep.consumedAccumulators_length {branches w ncStep kw ks n : ℕ}
    {slotWidths : Vector (Fin (MaxProofsVerified + 1)) w}
    (Vw : Valuation Fq) (Vs : Valuation Fp)
    (finalizeOut : WrapMainFinalizeOut branches w ncStep kw slotWidths)
    (chals : Vector (Vector (FVar Fp) ks) n) (hn : n = w) (ms : Vector Bool n)
    (kept : Fin (w + 1))
    (hms : ∀ (j : ℕ) (hj : j < n), ms[j] = decide (w - kept.val ≤ j)) :
    (WrapStep.consumedAccumulators Vw Vs finalizeOut chals hn ms).length = kept.val := by
  subst n
  simp only [WrapStep.consumedAccumulators, List.length_map]
  have hm : (fun j : Fin w => ms[j]) = (fun j : Fin w => decide (w - kept.val ≤ j.val)) :=
    funext fun j => hms j j.isLt
  rw [hm, length_kept_finRange, Nat.sub_sub_self (Nat.le_of_lt_succ kept.isLt)]

/-- `wrapStep_kimchiVerify` for one slot of the next step circuit, from its readings, over the
wrap circuit's constants as given, tied to the step key `KStep` over the step SRS `SStep` by
hypotheses. -/
private theorem wrapStep_kimchiVerify_core
    -- the tag's `w`, the wrap circuit's slots; the wrap circuit's `branches`, the step proof it
    -- verifies at `ncStep` chunks
    {w branches ncStep : ℕ} [NeZero branches]
    -- the cell count of the next step circuit's slot's previous statement
    {sp : ℕ}
    -- the wrap proofs' SRS and key
    (σ : SRS IpaPallas.curve.Point) (cvk : KimchiVK IpaPallas.curve 1)
    -- the SRS and key of the step proof the wrap circuit verifies, at its chunk count
    (SStep : Srs IpaVesta.curve) (KStep : Key IpaVesta.curve ncStep)
    (hnc : ncStep = chunkCount SStep.σ.k KStep.cvk.domainLog2)
    -- the wrap circuit's valuation
    (Vw : Valuation Fq)
    -- the tag's branches: their slot counts, step domains and step keys
    (widths : Vector (Fin (w + 1)) branches) (log2s : Vector ℕ branches)
    (stepKeys : Vector (VkComms ncStep (AffinePoint (FVar Fq))) branches)
    -- each slot's compile-time wrap domain index per branch
    (pins : Vector (Vector (Option ℕ) branches) w)
    -- the Lagrange bases at a step domain, the blinding base, the padding challenges and each
    -- slot's challenge-stack height: constants of the wrap circuit
    (lagrange : ℕ → Vector (Vector IpaVesta.curve.Point ncStep)
      (CircuitType.size Fp (StepStatement (UnfVal σ.k) Fp w)))
    (h : IpaVesta.curve.Point)
    (dummy : Vector Fq σ.k) (slotWidths : Vector (Fin (MaxProofsVerified + 1)) w)
    -- the wrap circuit's advice
    (advW : WrapMainAdvice w ncStep σ.k SStep.σ.k (slotWidths.map Fin.val).sum)
    -- fewer branches than the field's characteristic
    (hbr : branches ≤ PALLAS_SCALAR_CARD)
    -- the active branch: its key and Lagrange bases are `KStep`'s, its blinding base `SStep`'s
    (b : Fin branches)
    (hkeyB : stepKeys[b] = keyCellsOf constPt KStep.cvk)
    (hlag : lagrange log2s[b]
      = KStep.cvk.lagrangePoints SStep.σ (CircuitType.size Fp (StepStatement (UnfVal σ.k) Fp w)))
    (hh : h = SStep.σ.h)
    -- the key's points are finite, and the SRS avoids the key's Lagrange relations, one per
    -- cell of the step statement
    (hnz : ∀ P ∈ KStep.cvk.comms.indexPoints, P ≠ 0)
    (havoidS : SStep.σ.Avoids
      (KStep.cvk.lagrangeRelations SStep.σ.k
        (CircuitType.size Fp (StepStatement (UnfVal σ.k) Fp w))))
    -- branch `b`'s domain is the key's; the tag verifies at most `MaxProofsVerified`
    (hlog : log2s[b] = KStep.cvk.domainLog2) (hw : w ≤ MaxProofsVerified)
    -- the next step circuit's valuation
    (Vs : Valuation Fp) :
    -- the compiled wrap circuit
    let wrap := compileWith (a := StatementPacked SStep.σ.k (Type1 Fq) Fq) (b := Unit)
      (wrapMainCircuit (c := Builder Vw (KimchiConstraint Fq))
        (FopParams.of IpaPallas.curve 1 σ.k Linearization.fqTokens) widths log2s stepKeys
        pins lagrange h dummy slotWidths advW)
    -- `Vw` satisfies every constraint of the compiled wrap circuit
    (∀ con ∈ wrap.constraints, ConstraintHolds.Holds Vw con) →
    -- the wrap circuit's statement and cells
    let stmt := inputVar (F := Fq) (a := StatementPacked SStep.σ.k (Type1 Fq) Fq)
    let wrapFinalizeOut := wrap.result.1.2.1
    let wrapVerifyOut := wrap.result.1.2.2
    -- the wrap circuit's branch index reads as `b`
    wrapFinalizeOut.whichBranch.val Vw = (b : Fq) →
    -- a slot of the next step circuit, at this tag's width, from its cells: its finalize reads
    -- as the key's scalar half at its expanded challenges, and its branch data carries a domain
    -- exponent and a mask
    ∀ (dummySg : AffinePoint (FVar Fp)) (prev : PrevStatement sp)
      (s : SlotVar w 1 ncStep σ.k SStep.σ.k) (u : UnfVar σ.k) (msg : FVar Fp)
      (expanded : Vector (FVar Fp) SStep.σ.k),
    let inp := slotInput hw dummySg prev s u msg
    inp.ScalarReads SStep.σ KStep.cvk Vs expanded →
    ∀ (n0 : ℕ) (ms0 : Vector Bool MaxProofsVerified), n0 < 2 ^ 16 →
      inp.branchData.domainLog2.val Vs = (n0 : Fp) →
      CircuitType.Reads Vs inp.branchData.proofsVerifiedMask ms0 →
    -- its masks
    ∀ ms : Vector Bool w, CircuitType.Reads Vs inp.proofMask ms →
      -- its wrap proof was made at the wrap circuit's public input
      CircuitType.Reads Vw stmt (inp.packedAt cvk Vs ms) →
      ∃ (cp : KimchiProof IpaVesta.curve ncStep SStep.σ.k)
        (oldsW : Vector (IpaVesta.curve.Point × Bool) w),
        -- the step proof's public input: the wrap circuit's packed step statement
        let pub := wrapPublicInput SStep.σ KStep.cvk Vw wrapVerifyOut.statement
        -- the wrap circuit's cells hold `cp`
        ProofReads (wrapSide Vw)
          wrapVerifyOut.cells.wComm
          wrapVerifyOut.cells.zComm
          wrapVerifyOut.cells.tComm
          wrapVerifyOut.cells.opening
          cp ∧
        OldsRead Vw wrapVerifyOut.cells.sgOld cp oldsW ∧
        -- the next step circuit's finalize cells hold `cp`'s evaluations and old challenges
        FopTies SStep.σ KStep.cvk cp pub (inp.finalizedHalf Vs) ∧
        -- the link emits `cp`'s deferred obligation: its wrap message's commitment, with the
        -- expanded challenges
        Accumulator.ofCells Vw Vs
            (wrapVerifyOut.messagesForNextWrapProof wrapFinalizeOut).challengePolynomialCommitment
            expanded
          = ⟨cp.opening.sg, wireChallenges SStep.σ KStep.cvk cp pub⟩ ∧
        -- the link consumes `cp`'s old accumulators
        WrapStep.consumedAccumulators Vw Vs wrapFinalizeOut inp.prevChallenges rfl ms
          = cp.olds.toList ∧
        -- the slot's mask keeps exactly the last `widths[b]` slots
        (∀ (j : ℕ) (hj : j < w), ms[j] = decide (w - (widths[b] : ℕ) ≤ j)) ∧
        -- the wrap circuit hashes its messages
        wrapVerifyOut.HashesMessages Vw dummy stmt wrapFinalizeOut ∧
        -- of `cp` itself: the guards and the deferred `sg` equation
        (Guards IpaVesta.curve KStep.cvk cp pub →
          SgOk SStep.σ KStep.cvk cp pub →
          kimchiVerify IpaVesta.curve SStep.σ KStep.cvk cp pub = true) := by
  intro wrap hwrap
  rw [show wrap.result.1.2 = _ from compileWith_wrapMainCircuit_cells _ _ _ _ _ _ _ _ _ _]
  intro stmt wrapFinalizeOut wrapVerifyOut hb dummySg prev s u msg expanded inp hscal n0 ms0
      hn0 hdv hmsR ms hms htie
  -- the wrap side: the body's constraints hold, so its reads do
  have hbody : ∀ con ∈ (build (wrapMain (c := Builder Vw (KimchiConstraint Fq))
      (FopParams.of IpaPallas.curve 1 σ.k Linearization.fqTokens) widths log2s stepKeys pins
      lagrange h dummy slotWidths advW stmt)
      (bodyStart (F := Fq) (c := Builder Vw (KimchiConstraint Fq))
        (a := StatementPacked SStep.σ.k (Type1 Fq) Fq))
      ).constraints, ConstraintHolds.Holds Vw con := fun con hc =>
    hwrap con (mem_compileWith_wrapMainCircuit _ _ _ _ _ _ _ _ _ _ hc)
  obtain ⟨b', hb', hwb, -, hmask, -, hbd, -⟩ := (builder_spec_iff _ _).mp
    (wrapMain_reads σ Vw widths log2s stepKeys pins lagrange h dummy slotWidths advW stmt hw
      hbr) _ hbody
  -- the circuit's branch is `b`: both are below the field's characteristic
  have hbb : b' = b.val := CharP.natCast_injOn_Iio Fq PALLAS_SCALAR_CARD
    (Set.mem_Iio.2 (by omega)) (Set.mem_Iio.2 (by omega)) (hwb.symm.trans hb)
  subst hbb
  obtain ⟨-, -, -, hgrp⟩ := (builder_spec_iff _ _).mp
    (wrapMain_verifyReads σ SStep KStep hnc Vw widths log2s stepKeys pins lagrange h dummy
      slotWidths advW stmt hw hbr hh hnz havoidS) _ hbody b hb hkeyB hlag
  -- the wrap circuit's proof cells and accumulators, on the curve
  obtain ⟨hacc, pr, hcells, hon⟩ := (builder_spec_iff _ _).mp
    (wrapMain_cells (FopParams.of IpaPallas.curve 1 σ.k Linearization.fqTokens) Vw widths log2s
      stepKeys pins lagrange h dummy slotWidths advW stmt) _ hbody
  have hhash := ((builder_spec_iff _ _).mp
    (wrapMain_statement (FopParams.of IpaPallas.curve 1 σ.k Linearization.fqTokens) Vw widths
      log2s stepKeys pins lagrange h dummy slotWidths advW stmt KStep.cvk.nc_pos) _ hbody).2.2.2.2
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
  have hL : KStep.cvk.domainLog2 < 255 := KStep.domainLog2_le.trans_lt (by decide)
  have hn0p : 4 * n0 + t < PALLAS_BASE_CARD := by norm_num [PALLAS_BASE_CARD]; omega
  have hlog' : log2s[b.val] = KStep.cvk.domainLog2 := by simpa using hlog
  rw [hsum, hlog'] at hbd
  simp only [ToNat.toNat, ZMod.val_natCast_of_lt hn0p] at hbd
  have hnat : 4 * n0 + t = 4 * KStep.cvk.domainLog2 + sN :=
    CharP.natCast_injOn_Iio Fq PALLAS_SCALAR_CARD
    (Set.mem_Iio.2 (by norm_num [PALLAS_SCALAR_CARD]; omega))
    (Set.mem_Iio.2 (by norm_num [PALLAS_SCALAR_CARD]; omega)) (by push_cast at hbd ⊢; exact hbd)
  -- the slot's domain is the key's
  have hdom : inp.branchData.domainLog2.val Vs = (KStep.cvk.domainLog2 : Fp) := by
    rw [hdv, show n0 = KStep.cvk.domainLog2 by omega]
  -- the slot's mask is the wrap mask reversed
  have hrev := mask_rev hw _ ms0 (htdef ▸ (by omega : t = sN))
  have hmsj : ∀ j : Fin w, ms[j] = ms0[MaxProofsVerified - w + j] :=
    reads_drop (by simpa [MaxProofsVerified] using hw) hmsR hms
  -- so it keeps exactly the last `widths[b]` slots
  have hkept : ∀ (j : ℕ) (hj : j < w), ms[j] = decide (w - (widths[b.val] : ℕ) ≤ j) := by
    intro j hj
    rw [show ms[j] = ms[(⟨j, hj⟩ : Fin w)] from rfl, hmsj ⟨j, hj⟩, hrev ⟨j, hj⟩]
    simp only [decide_eq_decide]
    omega
  -- so the wrap circuit's keep bit for slot `j` reads as `ms[j]`
  have hkeep : ∀ j : Fin w, (↑wrapFinalizeOut.mask.reverse[j] : CVar Fq).val Vw = bit ms[j] := by
    intro j
    have h := CircuitType.reads_boolVar.mp
      (CircuitType.reads_vector.mp hmask (w - 1 - j) (by omega))
    simp only [Vector.getElem_ofFn] at h
    rw [Fin.getElem_fin, Vector.getElem_reverse, h, hmsj j, hrev j]
  -- the step proof the cells hold: its group half from the wrap circuit's cells, its evaluations
  -- and kept old challenges from the next step circuit's
  have hcells' : wrapVerifyOut.cells = ivpInputOf stmt.claims.deferredValues wrapFinalizeOut.sgOld
      wrapFinalizeOut.key pr := hcells
  let P : Fin w → IpaVesta.curve.Point := fun j =>
    readPt (C := IpaVesta.curve) Vw wrapFinalizeOut.stepAccs[j].pt
  let U : Fin w → Vector Fp SStep.σ.k := fun j => inp.prevChallenges[j].map (·.val Vs)
  let cp := pr.read (wrapSide Vw) (inp.evals.evals.map fun v => v.map (·.val Vs))
    (.carried (inp.evals.pub.map fun v => v.map (·.val Vs))) (inp.evals.ftEval1.val Vs)
    (((List.finRange w).filter fun j => ms[j]).map fun j =>
      (⟨P j, U j⟩ : Accumulator IpaVesta.curve SStep.σ.k)).toArray
  let oldsW : Vector (IpaVesta.curve.Point × Bool) w := Vector.ofFn fun j => (P j, ms[j])
  have hpr : ProofReads (wrapSide Vw) wrapVerifyOut.cells.wComm wrapVerifyOut.cells.zComm
      wrapVerifyOut.cells.tComm wrapVerifyOut.cells.opening cp := by
    rw [hcells']
    exact IvpProof.read_proofReads _ _ _ _ _ _ hon
  have hol : OldsRead Vw wrapVerifyOut.cells.sgOld cp oldsW := by
    rw [hcells']
    refine ⟨?_, ?_⟩
    · rw [← Vector.toList_map, ← Vector.toList_map]
      refine forall₂_toList_iff.mpr fun j => ?_
      simp only [ivpInputOf, WrapMainFinalizeOut.sgOld, oldsW, Fin.getElem_fin,
        Vector.getElem_map, Vector.getElem_ofFn]
      exact ⟨onCurveAt_readPt (hacc j), hkeep j⟩
    · simp [cp, IvpProof.read, oldsW, Vector.toList_ofFn, List.ofFn_eq_map, List.filter_map,
        Function.comp_def]
  have hf : FopTies SStep.σ KStep.cvk cp
      (wrapPublicInput SStep.σ KStep.cvk Vw wrapVerifyOut.statement)
      (inp.finalizedHalf Vs) := by
    refine ⟨?_, rfl, rfl, rfl⟩
    have hm : (inp.finalizedHalf Vs).maskVals = Vector.ofFn fun j : Fin w => ms[j] := by
      refine Vector.ext fun j hj => ?_
      have h := CircuitType.reads_boolVar.mp (CircuitType.reads_vector.mp hms j hj)
      simp only [ScalarHalf.maskVals, VerifyOneInput.finalizedHalf, ScalarHalf.step,
        Vector.getElem_map, Vector.getElem_ofFn, h]
      cases ms[j]'hj <;> simp [bit]
    have hp : (inp.finalizedHalf Vs).prevVals = Vector.ofFn fun j : Fin w => U j := by
      refine Vector.ext fun j hj => ?_
      simp [ScalarHalf.prevVals, VerifyOneInput.finalizedHalf, ScalarHalf.step, U]
    rw [hm, hp, Vector.toList_zipWith, Vector.toList_ofFn, Vector.toList_ofFn,
      flatten_zipWith_keep]
    simp [cp, IvpProof.read]
  obtain ⟨v, hv, hv1⟩ := hgrp cp oldsW hpr hol
  have hcc := claimsCast_of_reads stmt _ htie
  -- the link's accumulators: the opening `sg` is `cp`'s, and `cp`'s old accumulators are the
  -- masked slots'
  have hsg : readPt (C := IpaVesta.curve) Vw wrapVerifyOut.cells.opening.sg = cp.opening.sg := by
    rw [hcells']
    rfl
  have hcons : WrapStep.consumedAccumulators Vw Vs wrapFinalizeOut inp.prevChallenges rfl ms
      = cp.olds.toList := by
    simp [WrapStep.consumedAccumulators, cp, IvpProof.read, P, U, Accumulator.ofCells]
  clear_value oldsW cp U P
  obtain ⟨hE, hK⟩ := hscal hdom cp (wrapPublicInput SStep.σ KStep.cvk Vw wrapVerifyOut.statement) Vw
    stmt.claims v hv hv1 hcc hf
  refine ⟨cp, oldsW, hpr, hol, hf, ?_, hcons, hkept, hhash, hK⟩
  simp only [Accumulator.ofCells, hsg, hE]

/-- **The wrap circuit's step proof verifies.** Let `Vw` satisfy the wrap circuit built from the
tag's step keys `stepKeys` and the step SRS `SStep`, its branch index reading as branch `b`,
whose key is the checked key `KStep`, and let `Vs` satisfy the next step circuit of any tag, its
slots from any sources, compiled with the step proofs' finalize constants (`FopParams.of`). For
every must-verify slot over the domains `D`, at this tag's width, whose wrap proof was made at
the wrap circuit's public input, the wrap circuit's cells hold a step proof; the slot's finalize
cells hold its evaluations and old challenges, and `kimchiVerify` accepts it under `SgOk`,
with its guards derived from `StepKeyLayout`. -/
theorem wrapStep_kimchiVerify
    -- the next rule's `n` slots, its tag's `wNext`; this tag's `w`, the wrap circuit's slots; the
    -- wrap circuit's `branches`, the step proof it verifies at `ncStep` chunks
    {n wNext w branches ncStep : ℕ} {ncs : Fin n → ℕ}
    [NeZero branches]
    -- the next rule's input and output, as values and as cells
    {inVal inVar outVal outVar : Type}
    [CircuitType Fp inVal inVar] [CircuitType Fp outVal outVar]
    -- each of the next rule's slots' previous statement's cell count
    {ss : Fin n → ℕ}
    -- the wrap proofs' SRS and key
    (σ : SRS IpaPallas.curve.Point) (cvk : KimchiVK IpaPallas.curve 1)
    -- the wrap SRS has the deployed size, `2 ^ WrapIPARounds` points
    (hE : σ.k = WrapIPARounds)
    -- the step SRS
    (SStep : Srs IpaVesta.curve)
    -- the step SRS has the deployed size, `2 ^ StepIPARounds` points
    (hσk : SStep.σ.k = StepIPARounds)
    -- the tag's step keys, one per branch
    (stepKeys : Vector (KimchiVK IpaVesta.curve ncStep) branches)
    -- the branch the wrap circuit takes
    (b : Fin branches)
    -- its key is a checked key, at the step SRS's chunk count
    (KStep : Key IpaVesta.curve ncStep) (hkey : KStep.cvk = stepKeys[b])
    (hnc : ncStep = chunkCount SStep.σ.k KStep.cvk.domainLog2)
    -- the Lagrange tables the wrap circuit bakes in, per step domain: at branch `b`'s, its key's
    -- points
    (lagrange : ℕ → Vector (Vector IpaVesta.curve.Point ncStep)
      (CircuitType.size Fp (StepStatement (UnfVal σ.k) Fp w)))
    (hlag : lagrange KStep.cvk.domainLog2
      = KStep.cvk.lagrangePoints SStep.σ (CircuitType.size Fp (StepStatement (UnfVal σ.k) Fp w)))
    -- the wrap circuit's valuation
    (Vw : Valuation Fq)
    -- the tag's branches' slot counts
    (widths : Vector (Fin (w + 1)) branches)
    -- the selected key declares this statement's size and this branch's slot count
    (hlayout : StepKeyLayout KStep.cvk w (widths[b] : ℕ))
    -- each slot's compile-time wrap domain index per branch
    (pins : Vector (Vector (Option ℕ) branches) w)
    -- the padding challenges
    (dummy : Vector Fq σ.k)
    -- each slot's challenge-stack height
    (slotWidths : Vector (Fin (MaxProofsVerified + 1)) w)
    -- the wrap circuit's advice
    (advW : WrapMainAdvice w ncStep σ.k SStep.σ.k (slotWidths.map Fin.val).sum)
    -- fewer branches than the field's characteristic
    (hbr : branches ≤ PALLAS_SCALAR_CARD)
    -- key `b`'s points are finite
    (hnz : ∀ P ∈ stepKeys[b].comms.indexPoints, P ≠ 0)
    -- the step SRS avoids key `b`'s Lagrange relations, one per cell of the step statement
    (havoidS : SStep.σ.Avoids (stepKeys[b].lagrangeRelations SStep.σ.k
      (CircuitType.size Fp (StepStatement (UnfVal σ.k) Fp w))))
    -- the step domains the next step circuit's finalize dispatches over
    (domains : List (KnownDomain Fp))
    -- the candidate domains, each holding the chunk count's zero-knowledge rows
    (D : KnownDomains ncStep)
    -- the next rule has at most `MaxProofsVerified` slots
    (hn : n ≤ MaxProofsVerified)
    -- the tag verifies at most `MaxProofsVerified`
    (hw : w ≤ MaxProofsVerified)
    -- the next step circuit's slots' sources, each verifying at most `MaxProofsVerified`
    -- accumulators
    (srcs : Fin n → SlotSource 1 SStep.σ.k)
    (hws : ∀ i, SlotSource.widths wNext srcs i ≤ MaxProofsVerified)
    -- the `sg` padding the missing accumulators
    (dummySg : AffinePoint (FVar Fp))
    -- the unfinalized entry padding the statement
    (dummyUnf : UnfVal σ.k)
    -- the next step circuit's valuation
    (Vs : Valuation Fp)
    [CheckedType Fp (Builder Vs (KimchiConstraint Fp)) inVal inVar]
    -- the next rule
    (rule :
      inVar →
        CircuitM Fp (Builder Vs (KimchiConstraint Fp)) (((i : Fin n) → PrevStatement (ss i)) ×
          outVar))
    -- the next step circuit's advice
    (adv : StepMainAdvice n wNext (SlotSource.widths wNext srcs) 1 ncs σ.k SStep.σ.k inVal) :
    -- the compiled wrap circuit, over the branches' keys and domains, the Lagrange tables and the
    -- SRS's blinding base
    let wrap :=
      compileWith (a := StatementPacked SStep.σ.k (Type1 Fq) Fq) (b := Unit)
        (wrapMainCircuit (c := Builder Vw (KimchiConstraint Fq))
          (FopParams.of IpaPallas.curve 1 σ.k Linearization.fqTokens)
          widths
          (stepDomainLog2s stepKeys)
          (stepKeyCells stepKeys)
          pins
          lagrange
          SStep.σ.h
          dummy
          slotWidths
          advW)
    -- the compiled next step circuit: its rows, and the cells of the run that emitted them
    let step :=
      compileWith (a := Unit) (b := StepStatement (UnfVal σ.k) Fp wNext)
        (stepMainCircuit (c := Builder Vs (KimchiConstraint Fp)) (outVal := outVal)
          srcs
          hws
          σ.h
          (fun j => FopParams.of IpaVesta.curve (ncs j) SStep.σ.k Linearization.fpTokens)
          domains
          dummySg
          dummyUnf
          rule
          adv)
    -- `Vw` satisfies every constraint of the compiled wrap circuit
    (∀ con ∈ wrap.constraints, ConstraintHolds.Holds Vw con) →
    -- `Vs` satisfies every constraint of the compiled next step circuit
    (∀ con ∈ step.constraints, ConstraintHolds.Holds Vs con) →
    -- the next step circuit's run
    let stepOut := step.result.1.2
    -- the wrap circuit's statement
    let wrapStmt := inputVar (F := Fq) (a := StatementPacked SStep.σ.k (Type1 Fq) Fq)
    -- the wrap circuit's cells over it
    let wrapFinalizeOut := wrap.result.1.2.1
    let wrapVerifyOut := wrap.result.1.2.2
    -- the wrap circuit's branch index reads as `b`
    wrapFinalizeOut.whichBranch.val Vw = (b : Fq) →
    -- slot `i` finalizes this wrap circuit's step proofs and must verify
    ∀ (i : Fin n) (hci : ncs i = ncStep),
      CircuitType.Reads Vs (stepOut.prevs i).mustVerify true →
      -- it finalizes over key `b`'s domains, at this tag's width
      (srcs i).domains domains = D.list →
      ∀ hwi : SlotSource.widths wNext srcs i = w,
      let inp := slotInput (hws i) dummySg (stepOut.prevs i) (stepOut.slots i) stepOut.unfs[i]
          stepOut.msgs[i]
      -- its masks
      ∀ ms : Vector Bool (SlotSource.widths wNext srcs i),
        CircuitType.Reads Vs inp.proofMask ms →
        -- its wrap proof was made at the wrap circuit's public input
        CircuitType.Reads Vw wrapStmt (inp.packedAt cvk Vs ms) →
        ∃ (cp : KimchiProof IpaVesta.curve ncStep SStep.σ.k)
          (oldsW : Vector (IpaVesta.curve.Point × Bool) w),
          -- the step proof's public input: the wrap circuit's packed step statement
          let pub := wrapPublicInput SStep.σ stepKeys[b] Vw wrapVerifyOut.statement
          -- the wrap circuit's cells hold `cp`, with keep bits `oldsW`
          ProofReads (wrapSide Vw)
            wrapVerifyOut.cells.wComm
            wrapVerifyOut.cells.zComm
            wrapVerifyOut.cells.tComm
            wrapVerifyOut.cells.opening
            cp ∧
          OldsRead Vw wrapVerifyOut.cells.sgOld cp oldsW ∧
          -- the next step circuit's finalize cells hold `cp`'s evaluations and old challenges
          FopTies SStep.σ stepKeys[b] cp pub
            ((hci ▸ inp : VerifyOneInput (ss i) SStep.σ.k σ.k 1 ncStep
              (SlotSource.widths wNext srcs i)).finalizedHalf Vs) ∧
          -- the link emits `cp`'s deferred obligation, as its outgoing messages carry it
          WrapStep.emittedAccumulator Vw Vs i wrapVerifyOut wrapFinalizeOut stepOut
            = ⟨cp.opening.sg, wireChallenges SStep.σ stepKeys[b] cp pub⟩ ∧
          -- the link consumes `cp`'s old accumulators, as its incoming messages were rebuilt
          WrapStep.consumedAccumulators Vw Vs wrapFinalizeOut inp.prevChallenges hwi ms
            = cp.olds.toList ∧
          -- the slot's mask keeps exactly the last `widths[b]` slots
          (∀ (j : ℕ) (hj : j < SlotSource.widths wNext srcs i),
            ms[j] = decide (w - (widths[b] : ℕ) ≤ j)) ∧
          -- the wrap circuit and the next step circuit hash their messages
          wrapVerifyOut.HashesMessages Vw dummy wrapStmt wrapFinalizeOut ∧
          stepOut.HashesMessages Vs ∧
          -- of `cp` itself: only the deferred `sg` equation remains
          (SgOk SStep.σ stepKeys[b] cp pub →
            kimchiVerify IpaVesta.curve SStep.σ stepKeys[b] cp pub = true) := by
  rw [← hkey] at hnz havoidS
  -- branch `b`'s domain exponent is its key's
  have hlog : (stepDomainLog2s stepKeys)[b] = KStep.cvk.domainLog2 := by
    simp [stepDomainLog2s, hkey]
  -- branch `b`'s table is its key's Lagrange points
  have hlagb : lagrange (stepDomainLog2s stepKeys)[b]
      = KStep.cvk.lagrangePoints SStep.σ
          (CircuitType.size Fp (StepStatement (UnfVal σ.k) Fp w)) := by
    rw [hlog]
    exact hlag
  intro wrap step hwrap hstep
  rw [show step.result.1.2 = _ from compileWith_stepMainCircuit_cells srcs hws _ _ _ _ _ _ _]
  intro stepOut wrapStmt wrapFinalizeOut wrapVerifyOut hb i hci
  cases hci
  intro hmv hdi hwi inp ms hms htie
  rw [← hkey]
  -- the step side: slot `i` finalizes, over the domain its branch data names; a slot over
  -- branch `b`'s domains reads as its key's scalar half
  obtain ⟨-, -, hscal, -, -, n0, ms0, hn0, hdv, hmsR⟩ := (builder_spec_iff _ _).mp
    (stepMain_reads (outVal := outVal) (ks := SStep.σ.k) σ
      (fun j => FopParams.of IpaVesta.curve (ncs j) SStep.σ.k Linearization.fpTokens) domains
      SStep.rounds_small srcs
      (fun j inp e => ∀ (K : Key IpaVesta.curve (ncs j)) (Ds : KnownDomains (ncs j)),
        (srcs j).domains domains = Ds.list → inp.ScalarReads SStep.σ K.cvk Vs e)
      (fun j vk inp => by
        rw [builder_spec_iff]
        intro nv hsat hmsk hmv' h1 K Ds hdj
        rw [hdj] at hsat h1 ⊢
        exact (builder_spec_iff _ _).mp (verifyOne_scalarReads SStep K Ds (hws j)
          (verifyProofWith σ.h (srcs j).lagrange) vk inp) nv hsat hmsk hmv' h1)
      hn hws dummySg dummyUnf rule adv
      (by rw [hσk, hE]; decide))
      0 (fun con hc => hstep con (mem_compileWith_stepMainCircuit srcs hws _ _ _ _ _ _ _ hc)) i hmv
  have hhashS := ((builder_spec_iff _ _).mp
    (stepMain_out (outVal := outVal) srcs hws σ.h
      (fun j => FopParams.of IpaVesta.curve (ncs j) SStep.σ.k Linearization.fpTokens)
      domains dummySg dummyUnf rule adv) 0
    (fun con hc => hstep con (mem_compileWith_stepMainCircuit srcs hws _ _ _ _ _ _ _ hc))).2.2
  -- the slot is at this tag's width
  subst hwi
  obtain ⟨cp, oldsW, hpr, hol, hf, hemit, hcons, hkept, hhashW, hK⟩ :=
    wrapStep_kimchiVerify_core σ cvk SStep KStep hnc Vw widths
    (stepDomainLog2s stepKeys) (stepKeyCells stepKeys) pins lagrange SStep.σ.h dummy
    slotWidths advW hbr b (by simp [stepKeyCells, hkey]) hlagb
    rfl hnz havoidS hlog hw Vs hwrap hb dummySg (stepOut.prevs i) (stepOut.slots i) stepOut.unfs[i]
        stepOut.msgs[i] _
    (hscal KStep D hdi) n0 ms0 hn0 hdv hmsR ms hms htie
  have hguards : Guards IpaVesta.curve KStep.cvk cp
      (wrapPublicInput SStep.σ KStep.cvk Vw wrapVerifyOut.statement) := by
    constructor
    · rw [hlayout.prevChallenges_eq, ← Array.length_toList, ← hcons]
      exact WrapStep.consumedAccumulators_length _ _ _ _ _ _ _ hkept
    · rw [hlayout.publicCount_eq, wrapPublicInput_size, hE]
  exact ⟨cp, oldsW, hpr, hol, hf, hemit, hcons, hkept, hhashW, hhashS, hK hguards⟩

end Pickles
