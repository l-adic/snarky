import Pickles.StepMain
import Pickles.WrapMain

set_option mvcgen.warning false

/-!
# Every must-verify slot's wrap proof verifies

A step circuit verifies up to `MaxProofsVerified` previous wrap proofs, each across two circuits:
the step circuit checks its group half, and the next wrap circuit's finalize block checks its
scalar half. This module joins the two reads. For any rule, under a valuation satisfying the step
circuit's constraints and one satisfying the wrap circuit's (`wrapMain`), every wrap proof that
a slot the rule marks must-verify reads as is accepted by `kimchiVerify`.

## Main results

* `stepWrap_kimchiVerify`: the two circuits' runs, each satisfied under its own valuation, with
  the step circuit's output read as the wrap circuit's public input, the pins at the key's wrap
  domain and the readings, make `kimchiVerify` accept every must-verify slot's wrap proof.

## Implementation notes

The wrap circuit has one slot per proof the tag verifies, `w`, front-padded: step slot `i` is
wrap slot `i + (w − n)`. The wrap proofs are at one chunk, the chunk count the wrap circuit
allocates their evaluations at. The step circuit sets `shouldFinalize` on every
must-verify slot, and the tie carries that bit to the finalize block, where it forces the slot
to finalize.

The public-input tie is stated on reduced values: each wrap public-input cell holds an `Fq`
value, the step circuit's matching output an `Fp` one. The x_hat ladder bounds every packed
cell below `2^254 < p` (`PackedScalar.Bound`), so the reduction is injective and the tie fixes
each slot's claims (`SplitClaimsCast`) and its `shouldFinalize` bit.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta
open scoped Kimchi

/-- A bounded cell's representative is below `2^254`: `2z + bb` with `z < 2^253`, or a bit. -/
private theorem val_lt_of_bound {Vs : Valuation Fq} {k : PackedScalar Fq} (hb : k.Bound Vs) :
    ZMod.val (k.cell.val Vs) < 2 ^ 254 := by
  have hq : (2 : ℕ) ^ 254 < PALLAS_SCALAR_CARD := by norm_num [PALLAS_SCALAR_CARD]
  have hcell : ∀ w ≤ 253, ∀ s : FVar Fq, CellBound Vs w s → ZMod.val (s.val Vs) < 2 ^ 254 := by
    intro w hw s ⟨z, bb, h0, hlt, hval⟩
    have hz : z < 2 ^ 253 := lt_of_lt_of_le hlt (pow_le_pow_right₀ (by norm_num) hw)
    obtain ⟨N, hNz⟩ := Int.eq_ofNat_of_zero_le
      (show 0 ≤ 2 * z + (if bb then 1 else 0) by cases bb <;> simp <;> omega)
    have hN : N < 2 ^ 254 := by
      have : (N : ℤ) < 2 ^ 254 := by rw [← hNz]; cases bb <;> simp <;> omega
      exact_mod_cast this
    rw [← hval, hNz, Int.cast_natCast, ZMod.val_natCast_of_lt (hN.trans hq)]
    exact hN
  cases k with
  | full s => exact hcell 253 le_rfl s hb
  | b128 s => exact hcell 127 (by norm_num) s hb
  | b10 s => exact hcell 9 (by norm_num) s hb
  | bit b =>
    obtain ⟨bb, hbb⟩ := hb
    show ZMod.val ((↑b : CVar Fq).val Vs) < _
    rw [hbb]
    cases bb <;> simp [bit, ZMod.val_one_eq_one_mod, PALLAS_SCALAR_CARD]

/-- A bounded cell is the lift of its own public-input entry: reducing into the step field and
lifting back is the identity below `2^254 < p`. -/
private theorem cell_eq_redFq {Vs : Valuation Fq} {k : PackedScalar Fq} (hb : k.Bound Vs) :
    k.cell.val Vs = redFq (PackedScalar.reduced IpaVesta.curve Vs k) := by
  have hN := val_lt_of_bound hb
  have hp : (2 : ℕ) ^ 254 < PALLAS_BASE_CARD := by norm_num [PALLAS_BASE_CARD]
  have hr : PackedScalar.reduced IpaVesta.curve Vs k
      = ((ZMod.val (k.cell.val Vs) : ℕ) : Fp) := by
    cases k <;> rfl
  rw [hr, redFq, ZMod.val_natCast_of_lt (hN.trans hp), ZMod.natCast_zmod_val]

/-- Two flat maps with blocks of one length that agree, read through `g`, up to their tails
agree block by block. -/
private theorem map_flatMap_block {α β γ δ : Type} (f : α → List β) (h : γ → List δ)
    (g : β → δ) (L : ℕ) (hf : ∀ a, (f a).length = L) (hh : ∀ c, (h c).length = L) :
    ∀ (as : List α) (cs : List γ) (t : List β) (t' : List δ), as.length = cs.length →
      (as.flatMap f ++ t).map g = cs.flatMap h ++ t' →
      ∀ j (hj : j < as.length) (hj' : j < cs.length), (f as[j]).map g = h cs[j]
  | [], _, _, _, _, _, j, hj, _ => absurd hj (Nat.not_lt_zero _)
  | _ :: _, [], _, _, hl, _, _, _, _ => by simp at hl
  | a :: as, c :: cs, t, t', hl, he, j, hj, hj' => by
    simp only [List.flatMap_cons, List.append_assoc, List.map_append] at he
    obtain ⟨h0, hrest⟩ := List.append_inj he (by simp [hf, hh])
    cases j with
    | zero => exact h0
    | succ j =>
      simp only [List.length_cons] at hl hj hj'
      exact map_flatMap_block f h g L hf hh as cs t t' (by omega)
        (by simpa [List.map_append] using hrest) j (by omega) (by omega)

open Snarky.Kimchi in
/-- One slot across the tie: its cells, read, are the wrap statement's slot reduced, and the wrap
side's ladders bound that slot; then the wrap circuit's claims hold the step circuit's lifted
(`SplitClaimsCast`) and both read one `shouldFinalize` bit. -/
private theorem slot_cast {k : ℕ} {Vg : Valuation Fp} {Vs : Valuation Fq} (u : UnfVar k)
    (sp : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type2 (SplitField (FVar Fq) (BoolVar Fq))))
    (a : AllocUnfinalized k (FVar Fq) (BoolVar Fq) (Type2 (FVar Fq)))
    (hblock : (CircuitType.varToFields (F := Fp) (val := UnfVal k) u).toList.map (·.val Vg)
      = sp.packed.map (PackedScalar.reduced IpaVesta.curve Vs))
    (hbnd : ∀ x ∈ sp.packed, x.Bound Vs)
    (hsr : SplitClaimsRead Vs a.toUnfinalized sp) :
    SplitClaimsCast Vg u.toUnfinalized Vs a.toUnfinalized ∧
      ∃ bb : Bool, CircuitType.Reads Vg u.toUnfinalized.shouldFinalize bb ∧
        CircuitType.Reads Vs a.toUnfinalized.shouldFinalize bb := by
  -- each wrap entry is the lift of the step cell it is read against
  have hB : ∀ x ∈ sp.packed, x.cell.val Vs = redFq (PackedScalar.reduced IpaVesta.curve Vs x) :=
    fun x hx => cell_eq_redFq (hbnd x hx)
  rw [AllocUnfinalized.varToFields_toList] at hblock
  simp only [UnfinalizedProof.packed, List.map_append, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.cons.injEq] at hblock
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, htail⟩ := hblock
  obtain ⟨hbp, hsf⟩ := List.append_inj htail (by simp)
  simp only [List.cons.injEq, and_true] at hsf
  have mem : ∀ x, x ∈ sp.packed ↔ x ∈ UnfinalizedProof.packed sp := fun _ => Iff.rfl
  obtain ⟨ha, hbe, hg, hz, hxi, hbps, hsfe, hdig, hscip, hsb, hsperm, hszm, hszn⟩ := hsr
  -- an entry of the slot, read against the step cell `v`, is `v` lifted
  have e : ∀ {x : PackedScalar Fq} {v : Fp}, x ∈ UnfinalizedProof.packed sp →
      v = PackedScalar.reduced IpaVesta.curve Vs x → x.cell.val Vs = redFq v :=
    fun hx hv => (hB _ hx).trans (by rw [hv])
  have mem : ∀ {x : PackedScalar Fq}, x ∈ UnfinalizedProof.packed sp ↔ x ∈ sp.packed :=
    Iff.rfl
  -- the scalar claims and the digest
  have fa : a.alpha.val Vs = redFq (u.alpha.val Vg) := by
    have := e (x := .b128 sp.deferredValues.plonk.alpha.val) (by simp [UnfinalizedProof.packed]) c14
    simpa [PackedScalar.cell, ha, AllocUnfinalized.toUnfinalized] using this
  have fb : a.beta.val Vs = redFq (u.beta.val Vg) := by
    have := e (x := .b128 sp.deferredValues.plonk.beta.val) (by simp [UnfinalizedProof.packed]) c12
    simpa [PackedScalar.cell, hbe, AllocUnfinalized.toUnfinalized] using this
  have fg : a.gamma.val Vs = redFq (u.gamma.val Vg) := by
    have := e (x := .b128 sp.deferredValues.plonk.gamma.val) (by simp [UnfinalizedProof.packed])
      c13
    simpa [PackedScalar.cell, hg, AllocUnfinalized.toUnfinalized] using this
  have fz : a.zeta.val Vs = redFq (u.zeta.val Vg) := by
    have := e (x := .b128 sp.deferredValues.plonk.zeta.val) (by simp [UnfinalizedProof.packed]) c15
    simpa [PackedScalar.cell, hz, AllocUnfinalized.toUnfinalized] using this
  have fxi : a.xi.val Vs = redFq (u.xi.val Vg) := by
    have := e (x := .b128 sp.deferredValues.xi.val) (by simp [UnfinalizedProof.packed]) c16
    simpa [PackedScalar.cell, hxi, AllocUnfinalized.toUnfinalized] using this
  have fd : a.spongeDigest.val Vs = redFq (u.spongeDigest.val Vg) := by
    have := e (x := .full sp.spongeDigestBeforeEvaluations) (by simp [UnfinalizedProof.packed]) c11
    simpa [PackedScalar.cell, hdig, AllocUnfinalized.toUnfinalized] using this
  -- a split claim joins its lifted half and parity
  have join : ∀ (w : Type2 (FVar Fq)) (s : Type2 (SplitField (FVar Fq) (BoolVar Fq)))
      (x : Type2 (SplitField (FVar Fp) (BoolVar Fp))), SplitReads Vs w s →
      (PackedScalar.full s.val.sDiv2).cell.val Vs = redFq (x.val.sDiv2.val Vg) →
      (PackedScalar.bit s.val.sOdd).cell.val Vs = redFq ((↑x.val.sOdd : CVar Fp).val Vg) →
      w.val.val Vs = 2 * redFq (x.val.sDiv2.val Vg) + redFq ((↑x.val.sOdd : CVar Fp).val Vg) := by
    intro w s x ⟨bb, hbb, hw⟩ hh ho
    simp only [PackedScalar.cell] at hh ho
    rw [hw, hh, ← hbb, ho]
  have pm := fun (x : PackedScalar Fq) (h : x ∈ UnfinalizedProof.packed sp) => h
  have fcip := join _ _ u.cip hscip (e (by simp [UnfinalizedProof.packed]) c1)
    (e (by simp [UnfinalizedProof.packed]) c2)
  have fbb := join _ _ u.b hsb (e (by simp [UnfinalizedProof.packed]) c3)
    (e (by simp [UnfinalizedProof.packed]) c4)
  have fzm := join _ _ u.zetaToSrsLength hszm (e (by simp [UnfinalizedProof.packed]) c5)
    (e (by simp [UnfinalizedProof.packed]) c6)
  have fzn := join _ _ u.zetaToDomainSize hszn (e (by simp [UnfinalizedProof.packed]) c7)
    (e (by simp [UnfinalizedProof.packed]) c8)
  have fperm := join _ _ u.perm hsperm (e (by simp [UnfinalizedProof.packed]) c9)
    (e (by simp [UnfinalizedProof.packed]) c10)
  -- the round challenges, entrywise
  have fbp : a.bulletproofChallenges.toList.map (·.val Vs)
      = u.bulletproofChallenges.toList.map fun c => redFq (c.val Vg) := by
    have hs : ∀ c ∈ sp.deferredValues.bulletproofChallenges.toList,
        c.val.val Vs = redFq (PackedScalar.reduced IpaVesta.curve Vs (.b128 c.val)) :=
      fun c hc => hB (.b128 c.val) (by
        simp only [UnfinalizedProof.packed, List.mem_append, List.mem_cons, List.mem_map,
          PackedScalar.b128.injEq]
        exact Or.inl (Or.inr ⟨c, hc, rfl⟩))
    have hbp' : u.bulletproofChallenges.toList.map (·.val Vg)
        = sp.deferredValues.bulletproofChallenges.toList.map fun c =>
            PackedScalar.reduced IpaVesta.curve Vs (.b128 c.val) := by
      simpa [List.map_map, Function.comp_def] using hbp
    have hsp : sp.deferredValues.bulletproofChallenges.toList.map (·.val.val Vs)
        = (u.bulletproofChallenges.toList.map (·.val Vg)).map redFq := by
      rw [hbp', List.map_map]
      exact List.map_congr_left hs
    rw [hbps] at hsp
    simpa [AllocUnfinalized.toUnfinalized, Vector.toList_map, List.map_map,
      Function.comp_def] using hsp
  -- the finalize flag: a bit on the wrap side, so the same bit on the step side
  have fsf : ∃ bb : Bool, CircuitType.Reads Vg u.shouldFinalize bb ∧
      CircuitType.Reads Vs a.shouldFinalize bb := by
    obtain ⟨bb, hbb⟩ := hbnd (.bit sp.shouldFinalize) (by simp [UnfinalizedProof.packed])
    refine ⟨bb, CircuitType.reads_boolVar.mpr ?_, CircuitType.reads_boolVar.mpr ?_⟩
    · rw [hsf]
      show ((ZMod.val ((↑sp.shouldFinalize : CVar Fq).val Vs) : ℕ) : Fp) = bit bb
      rw [hbb]
      cases bb <;> simp [bit, ZMod.val_one_eq_one_mod, PALLAS_SCALAR_CARD]
    · rw [← show sp.shouldFinalize = a.shouldFinalize from hsfe]
      exact hbb
  refine ⟨?_, fsf⟩
  simp only [SplitClaimsCast, AllocUnfinalized.toUnfinalized, List.map_cons, List.map_nil,
    List.cons.injEq, and_true] at fcip fbb fzm fzn fperm ⊢
  exact ⟨⟨fa, fb, fg, fz, fxi, fd⟩, ⟨fperm, fzm, fzn, fcip, fbb⟩, by
    simpa [Function.comp_def, Vector.toList_map, List.map_map] using fbp⟩

/-- A bit that reads as `true` on one side of a tie reads as `true` on the other. -/
private theorem reads_true_of_tie {Vg : Valuation Fp} {Vs : Valuation Fq} {a : BoolVar Fp}
    {a' : BoolVar Fq} (ht : ∃ bb : Bool, CircuitType.Reads Vg a bb ∧ CircuitType.Reads Vs a' bb)
    (hG : CircuitType.Reads Vg a true) : (↑a' : CVar Fq).val Vs = 1 := by
  obtain ⟨bb, hGb, hSb⟩ := ht
  rw [CircuitType.reads_boolVar] at hG hGb hSb
  have : bb = true := by
    cases bb
    · rw [hG] at hGb
      simp [bit] at hGb
    · rfl
  subst this
  simpa [bit] using hSb

/-- **Every must-verify slot's wrap proof verifies.** Let `Vg` satisfy the step circuit of any
rule and `Vs` the next wrap circuit, with its branch index reading as branch `b`. When the step
circuit's output reads as the wrap circuit's public input, every must-verify slot whose wrap
slot was compiled for the key's wrap domain has each wrap proof its cells read as accepted by
`kimchiVerify`, under the guards, the finalize ties and `SgOk`. -/
theorem stepWrap_kimchiVerify
    -- the rule's `n` slots; the tag's `w`, the accumulators each of its wrap proofs carries
    -- and the wrap circuit's slots; the step proofs the wrap proofs verified at `ncPrevStep`; the
    -- wrap circuit's `branches`, the step proof it verifies at `ncStep` chunks and `ks` rounds
    {n w ncPrevStep branches ncStep ks : ℕ} [NeZero branches]
    -- the rule's input, as a value and as cells
    {inVal inVar : Type}
    [CircuitType Fp inVal inVar]
    -- the environment of the wrap proofs the slots verify (key, SRS, domain)
    (E : Env IpaPallas.curve 1)
    -- the environment of the step proofs those wrap proofs carry
    (EsPrev : Env IpaVesta.curve ncPrevStep)
    -- the step domains the finalize inside the step circuit dispatches over
    (D : KnownDomains EsPrev)
    -- the rule verifies at most the tag's `w` slots
    (hn : n ≤ w)
    -- the tag verifies at most `MaxProofsVerified`
    (hw : w ≤ MaxProofsVerified)
    -- the `sg` padding the missing accumulators
    (dummySg : AffinePoint (FVar Fp))
    -- the unfinalized entry padding the step statement to the tag's `w` slots
    (dummyUnf : UnfVal E.σ.k)
    -- every slot statement packs into at most `2 ^ E.σ.k` cells, the SRS size
    (hsmall : ∀ (inp : VerifyOneInput EsPrev.σ.k E.σ.k 1 ncPrevStep w) msg,
      (inp.statement msg).packed.length ≤ 2 ^ E.σ.k)
    -- no relation the slot statements' public-input commitment names commits the SRS to the
    -- identity
    (havoid : ∀ (inp : VerifyOneInput EsPrev.σ.k E.σ.k 1 ncPrevStep w) msg,
      E.σ.Avoids (stepRelationsAt E (inp.statement msg)))
    -- the step circuit's valuation
    (Vg : Valuation Fp)
    [CheckedType Fp (Builder Vg (KimchiConstraint Fp)) inVal inVar]
    -- the application rule: from its input, each slot's statement and the public output
    (rule : inVar →
      CircuitM Fp (Builder Vg (KimchiConstraint Fp)) (Vector PrevStatement n × List (FVar Fp)))
    -- the step circuit's advice
    (adv : StepMainAdvice n w 1 ncPrevStep E.σ.k EsPrev.σ.k inVal)
    -- `Vg` satisfies every constraint of the compiled step circuit
    (hstep : ∀ con ∈ (compile (a := Unit) (b := Vector Fp (w * (E.σ.k + 17) + 1 + w))
        (stepMainCircuit (c := Builder Vg (KimchiConstraint Fp)) hw (verifyProofAt E)
          (FopParams.ofEnv EsPrev Linearization.fpTokens) D.list dummySg dummyUnf rule
          adv)).constraints, ConstraintHolds.Holds Vg con)
    -- the next wrap circuit's valuation
    (Vs : Valuation Fq)
    -- the generator of the wrap domain of each `log2`, a constant of the circuit
    (gen : ℕ → Fq)
    -- the tag's branches' slot counts, and their step circuits' environments over one SRS
    (widths : Vector (Fin (w + 1)) branches)
    (stepEnvs : Vector (Env IpaVesta.curve ncStep) branches) (σStep : SRS IpaVesta.curve.Point)
    -- each slot's compile-time wrap domain index per branch: the tag's `w` slots,
    -- front-padded
    (pins : Vector (Vector (Option ℕ) branches) w)
    -- the Lagrange bases at a step domain, the padding challenges and each slot's
    -- challenge-stack height: constants of the wrap circuit
    (lagrange : ℕ → List (Vector IpaVesta.curve.Point ncStep))
    (dummy : List Fq) (slotWidths : Vector ℕ w)
    -- the wrap circuit's advice
    (advW : WrapMainAdvice w ncStep E.σ.k ks slotWidths.toList.sum)
    -- fewer branches than the field's characteristic
    (hbr : branches ≤ PALLAS_SCALAR_CARD)
    -- `Vs` satisfies every constraint of the compiled wrap circuit, over the branches' keys and
    -- domains and the SRS's blinding base
    (hwrap : ∀ con ∈ (compile (a := StatementPacked ks (Type1 Fq) Fq) (b := Unit)
        (wrapMainCircuit (c := Builder Vs (KimchiConstraint Fq))
          (FopParams.ofEnv E Linearization.fqTokens) gen widths (stepDomainLog2s stepEnvs)
          (stepKeyCells stepEnvs) pins lagrange σStep.h
          dummy slotWidths advW)).constraints,
        ConstraintHolds.Holds Vs con)
    -- the active branch
    (b : Fin branches)
    -- the key's wrap domain, as an index into `wrapDomainLog2s`
    (j : ℕ)
    -- `j` is the key's domain
    (hdom : wrapDomainLog2s[j]? = some E.cvk.domainLog2)
    -- `gen` gives the key's generator at its domain
    (hgen : gen E.cvk.domainLog2 = E.cvk.omega) :
    let r := (build (stepMain (c := Builder Vg (KimchiConstraint Fp)) hw (verifyProofAt E)
      (FopParams.ofEnv EsPrev Linearization.fpTokens) D.list dummySg dummyUnf rule adv) 0).result
    -- the wrap circuit's cells over its statement
    let hd := (build (wrapMain (c := Builder Vs (KimchiConstraint Fq))
      (FopParams.ofEnv E Linearization.fqTokens) gen widths (stepDomainLog2s stepEnvs)
          (stepKeyCells stepEnvs) pins lagrange σStep.h dummy
      slotWidths advW (inputVar (F := Fq) (a := StatementPacked ks (Type1 Fq) Fq)))
      (bodyStart (F := Fq) (c := Builder Vs (KimchiConstraint Fq))
        (a := StatementPacked ks (Type1 Fq) Fq))).result
    -- the wrap circuit's branch index reads as `b`
    hd.1.whichBranch.val Vs = (b : Fq) →
    -- the step proof's public input: the step circuit's statement is the wrap circuit's packed
    -- step statement, each cell reduced into the step field (`wrapPublicInput_toList`)
    r.out.map (·.val Vg) = hd.2.statement.packed.map (PackedScalar.reduced IpaVesta.curve Vs) →
    -- slot `i` must verify
    ∀ i : Fin n, CircuitType.Reads Vg r.prevs[i].mustVerify true →
      let inp := slotInput hw dummySg r.prevs[i] r.slots[i] r.unfs[i] r.msgs[i]
      let sl := hd.1.slots[Fin.cast (Nat.sub_add_cancel hn) (Fin.natAdd (w - n) i)]
      -- the active branch compiled its wrap slot for the key's domain
      sl.pins[b] = some j →
      ∀ (cp : KimchiProof IpaPallas.curve 1 E.σ.k)
        (ms : List Bool),
        -- the slot's public input: its statement, carrying the step-message digest
        let pub := inp.publicInputAt E Vg ms
        -- its cells hold `cp`, with masks `ms`
        inp.WireReads E Vg r.vk.points cp ms →
        -- of `cp` itself: the guards, the finalize ties and the deferred `sg` equation
        Guards IpaPallas.curve E.cvk cp pub →
        FopTies E cp pub (ScalarHalf.wrap Vs sl.unfinalized sl.evals sl.prevChallenges) →
        SgOk E.σ E.cvk cp pub →
        kimchiVerify IpaPallas.curve E.σ E.cvk cp pub = true := by
  intro r hd hb htie i hmv inp sl hpin cp ms pub hwire hguard hf hsg
  -- the step side: `shouldFinalize` set, and the group half accepts `cp`
  obtain ⟨hsfG, hslot, -⟩ := (builder_spec_iff _ _).mp
    (stepMain_reads E EsPrev D (hn.trans hw) hw dummySg dummyUnf rule adv hsmall havoid) 0
      (fun con hc => hstep con (mem_compile_stepMainCircuit hw _ _ _ _ _ _ _ hc)) i hmv
  obtain ⟨v, hv, hv1⟩ := hslot cp ms hwire
  -- the wrap side: the body's constraints hold, so its finalize read does
  have hbody : ∀ con ∈ (build (wrapMain (c := Builder Vs (KimchiConstraint Fq))
      (FopParams.ofEnv E Linearization.fqTokens) gen widths (stepDomainLog2s stepEnvs)
          (stepKeyCells stepEnvs) pins lagrange σStep.h dummy
      slotWidths advW (inputVar (F := Fq) (a := StatementPacked ks (Type1 Fq) Fq)))
      (bodyStart (F := Fq) (c := Builder Vs (KimchiConstraint Fq))
        (a := StatementPacked ks (Type1 Fq) Fq))
      ).constraints, ConstraintHolds.Holds Vs con := fun con hc =>
    hwrap con (mem_compile_of_mem_body (by
      simp only [wrapMainCircuit, build_bind]
      exact List.mem_append_left _ hc))
  obtain ⟨b', hb', hwb, -, -, -, hfin⟩ := (builder_spec_iff _ _).mp
    (wrapMain_reads E Vs gen widths (stepDomainLog2s stepEnvs)
          (stepKeyCells stepEnvs) pins lagrange σStep.h dummy slotWidths advW
      (inputVar (F := Fq) (a := StatementPacked ks (Type1 Fq) Fq)) hw hbr) _ hbody
  -- the tie, slot by slot: the wrap claims hold the step claims lifted (`slot_cast`)
  have hnc : 0 < ncStep := (stepEnvs[0]'(Nat.pos_of_neZero branches)).nc_pos
  obtain ⟨hsplitsEq, hsr, hbnd, hslots⟩ := (builder_spec_iff _ _).mp
    (wrapMain_statement (FopParams.ofEnv E Linearization.fqTokens) Vs gen widths
      (stepDomainLog2s stepEnvs) (stepKeyCells stepEnvs) pins lagrange σStep.h dummy slotWidths
      advW (inputVar (F := Fq) (a := StatementPacked ks (Type1 Fq) Fq)) hnc) _ hbody
  obtain ⟨tail, hout⟩ := (builder_spec_iff _ _).mp
    (stepMain_out hw (verifyProofAt E) (FopParams.ofEnv EsPrev Linearization.fpTokens) D.list
      dummySg dummyUnf rule adv) 0
    (fun con hc => hstep con (mem_compile_stepMainCircuit hw _ _ _ _ _ _ _ hc))
  have hlenU : ∀ u : UnfVar E.σ.k,
      (CircuitType.varToFields (F := Fp) (val := UnfVal E.σ.k) u).toList.length = E.σ.k + 17 := by
    intro u
    rw [AllocUnfinalized.varToFields_toList]
    simp
  have hlenP : ∀ sp : UnfinalizedProof E.σ.k (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq))),
      (sp.packed.map (PackedScalar.reduced IpaVesta.curve Vs)).length = E.σ.k + 17 := by
    intro sp
    simp [UnfinalizedProof.packed]
  have htie' := htie
  rw [hout, StepStatement.packed, hsplitsEq, List.append_assoc] at htie'
  rw [List.map_append (f := PackedScalar.reduced IpaVesta.curve Vs), List.map_flatMap] at htie'
  -- slot `i` is the `(w − n) + i`-th block on both sides
  set jf : Fin w := Fin.cast (Nat.sub_add_cancel hn) (Fin.natAdd (w - n) i)
  have hjv : jf.val = w - n + i := rfl
  have hblk := map_flatMap_block _
    (fun sp => sp.packed.map (PackedScalar.reduced IpaVesta.curve Vs)) (fun x : FVar Fp => x.val Vg)
    (E.σ.k + 17) hlenU hlenP (List.replicate (w - n)
      (CircuitType.constVar (F := Fp) (var := UnfVar E.σ.k) dummyUnf) ++ r.unfs.toList)
    hd.2.splits.toList tail _ (by simp; omega) htie' (w - n + i)
    (by simp) (by simp; omega)
  have hl : (List.replicate (w - n)
      (CircuitType.constVar (F := Fp) (var := UnfVar E.σ.k) dummyUnf) ++ r.unfs.toList)[w - n + i]'
        (by simp) = r.unfs[i] := by
    rw [List.getElem_append_right (by simp)]
    simp
  have hr : hd.2.splits.toList[w - n + i]'(by simp; omega) = hd.2.splits[jf] := by
    simp [hjv]
  rw [hl, hr] at hblk
  have hbj : ∀ x ∈ hd.2.splits[jf].packed, x.Bound Vs := fun x hx => hbnd x (by
    rw [StepStatement.packed, hsplitsEq]
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨_, Vector.mem_toList_iff.mpr (Vector.getElem_mem _), hx⟩)))
  obtain ⟨hc, hsf⟩ := slot_cast r.unfs[i] hd.2.splits[jf] hd.1.proofState.1[jf] hblk hbj (hsr jf)
  rw [← hslots jf] at hc hsf
  -- the circuit's branch is `b`: both are below the field's characteristic
  have hbb : b' = b.val := CharP.natCast_injOn_Iio Fq PALLAS_SCALAR_CARD
    (Set.mem_Iio.2 (by omega)) (Set.mem_Iio.2 (by omega)) (hwb.symm.trans hb)
  subst hbb
  exact hfin j hdom hgen _ hpin (reads_true_of_tie hsf hsfG) cp pub hguard Vg inp.unfinalized v hv
    hv1 hc hf hsg

end Pickles
