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
  the ties between each slot's two halves, the pins at the key's wrap domain and the readings,
  make `kimchiVerify` accept every must-verify slot's wrap proof.

## Implementation notes

The wrap circuit has one slot per proof the tag verifies, `w`, front-padded: step slot `i` is
wrap slot `i + (w − n)`. The wrap proofs are at one chunk, the chunk count the wrap circuit
allocates their evaluations at. The step circuit sets `shouldFinalize` on every
must-verify slot, and the tie carries that bit to the finalize block, where it forces the slot
to finalize.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta
open scoped Kimchi

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
rule and `Vs` the next wrap circuit, with its branch index reading as branch `b`. Every
must-verify slot whose wrap slot was compiled for the key's wrap domain, and
whose two halves are tied and read one `shouldFinalize` bit, has each wrap proof its cells read
as accepted by `kimchiVerify`, under the guards, the finalize ties and `SgOk`. -/
theorem stepWrap_kimchiVerify
    -- the rule's `n` slots; the tag's `w`, the accumulators each of its wrap proofs carries
    -- and the wrap circuit's slots; the step proofs the wrap proofs verified at `ncPrevStep`; the
    -- wrap circuit's `branches`, the step proof it verifies at `ncStep` chunks
    {n w ncPrevStep branches ncStep : ℕ} [NeZero branches]
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
    -- `Vg` satisfies every constraint of the step circuit, which allocates all its cells
    (hstep : ∀ con ∈ (build (stepMain (c := Builder Vg (KimchiConstraint Fp)) hw
        (verifyProofAt E) (FopParams.ofEnv EsPrev Linearization.fpTokens) D.list dummySg dummyUnf
        rule adv) 0).constraints, ConstraintHolds.Holds Vg con)
    -- the next wrap circuit's valuation
    (Vs : Valuation Fq)
    -- the generator of the wrap domain of each `log2`, a constant of the circuit
    (gen : ℕ → Fq)
    -- the tag's branches: their slot counts, step domains and step keys
    (widths log2s : List ℕ)
    (stepKeys : Vector (VkComms ncStep (AffinePoint (FVar Fq))) branches)
    -- each slot's compile-time wrap domain index per branch: the tag's `w` slots,
    -- front-padded
    (pins : Vector (Vector (Option ℕ) branches) w)
    -- the Lagrange bases at a step domain, the blinding base, the padding challenges and each
    -- slot's challenge-stack height: constants of the wrap circuit
    (lagrange : ℕ → List (Vector IpaVesta.curve.Point ncStep)) (h : IpaVesta.curve.Point)
    (dummy : List Fq) (slotWidths : Vector ℕ w)
    -- the wrap circuit's advice
    (advW : WrapMainAdvice w ncStep E.σ.k slotWidths.toList.sum)
    -- one slot count and one step domain per branch, each slot count at most `w`, and fewer
    -- branches than the field's characteristic
    (hwl : widths.length = branches)
    (hll : log2s.length = branches)
    (hwidths : ∀ x ∈ widths, x ≤ w)
    (hbr : branches ≤ PALLAS_SCALAR_CARD)
    -- `Vs` satisfies every constraint of the compiled wrap circuit
    (hwrap : ∀ con ∈ (compile (a := Vector Fq 40) (b := Unit)
        (wrapMainCircuit (c := Builder Vs (KimchiConstraint Fq))
          (FopParams.ofEnv E Linearization.fqTokens) gen widths log2s stepKeys pins lagrange h
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
      (FopParams.ofEnv E Linearization.fqTokens) gen widths log2s stepKeys pins lagrange h dummy
      slotWidths advW (inputVar (F := Fq) (a := Vector Fq 40)))
      (bodyStart (F := Fq) (c := Builder Vs (KimchiConstraint Fq)) (a := Vector Fq 40))).result
    -- the wrap circuit's branch index reads as `b`
    hd.whichBranch.val Vs = (b : Fq) →
    -- slot `i` must verify
    ∀ i : Fin n, CircuitType.Reads Vg r.prevs[i].mustVerify true →
      let inp := slotInput hw dummySg r.prevs[i] r.slots[i] r.unfs[i] r.msgs[i]
      let sl := hd.slots[Fin.cast (Nat.sub_add_cancel hn) (Fin.natAdd (w - n) i)]
      -- the active branch compiled its wrap slot for the key's domain
      sl.pins[b] = some j →
      -- its two halves hold one set of claims
      HalvesTies (GroupHalf.step Vg inp.unfinalized)
        (ScalarHalf.wrap Vs sl.unfinalized sl.evals sl.prevChallenges) →
      -- and read one `shouldFinalize` bit
      (∃ bb : Bool, CircuitType.Reads Vg inp.unfinalized.shouldFinalize bb ∧
        CircuitType.Reads Vs sl.unfinalized.shouldFinalize bb) →
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
  intro r hd hb i hmv inp sl hpin ht hsf cp ms pub hwire hguard hf hsg
  -- the step side: `shouldFinalize` set, and the group half accepts `cp`
  obtain ⟨hsfG, hslot⟩ := (builder_spec_iff _ _).mp
    (stepMain_reads E EsPrev D (hn.trans hw) hw dummySg dummyUnf rule adv hsmall havoid) 0 hstep i
      hmv
  obtain ⟨v, hv, hv1⟩ := hslot cp ms hwire
  -- the wrap side: the body's constraints hold, so its finalize read does
  have hbody : ∀ con ∈ (build (wrapMain (c := Builder Vs (KimchiConstraint Fq))
      (FopParams.ofEnv E Linearization.fqTokens) gen widths log2s stepKeys pins lagrange h dummy
      slotWidths advW (inputVar (F := Fq) (a := Vector Fq 40)))
      (bodyStart (F := Fq) (c := Builder Vs (KimchiConstraint Fq)) (a := Vector Fq 40))
      ).constraints, ConstraintHolds.Holds Vs con := fun con hc =>
    hwrap con (mem_compile_of_mem_body (by
      simp only [wrapMainCircuit, build_bind]
      exact List.mem_append_left _ hc))
  obtain ⟨b', hb', hwb, -, hfin⟩ := (builder_spec_iff _ _).mp
    (wrapMain_reads E Vs gen widths log2s stepKeys pins lagrange h dummy slotWidths advW
      (inputVar (F := Fq) (a := Vector Fq 40)) hwl hll hwidths hw hbr j hdom hgen) _ hbody
  -- the circuit's branch is `b`: both are below the field's characteristic
  have hbb : b' = b.val := CharP.natCast_injOn_Iio Fq PALLAS_SCALAR_CARD
    (Set.mem_Iio.2 (by omega)) (Set.mem_Iio.2 (by omega)) (hwb.symm.trans hb)
  subst hbb
  exact hfin _ hpin (reads_true_of_tie hsf hsfG) cp pub hguard Vg inp.unfinalized v hv hv1 ht hf
    hsg

end Pickles
