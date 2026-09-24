import Pickles.StepMain
import Pickles.WrapFinalize

set_option mvcgen.warning false

/-!
# Every must-verify slot's wrap proof verifies

A step circuit verifies up to `MaxProofsVerified` previous wrap proofs, each across two circuits:
the step circuit checks its group half, and the next wrap circuit's finalize block checks its
scalar half. This module joins the two reads. For any rule, under a valuation satisfying the step
circuit's constraints and one satisfying the finalize block's, every wrap proof that a slot the
rule marks must-verify reads as is accepted by `kimchiVerify`.

## Main results

* `stepWrap_kimchiVerify`: the two circuits' runs, each satisfied under its own valuation, with
  the ties between each slot's two halves, the pins at the key's wrap domain and the readings,
  make `kimchiVerify` accept every must-verify slot's wrap proof.

## Implementation notes

The finalize block has one slot per proof the tag verifies, `w`, front-padded: step slot `i`
is finalize slot `i + (w − n)`. The step circuit sets `shouldFinalize` on every
must-verify slot, and the tie carries that bit to the finalize block, where it forces the slot
to finalize.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta
open scoped Kimchi

/-- A bit that reads as `true` on one side of a tie reads as `true` on the other. -/
private theorem reads_true_of_tie {C : KimchiCurve} {sf sf' : Type} {k nc : ℕ}
    {G : GroupHalf C sf k} {Sc : ScalarHalf C sf' k nc} (ht : HalvesTies G Sc)
    (hG : CircuitType.Reads G.V G.claims.shouldFinalize true) :
    (↑Sc.claims.shouldFinalize : CVar C.ScalarField).val Sc.V = 1 := by
  obtain ⟨-, -, bb, hGb, hSb⟩ := ht
  rw [CircuitType.reads_boolVar] at hG hGb hSb
  have : bb = true := by
    cases bb
    · rw [hG] at hGb
      simp [bit] at hGb
    · rfl
  subst this
  simpa [bit] using hSb

/-- **Every must-verify slot's wrap proof verifies.** For any rule, take a satisfying run of
the step circuit under `Vg` and one of the next wrap circuit's finalize block under `Vs`, with
the branch bits reading as branch `b`. Suppose slot `i` is must-verify, its finalize slot was
compiled for the key's wrap domain, and its two halves are tied. Then any wrap proof its cells
read as, under the guards, the finalize ties and `SgOk`, is accepted by `kimchiVerify`. -/
theorem stepWrap_kimchiVerify
    -- the rule's `n` slots; the tag's `w`, the accumulators each of its wrap proofs carries
    -- and the finalize block's slots; keys of `nc` chunks; the wrap circuit's `branches`
    {n w nc branches : ℕ}
    -- the rule's input, as a value and as cells
    {inVal inVar : Type}
    [CircuitType Fp inVal inVar]
    -- the environment of the wrap proofs the slots verify (key, SRS, domain)
    (E : Env IpaPallas.curve nc)
    -- the environment of the step proofs those wrap proofs carry
    (Es : Env IpaVesta.curve nc)
    -- the step domains the finalize inside the step circuit dispatches over
    (D : KnownDomains Es)
    -- the rule verifies at most the tag's `w` slots
    (hn : n ≤ w)
    -- the tag verifies at most `MaxProofsVerified`
    (hw : w ≤ MaxProofsVerified)
    -- the `sg` padding the missing accumulators
    (dummySg : AffinePoint (FVar Fp))
    -- the unfinalized entry padding the step statement to the tag's `w` slots
    (dummyUnf : UnfVal E.σ.k)
    -- every slot statement packs into at most `2 ^ E.σ.k` cells, the SRS size
    (hsmall : ∀ (inp : VerifyOneInput Es.σ.k E.σ.k nc w) msg,
      (inp.statement msg).packed.length ≤ 2 ^ E.σ.k)
    -- no relation the slot statements' public-input commitment names commits the SRS to the
    -- identity
    (havoid : ∀ (inp : VerifyOneInput Es.σ.k E.σ.k nc w) msg,
      E.σ.Avoids (stepRelationsAt E (inp.statement msg)))
    -- the step circuit's valuation
    (Vg : Valuation Fp)
    [CheckedType Fp (Builder Vg (KimchiConstraint Fp)) inVal inVar]
    -- the application rule: from its input, each slot's statement and the public output
    (rule : inVar →
      CircuitM Fp (Builder Vg (KimchiConstraint Fp)) (Vector PrevStatement n × List (FVar Fp)))
    -- the step circuit's advice
    (adv : StepMainAdvice n w nc E.σ.k Es.σ.k inVal)
    -- `Vg` satisfies every constraint of the step circuit, which allocates all its cells
    (hstep : ∀ con ∈ (build (stepMain (c := Builder Vg (KimchiConstraint Fp)) hw
        (verifyProofAt E) (FopParams.ofEnv Es Linearization.fpTokens) D.list dummySg dummyUnf rule
        adv) 0).constraints, ConstraintHolds.Holds Vg con)
    -- the next wrap circuit's valuation
    (Vs : Valuation Fq)
    -- the generator of the wrap domain of each `log2`, a constant of the circuit
    (gen : ℕ → Fq)
    -- each finalize slot's compile-time domain index per branch: the tag's `w` slots,
    -- front-padded
    (pins : Vector (Vector (Option ℕ) branches) w)
    -- `Vs` satisfies every constraint of the compiled finalize block
    (hwrap : ∀ con ∈ (compile (a := WrapFinalizeIn branches w E.σ.k nc) (b := Unit)
        (wrapFinalizeCircuit (c := Builder Vs (KimchiConstraint Fq))
          (FopParams.ofEnv E Linearization.fqTokens) gen pins)).constraints,
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
      (FopParams.ofEnv Es Linearization.fpTokens) D.list dummySg dummyUnf rule adv) 0).result
    -- the finalize block's input cells: the branch bits and the slots, with their pins
    let x := inputVar (F := Fq) (a := WrapFinalizeIn branches w E.σ.k nc)
    let slots := WrapFinalizeInVar.slots x pins
    -- the branch bits read as `b`'s one-hot vector
    CircuitType.Reads Vs x.val.1 (Vector.ofFn fun l => decide (l = b)) →
    -- slot `i` must verify
    ∀ i : Fin n, CircuitType.Reads Vg r.prevs[i].mustVerify true →
      let inp := slotInput hw dummySg r.prevs[i] r.slots[i] r.unfs[i] r.msgs[i]
      let sl := slots[Fin.cast (Nat.sub_add_cancel hn) (Fin.natAdd (w - n) i)]
      -- the active branch compiled its finalize slot for the key's domain
      sl.pins[b] = some j →
      -- its two halves hold one set of claims
      HalvesTies (GroupHalf.step Vg inp.unfinalized)
        (ScalarHalf.wrap Vs sl.unfinalized sl.evals sl.prevChallenges) →
      ∀ (cp : KimchiProof IpaPallas.curve nc E.σ.k)
        (ms : List Bool)
        (cvs : List (List Fp)),
        -- the slot's public input: its statement, carrying the step-message digest
        let pub := inp.publicInputAt E Vg ms
        -- its cells hold `cp`, with masks `ms` and previous challenges `cvs`
        inp.WireReads E Vg r.vk.points cp ms cvs →
        -- of `cp` itself: the guards, the finalize ties and the deferred `sg` equation
        Guards IpaPallas.curve E.cvk cp pub →
        FopTies E cp pub (ScalarHalf.wrap Vs sl.unfinalized sl.evals sl.prevChallenges) →
        SgOk E.σ E.cvk cp pub →
        kimchiVerify IpaPallas.curve E.σ E.cvk cp pub = true := by
  intro r x slots hbits i hmv inp sl hpin ht cp ms cvs pub hwire hguard hf hsg
  -- the step side: `shouldFinalize` set, and the group half accepts `cp`
  obtain ⟨hsfG, hslot⟩ := (builder_spec_iff _ _).mp
    (stepMain_reads E Es D (hn.trans hw) hw dummySg dummyUnf rule adv hsmall havoid) 0 hstep i
      hmv
  obtain ⟨v, hv, hv1⟩ := hslot cp ms cvs hwire
  -- the finalize side: the slot reads as its scalar half
  have hfin := wrapFinalizePrevProofs_reads E Vs gen x.val.1 (WrapFinalizeInVar.slots x pins) b j
    hbits hdom hgen
  have hcirc : ⦃⌜True⌝⦄ wrapFinalizeCircuit (c := Builder Vs (KimchiConstraint Fq))
      (FopParams.ofEnv E Linearization.fqTokens) gen pins x
      ⦃⇓ _ _ => ⌜∀ i : Fin w, (WrapFinalizeInVar.slots x pins)[i].pins[b] = some j →
        (↑(WrapFinalizeInVar.slots x pins)[i].unfinalized.shouldFinalize : CVar Fq).val Vs = 1 →
        (WrapFinalizeInVar.slots x pins)[i].ScalarReads E Vs⌝⦄ := by
    simp only [wrapFinalizeCircuit]
    mvcgen [hfin]
  exact (builder_spec_iff _ _).mp hcirc _ (fun con hc => hwrap con (mem_compile_of_mem_body hc))
    _ hpin (reads_true_of_tie ht hsfG) cp pub hguard Vg inp.unfinalized v hv hv1 ht hf hsg

end Pickles
