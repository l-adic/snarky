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

The finalize block's slots are front-padded to `MaxProofsVerified`: step slot `i` is finalize
slot `i + (MaxProofsVerified − n)`. The step circuit sets `shouldFinalize` on every
must-verify slot, and the tie carries that bit to the finalize block, where it forces the slot
to finalize.
-/

namespace Pickles

open Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
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
theorem stepWrap_kimchiVerify {n w nc : ℕ} {inVal inVar : Type} [CircuitType Fp inVal inVar]
    (E : Env IpaPallas.curve nc) (Es : Env IpaVesta.curve nc) (D : KnownDomains Es)
    (hn : n ≤ MaxProofsVerified) (hw : w ≤ MaxProofsVerified) (dummySg : AffinePoint (FVar Fp))
    (hsmall : ∀ (inp : VerifyOneInput Es.σ.k E.σ.k nc w) msg,
      (inp.statement msg).packed.length ≤ 2 ^ E.σ.k)
    (havoid : ∀ (inp : VerifyOneInput Es.σ.k E.σ.k nc w) msg,
      E.σ.Avoids (stepRelationsAt E (inp.statement msg)))
    -- the step circuit's run, satisfied under `Vg`
    (Vg : Valuation Fp) [CheckedType Fp (Builder Vg (KimchiConstraint Fp)) inVal inVar]
    (rule : inVar →
      CircuitM Fp (Builder Vg (KimchiConstraint Fp)) (Vector PrevStatement n × List (FVar Fp)))
    (adv : StepMainAdvice n w nc E.σ.k Es.σ.k inVal) (nvg : ℕ)
    (hstep : ∀ con ∈ (build (stepMain (c := Builder Vg (KimchiConstraint Fp)) hw
        (verifyProofAt E) (FopParams.ofEnv Es Linearization.fpTokens) D.list dummySg rule adv)
        nvg).constraints, ConstraintHolds.Holds Vg con)
    -- the finalize block's run, satisfied under `Vs`, the branch bits reading as branch `b`
    (Vs : Valuation Fq) (gen : ℕ → Fq) (log2s : List ℕ) (whichBranch : List (BoolVar Fq))
    (slots : List (WrapFinalizeSlot E.σ.k nc Fq)) (nvs : ℕ)
    (hwrap : ∀ con ∈ (build (wrapFinalizePrevProofs (c := Builder Vs (KimchiConstraint Fq))
        (FopParams.ofEnv E Linearization.fqTokens) gen log2s whichBranch slots) nvs).constraints,
        ConstraintHolds.Holds Vs con)
    (hslots : slots.length = MaxProofsVerified) (b j : ℕ)
    (hbits : whichBranch.map (fun x : BoolVar Fq => (↑x : CVar Fq).val Vs)
      = (List.range whichBranch.length).map fun l => if l = b then (1 : Fq) else 0)
    (hpins : ∀ sl ∈ slots, sl.pins.length = whichBranch.length)
    -- the key's wrap domain is candidate `j`
    (hj : j < log2s.length) (hgen : gen log2s[j] = E.cvk.omega) (hlog : 2 ^ log2s[j] = E.cvk.n)
    (hinj : ∀ l < log2s.length, (j : Fq) = l → j = l) :
    let r := (build (stepMain (c := Builder Vg (KimchiConstraint Fp)) hw (verifyProofAt E)
      (FopParams.ofEnv Es Linearization.fpTokens) D.list dummySg rule adv) nvg).result
    ∀ i : Fin n, CircuitType.Reads Vg r.prevs[i].mustVerify true →
      let inp := slotInput hw dummySg r.prevs[i] r.slots[i] r.unfs[i] r.msgs[i]
      let sl := slots[i.val + (MaxProofsVerified - n)]'(by omega)
      sl.pins[b]? = some (some j) →
      HalvesTies (GroupHalf.step Vg inp.unfinalized)
        (ScalarHalf.wrap Vs sl.unfinalized sl.evals sl.prevChallenges) →
      ∀ (cp : KimchiProof IpaPallas.curve nc E.σ.k) (ms : List Bool) (cvs : List (List Fp)),
        List.Forall₂ (CircuitType.Reads Vg) inp.proofMask.toList ms →
        List.Forall₂ (List.Forall₂ (CircuitType.Reads Vg))
          (inp.prevChallenges.toList.map Vector.toList) cvs →
        KeyReads IpaPallas.curve Vg r.vk.points E.cvk →
        ProofReads (stepSide Vg) (inp.proof.wComm.toList.map (·.toList))
          inp.proof.zComm.toList inp.proof.tComm.toList inp.proof.opening cp →
        CommReads IpaPallas.curve Vg inp.sgOld.toList (cp.olds.map (·.sg)).toList →
        Guards IpaPallas.curve E.cvk cp (inp.publicInputAt E Vg ms) →
        FopTies E cp (inp.publicInputAt E Vg ms)
          (ScalarHalf.wrap Vs sl.unfinalized sl.evals sl.prevChallenges) →
        SgOk E.σ E.cvk cp (inp.publicInputAt E Vg ms) →
        kimchiVerify IpaPallas.curve E.σ E.cvk cp (inp.publicInputAt E Vg ms) = true := by
  intro r i hmv inp sl hpin ht cp ms cvs hmask hcvs hkey hproof hcomm hguard hf hsg
  -- the step side: `shouldFinalize` set, and the group half accepts `cp`
  obtain ⟨hsfG, hslot⟩ := (builder_spec_iff _ _).mp
    (stepMain_reads E Es D hn hw dummySg rule adv hsmall havoid) nvg hstep i hmv
  obtain ⟨v, hv, hv1⟩ := hslot cp ms cvs hmask hcvs hkey hproof hcomm
  -- the finalize side: the slot reads as its scalar half
  have hsl : sl ∈ slots := List.getElem_mem _
  have hsfS := reads_true_of_tie ht hsfG
  exact (builder_spec_iff _ _).mp
    (wrapFinalizePrevProofs_reads E Vs gen log2s whichBranch slots b j hbits hpins hj hgen hlog
      hinj) nvs hwrap sl hsl hpin hsfS cp (inp.publicInputAt E Vg ms) hguard Vg inp.unfinalized
    v hv hv1 ht hf hsg

end Pickles
