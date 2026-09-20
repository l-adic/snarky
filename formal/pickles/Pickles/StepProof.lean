import Pickles.StepScalarHalf
import Pickles.WrapVerify
import Snarky.Compile

/-!
# A step proof is verified by its two circuits

The top-level statement for a step proof (Vesta commitments): a valuation satisfying the wrap
circuit's verify block, a valuation satisfying the next step circuit's scalar half with its
`finalized` bit set, and the ties between them, make the deployed verifier accept.

`kimchiVerify` accepts exactly when its guards hold, the opening's Schnorr equation holds at
the run's own scalars, and `sg` is the challenge polynomial's commitment
(`kimchiVerify_reflects`, `verifyWith`). The group circuit proves the equation at the claimed
scalars; the scalar circuit proves the claimed scalars are the run's; the ties say the two
circuits speak of one set of claims and of this proof. The guards are the environment's, and
the `sg` equation is the one check no circuit performs — pickles defers it to the next
proof's accumulator (`SgOk`, `sgOk_iff_accOk`).

The two halves run in different circuits over different fields, so neither is a triple's
program here: each appears as its built constraint system, satisfied by its own valuation —
what a triple unfolds to (`builder_spec_iff`). The step circuit is compiled
(`Snarky.compile`) with the slot's branch data as its input, so the input's check is among
its rows and the mask's booleanity is a consequence of satisfaction, as it is in `Step.Main`,
which checks the branch data where it allocates it.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

/-- **A step proof's two circuits, satisfied and tied, make `kimchiVerify` accept.** -/
theorem stepProof_kimchiVerify_vesta {ks n : ℕ}
    (E : Env IpaVesta.curve)
    (cp : KimchiProof IpaVesta.curve 1 E.σ.k)
    -- the wrap circuit's verify block
    (Vg : Valuation Fq)
    (statement : StepStatement ks n (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq))))
    (claimsG : UnfinalizedProof E.σ.k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (cells : IvpInput E.σ.k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (spongeAfterIndex : SpongeVar Fq)
    (msgSponge : SpongeVar Fq)
    (newBpChallenges : List (List (FVar Fq)))
    (claimedMsgDigest : FVar Fq)
    (ng : ℕ)
    (hsatG : ∀ con ∈ (build (wrapVerifyAt (c := Builder Vg (KimchiConstraint Fq)) E statement
        spongeAfterIndex msgSponge newBpChallenges claimedMsgDigest claimsG cells)
        ng).constraints, ConstraintHolds.Holds Vg con)
    -- the step circuit's scalar half, compiled: its input is the slot's branch data, checked
    -- as `Step.Main` checks it on allocation, and its body asserts `finalized`
    (Vs : Valuation Fp)
    (domains : KnownDomains E)
    (claimsS : UnfinalizedProof E.σ.k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (evals : AllEvals (FVar Fp))
    (prevChallenges : Vector (Vector (FVar Fp) E.σ.k) MaxProofsVerified)
    (hsatS : ∀ con ∈ (compile (a := BranchData Fp Bool) (b := Unit)
        (stepScalarCircuit (c := Builder Vs (KimchiConstraint Fp)) E domains claimsS evals
          prevChallenges)).constraints, ConstraintHolds.Holds Vs con)
    -- the wrap circuit's inputs are the proof's and the key's
    (hivp : ∃ oldsW, IvpHyps (wrapSide Vg) E.σ E.cvk cp (wrapPublicInput E Vg statement) true
      spongeAfterIndex (cells.withClaims claimsG) oldsW)
    -- the step circuit's `domain_log2` input holds the key's
    (hdom : (inputVar (F := Fp) (a := BranchData Fp Bool)).domainLog2.val Vs
      = (domains.keyLog2 : Fp))
    -- the statement's full scalars avoid the ladder's sixteen-value band
    (hoff : ∀ leaf ∈ wrapLeavesAt E statement, Leaf.offBand IpaVesta.curve.scalar Vg leaf)
    -- the glue between the two circuits, and the step circuit's inputs being the proof's
    (ht : HalvesTies E cp (wrapPublicInput E Vg statement) (GroupHalf.wrap Vg claimsG)
      (ScalarHalf.step Vs claimsS evals
        (inputVar (F := Fp) (a := BranchData Fp Bool)).proofsVerifiedMask prevChallenges))
    -- the verifier's guards, and the deferred accumulator check
    (hguard : Guards IpaVesta.curve E.cvk cp (wrapPublicInput E Vg statement))
    (hsg : SgOk E cp (wrapPublicInput E Vg statement)) :
    kimchiVerify IpaVesta.curve E.σ E.cvk cp (wrapPublicInput E Vg statement) = true := by
  obtain ⟨v, hv, hv1⟩ := (builder_spec_iff _ _).mp
    (wrapVerifyAt_reads (V := Vg) E cp statement spongeAfterIndex msgSponge newBpChallenges
      claimedMsgDigest claimsG cells hoff hivp) ng hsatG
  -- the input check's rows are among the compiled ones, so the mask is boolean
  have hmask := BranchData.mask_boolean (V := Vs) _
    (CheckedType.check_sound Vs (inputVar (F := Fp) (a := BranchData Fp Bool)) _
      fun con hc => hsatS con (mem_compile_of_mem_check hc))
  -- and so are the body's
  exact (builder_spec_iff _ _).mp
    (stepScalarCircuit_reads E cp _ hguard Vs domains claimsS evals prevChallenges _ hmask hdom
      Vg claimsG v hv hv1 ht hsg) _ fun con hc => hsatS con (mem_compile_of_mem_body hc)

end Pickles
