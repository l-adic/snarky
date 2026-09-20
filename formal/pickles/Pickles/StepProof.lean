import Pickles.StepScalarHalf
import Pickles.WrapVerify

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
what a triple unfolds to (`builder_spec_iff`).
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
    -- the step circuit's scalar half, its `finalized` bit set
    (Vs : Valuation Fp)
    (domains : KnownDomains E)
    (claimsS : UnfinalizedProof E.σ.k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (evals : AllEvals (FVar Fp))
    (mask : Vector (BoolVar Fp) MaxProofsVerified)
    (prevChallenges : Vector (Vector (FVar Fp) E.σ.k) MaxProofsVerified)
    (domainLog2Var : FVar Fp)
    (ns : ℕ)
    (hsatS : ∀ con ∈ (build (finalizeOtherProofStepAt (c := Builder Vs (KimchiConstraint Fp))
        E domains claimsS evals mask prevChallenges domainLog2Var) ns).constraints,
      ConstraintHolds.Holds Vs con)
    (hfin : (↑(build (finalizeOtherProofStepAt (c := Builder Vs (KimchiConstraint Fp))
        E domains claimsS evals mask prevChallenges domainLog2Var) ns).result.finalized
        : CVar Fp).val Vs = 1)
    -- the wrap circuit's inputs are the proof's and the key's
    (hivp : ∃ oldsW, IvpHyps (wrapSide Vg) E.σ E.cvk cp (wrapPublicInput E Vg statement) true
      spongeAfterIndex (cells.withClaims claimsG) oldsW)
    -- the step circuit's `domain_log2` cell holds the key's
    (hdom : domainLog2Var.val Vs = (domains.keyLog2 : Fp))
    -- the mask cells are boolean: `finalize_other_proof` does not constrain them, pickles
    -- does where it unpacks the branch data. (The statement's boolean cells need no such
    -- line: the wrap block's `x_hat` gadget constrains each one.)
    (hmask : ∀ b ∈ mask.toList, (↑b : CVar Fp).val Vs = 0 ∨ (↑b : CVar Fp).val Vs = 1)
    -- the statement's full scalars avoid the ladder's sixteen-value band
    (hoff : ∀ leaf ∈ wrapLeavesAt E statement, Leaf.offBand IpaVesta.curve.scalar Vg leaf)
    -- the glue between the two circuits, and the step circuit's inputs being the proof's
    (ht : HalvesTies E cp (wrapPublicInput E Vg statement) (GroupHalf.wrap Vg claimsG)
      (ScalarHalf.step Vs claimsS evals mask prevChallenges))
    -- the verifier's guards, and the deferred accumulator check
    (hguard : Guards IpaVesta.curve E.cvk cp (wrapPublicInput E Vg statement))
    (hsg : SgOk E cp (wrapPublicInput E Vg statement)) :
    kimchiVerify IpaVesta.curve E.σ E.cvk cp (wrapPublicInput E Vg statement) = true := by
  obtain ⟨v, hv, hv1⟩ := (builder_spec_iff _ _).mp
    (wrapVerifyAt_reads (V := Vg) E cp statement spongeAfterIndex msgSponge newBpChallenges
      claimedMsgDigest claimsG cells hoff hivp) ng hsatG
  have hS := (builder_spec_iff _ _).mp
    (finalizeOtherProofStepAt_kimchiVerify_vesta E cp _ hguard Vs domains claimsS evals mask
      prevChallenges domainLog2Var hmask hdom Vg claimsG v hv hv1 ht) ns hsatS
  exact (hS.mp ⟨hsg, hfin⟩).1

end Pickles
