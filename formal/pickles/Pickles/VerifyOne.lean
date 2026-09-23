import Pickles.MessageHash
import Pickles.StepGroupHalf

/-!
# One previous proof inside the step circuit

Transcribed from `Pickles/Step/VerifyOne.purs`. For one previous wrap proof the step circuit
finalizes the deferred values that proof carries (`finalizeOtherProofStep`), recomputes its
`messagesForNextStepProof` digest (`hashMessagesForNextStepProofOpt`), checks the wrap proof's
group half against the statement those rebuild (`verifyProofAt`, resumed from the digest's
sponge after the key), and combines the two verdicts under the slot's `mustVerify` bit.

## Main definitions

* `VerifyOneInput`: the cells `verifyOne` reads for one previous proof;
* `verifyOne`: the gadget, returning the finalized proof's round challenges and the verdict.
-/

namespace Pickles

open Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta

/-- The cells `verifyOne` reads for one previous wrap proof: that proof's own deferred values
and digest (the step proof it verified, finalized here), its application state, evaluations
and the accumulator advice it carries, the unfinalized proof the step circuit holds for it,
its proof cells, and the slot's bits. -/
structure VerifyOneInput (ks k nc : ℕ) where
  /-- The previous proof's statement, as field elements. -/
  appState : List (FVar Fp)
  /-- The deferred values the previous wrap proof carries. -/
  deferred : DeferredValues ks (FVar Fp) (Type1 (FVar Fp))
  /-- Their fq-sponge digest before evaluations. -/
  spongeDigest : FVar Fp
  /-- The branch data the previous wrap proof carries. -/
  branchData : BranchData (FVar Fp) (BoolVar Fp)
  /-- The previous wrap proof's `messagesForNextWrapProof` digest. -/
  messagesForNextWrapProof : FVar Fp
  /-- The evaluations the deferred values are finalized against. -/
  evals : ChunkedEvals nc (FVar Fp)
  /-- The proofs-verified mask, trimmed to the slot's width. -/
  proofMask : List (BoolVar Fp)
  /-- The round challenges carried from the proofs the previous proof verified. -/
  prevChallenges : List (List (FVar Fp))
  /-- Their `sg` points, unpadded. -/
  prevSgs : List (AffinePoint (FVar Fp))
  /-- The `sg` points widened to the padded length, dummies first. -/
  sgOld : List (AffinePoint (FVar Fp))
  /-- The unfinalized proof the step circuit carries for this slot. -/
  unfinalized :
    UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp)))
  /-- The wrap proof's commitments and opening. -/
  proof : IvpProof k nc (FVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp)))
  /-- Whether this slot must verify. -/
  mustVerify : BoolVar Fp

variable {c : Type} [BasicSystem Fp c] [KimchiSystem Fp c] {ks k nc : ℕ}

/-- One previous proof: assert the unfinalized proof's `shouldFinalize` is `mustVerify`,
finalize the carried deferred values, hash the step-side messages, run the group half at the
rebuilt wrap statement from the hash's sponge after the key, and return the finalized round
challenges with the verdict `(verified ∧ finalized) ∨ ¬mustVerify`. -/
def verifyOne (E : Env IpaPallas.curve nc) (P : FopParams Fp) (domains : List (KnownDomain Fp))
    (vk : VkComms nc (AffinePoint (FVar Fp))) (inp : VerifyOneInput ks k nc) :
    CircuitM Fp c (FopOutput Fp × BoolVar Fp) := do
  assertEqual (inp.unfinalized.shouldFinalize : FVar Fp) (inp.mustVerify : FVar Fp)
  let fop ← finalizeOtherProofStep P domains ⟨inp.deferred, true_, inp.spongeDigest⟩ inp.evals
    inp.proofMask inp.prevChallenges inp.branchData.domainLog2
  let (msgStep, afterIndex) ← hashMessagesForNextStepProofOpt IpaPallas.curve.sponge.params vk
    inp.appState (inp.proofMask.zip (inp.prevSgs.zip inp.prevChallenges))
  let statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)) :=
    ⟨⟨⟨inp.deferred, inp.branchData⟩, inp.spongeDigest, inp.messagesForNextWrapProof⟩, msgStep⟩
  let success ← verifyProofAt E afterIndex (Snarky.not inp.mustVerify) statement inp.unfinalized
    (ivpInputOf inp.unfinalized.deferredValues (inp.sgOld.map (none, ·)) vk inp.proof)
  let verified ← Snarky.and success fop.finalized
  let result ← Snarky.or verified (Snarky.not inp.mustVerify)
  pure (fop, result)

end Pickles
