import Pickles.IncrementallyVerify
import Pickles.MessageHash

/-!
# `Wrap.Main`'s verify block

The port of PS `Pickles.Wrap.Verify.wrapVerify`, the wrap circuit's group half over the step
proof it verifies. It is `incrementally_verify_proof` on the conditional sponge plus the four
assertions the block makes:

* the opening's success bit holds outright — the wrap side has no `should_finalize` to defer
  it to, unlike `Step_verifier.verify`, which returns the bit;
* the accumulator advice hashes to the `messages_for_next_wrap_proof` digest the statement
  claims (`hashMessagesForNextWrapProof`), which is what binds this proof's `sg` and round
  challenges to the statement the next proof verifies;
* the fq digest equals the claimed `sponge_digest_before_evaluations`;
* each returned round prechallenge equals its claim, pair by pair over the zip.

The message sponge is the caller's, as in PureScript: the deployed block starts it from the
checkpoint that has already absorbed the dummy padding, so those absorptions stay out of the
circuit.
-/

namespace Pickles

open Snarky Snarky.Kimchi

variable {F c : Type} [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c]

/-- The wrap circuit's verify block: the group half, then its four assertions. -/
def wrapVerify {sf : Type} {k : ℕ} (ops : IpaScalarOps F c sf) (e : IpaEndo F)
    (p : Poseidon.Params F) (endo : FVar F) (gm : GroupMapParams F) (sqrtF : F → Option F)
    (blindingH : AffinePoint (FVar F)) (spongeAfterIndex : SpongeVar F)
    (computeXHat : CircuitM F c (List (AffinePoint (FVar F)))) (msgSponge : SpongeVar F)
    (newBpChallenges : List (List (FVar F))) (claimedMsgDigest claimedDigest : FVar F)
    (claimedChallenges : List (SizedF 128 (FVar F)))
    (inp : IvpInput k (FVar F) (BoolVar F) sf) : CircuitM F c PUnit := do
  let o ← incrementallyVerifyProof ops e p endo gm sqrtF true blindingH spongeAfterIndex
    computeXHat inp
  assert o.success
  let d ← hashMessagesForNextWrapProof p msgSponge newBpChallenges inp.opening.sg
  assertEqual claimedMsgDigest d
  assertEqual claimedDigest o.spongeDigest
  for cc in claimedChallenges.zip o.bulletproofChallenges do
    assertEqual cc.1.val cc.2.val
  pure PUnit.unit

end Pickles
