import Snarky.Kimchi.Circuit.Sponge

/-!
# The wrap proof's accumulator digest

Transcribed from `Pickles/Wrap/MessageHash.purs`. The digest binds a proof's accumulator
advice — the opening's `sg` and the expanded round challenges — to the statement the next proof
verifies. The starting sponge is the caller's: `wrapVerify` starts it from a checkpoint that has
already absorbed the dummy padding, keeping those absorptions out of the circuit.
-/

namespace Pickles

open Snarky Snarky.Kimchi

variable {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] [KimchiSystem F c]

/-- The accumulator digest from the sponge `sv`: every challenge vector absorbed in order, then
`sg.x` and `sg.y`, then one squeeze. -/
def hashMessagesForNextWrapProof (p : Poseidon.Params F) (sv : SpongeVar F)
    (allChallenges : List (List (FVar F))) (sg : AffinePoint (FVar F)) :
    CircuitM F c (FVar F) := do
  let sv ← allChallenges.flatten.foldlM (SpongeVar.absorb p) sv
  let sv ← SpongeVar.absorb p sv sg.x
  let sv ← SpongeVar.absorb p sv sg.y
  let (digest, _) ← SpongeVar.squeeze p sv
  pure digest

end Pickles
