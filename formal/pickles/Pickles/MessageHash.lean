import Snarky.Kimchi.Circuit.Sponge

/-!
# `messages_for_next_wrap_proof`, hashed

The port of PS `Pickles.Wrap.MessageHash.hashMessagesForNextWrapProofCircuit'` (OCaml
`wrap_hack.ml:119–142`), the digest the wrap circuit commits its accumulator advice to: the
challenge vectors absorbed in order, then `sg`'s two coordinates, then a squeeze.

The advice is the pair a recursion carries — the opening's `sg` and the expanded round
challenges — so this digest is what binds one proof's accumulator to the statement the next
proof verifies. The starting sponge is the caller's: the standalone circuit hashes from the
fresh sponge, while `Wrap.Main`'s verify block starts from the checkpoint that has already
absorbed the dummy padding, keeping those absorptions out of the circuit.
-/

namespace Pickles

open Snarky Snarky.Kimchi

variable {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] [KimchiSystem F c]

/-- The `messages_for_next_wrap_proof` digest of the accumulator advice, from the sponge
`sv`: every challenge vector absorbed in order, then `sg.x` and `sg.y`, then squeezed. -/
def hashMessagesForNextWrapProof (p : Poseidon.Params F) (sv : SpongeVar F)
    (allChallenges : List (List (FVar F))) (sg : AffinePoint (FVar F)) :
    CircuitM F c (FVar F) := do
  let sv ← allChallenges.flatten.foldlM (SpongeVar.absorb p) sv
  let sv ← SpongeVar.absorb p sv sg.x
  let sv ← SpongeVar.absorb p sv sg.y
  let (digest, _) ← SpongeVar.squeeze p sv
  pure digest

end Pickles
