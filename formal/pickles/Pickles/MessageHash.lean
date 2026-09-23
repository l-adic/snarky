import Pickles.OptSponge
import Pickles.VkComms

/-!
# The accumulator digests

Transcribed from `Pickles/Wrap/MessageHash.purs` and `Pickles/Step/MessageHash.purs`. A digest
binds a proof's accumulator advice — the opening's `sg` and the expanded round challenges — to
the statement the next proof verifies. The wrap digest's starting sponge is the caller's:
`wrapVerify` starts it from a checkpoint that has already absorbed the dummy padding, keeping
those absorptions out of the circuit. The step digest starts fresh and absorbs the key
(`spongeAfterIndex`) and the application state: the outer digest then absorbs each proof's
advice on the plain sponge, the per-slot one keeps it under the proof's mask.
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

/-- The sponge after the key: its commitments absorbed chunk by chunk, `x` then `y`, in the
order `σ₀…σ₆`, the coefficients, the selectors. -/
def spongeAfterIndex {nc : ℕ} (p : Poseidon.Params F) (vk : VkComms nc (AffinePoint (FVar F))) :
    CircuitM F c (SpongeVar F) :=
  ((vk.sigmaComm.toList ++ vk.coefficientsComm.toList ++ vk.selectors).flatMap
      Vector.toList).foldlM
    (fun sv P => do
      let sv ← SpongeVar.absorb p sv P.x
      SpongeVar.absorb p sv P.y)
    SpongeVar.init

/-- The step proof's accumulator digest on the plain sponge: after the key, the application
state, then per proof `sg` and its challenges, then one squeeze. -/
def hashMessagesForNextStepProof {nc : ℕ} (p : Poseidon.Params F)
    (vk : VkComms nc (AffinePoint (FVar F))) (appState : List (FVar F))
    (proofs : List (AffinePoint (FVar F) × List (FVar F))) : CircuitM F c (FVar F) := do
  let sv ← spongeAfterIndex p vk
  let sv ← appState.foldlM (SpongeVar.absorb p) sv
  let sv ← (proofs.flatMap fun (sg, chals) => sg.x :: sg.y :: chals).foldlM
    (SpongeVar.absorb p) sv
  let (digest, _) ← SpongeVar.squeeze p sv
  pure digest

/-- The step proof's accumulator digest with each proof's advice kept under its mask, and the
sponge after the key, which the verify block resumes from: after the key and the application
state, per proof `sg` and its challenges on the conditional sponge. With no proofs there is no
masked input, and the plain sponge squeezes. -/
def hashMessagesForNextStepProofOpt {nc : ℕ} (p : Poseidon.Params F)
    (vk : VkComms nc (AffinePoint (FVar F))) (appState : List (FVar F))
    (proofs : List (BoolVar F × AffinePoint (FVar F) × List (FVar F))) :
    CircuitM F c (FVar F × SpongeVar F) := do
  let afterIndex ← spongeAfterIndex p vk
  let sv ← appState.foldlM (SpongeVar.absorb p) afterIndex
  match proofs with
  | [] => do
    let (digest, _) ← SpongeVar.squeeze p sv
    pure (digest, afterIndex)
  | _ => do
    let ov ← OptSponge.ofSponge p sv
    let ov := proofs.foldl (fun ov (b, sg, chals) =>
      (sg.x :: sg.y :: chals).foldl (fun ov x => OptSponge.optAbsorb ov (b, x)) ov) ov
    let (digest, _) ← OptSponge.optSqueeze p ov
    pure (digest, afterIndex)

end Pickles
