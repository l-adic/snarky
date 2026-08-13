import Snarky.Circuit.DSL.Monad
import Snarky.Kimchi.Semantics
import Poseidon.Basic

/-!
# The Poseidon gadget

Port of `Snarky.Circuit.Kimchi.Poseidon`
(packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/Poseidon.purs): witness the 55 round
outputs of the permutation in ONE bulk `exists` — the traversal lives inside the
witness computation, so the circuit itself is three binds — emit the block constraint
over the 56 chained states, and return the output state.

Name map: `poseidon` keeps its name; the `exists` body's `scanl` renders as the
indexed prefix map `roundsUpTo` (same values, and output `i` is the `(i + 1)`-round
prefix by definition).

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- PS's ambient `PoseidonField` class arrives as the explicit parameter
  `p : Poseidon.Params F`, whose data the emitted payload carries (the payload-data
  deviation in `Constraint/Poseidon.lean`).
- PS's width-3 `Vector` states render as triples, matching the payload.
- The PS `label "poseidon"` wrapper is dropped (labels are not threaded —
  `Kimchi/Constraint.lean`'s deviation ledger).
-/

namespace Snarky.Kimchi

open Snarky

variable {F c : Type}

/-- The state after rounds `0 … k − 1` (the `k`-prefix of the `blockCipher` fold;
`getD` never fires at the deployed 55-entry table). -/
private def roundsUpTo [Field F] (p : Poseidon.Params F) :
    ℕ → F × F × F → F × F × F
  | 0, s => s
  | k + 1, s =>
    Poseidon.fullRound p.mds (p.roundConstants.getD k (0, 0, 0)) (roundsUpTo p k s)

/-- The bulk witness: read the input state, return all 55 round outputs, oldest
first (the PS `exists` body's `scanl`). -/
private def roundOutputsWit [Field F] (p : Poseidon.Params F)
    (s : FVar F × FVar F × FVar F) : AsProver F (Vector (F × F × F) 55) := do
  let s0 ← AsProver.readCVar s.1
  let s1 ← AsProver.readCVar s.2.1
  let s2 ← AsProver.readCVar s.2.2
  pure (Vector.ofFn fun i => roundsUpTo p (i.1 + 1) (s0, s1, s2))

/-- The Poseidon permutation gadget (PS `poseidon`): one bulk witness of the round
outputs, one block constraint over the 56 chained states at `p`'s data, the last
state returned. -/
def poseidon [Field F] [KimchiSystem F c] (p : Poseidon.Params F)
    (initialState : FVar F × FVar F × FVar F) :
    CircuitM F c (FVar F × FVar F × FVar F) := do
  let roundOutputs ← witness (val := Vector (F × F × F) 55)
    (roundOutputsWit p initialState)
  addConstraint (KimchiSystem.poseidon
    { mds := p.mds, rc := p.roundConstants.toList,
      state := initialState :: roundOutputs.toList })
  pure roundOutputs[54]

end Snarky.Kimchi
