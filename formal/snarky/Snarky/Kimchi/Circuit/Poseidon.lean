import Snarky.Circuit.DSL.Monad
import Snarky.Kimchi.Semantics
import Poseidon.Basic
import Kimchi.Gate.Semantics.Poseidon

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

/-! ## Soundness

`Poseidon.poseidon_spec`: any satisfying valuation reads the returned state as
`Poseidon.blockCipher` of the input state — the fixture-validated production
permutation. The walk is three nodes (the bulk witness promises nothing, the
constraint carries the whole chain), and the finish assembles the payload's
`chainHolds` windows into the gate tower's `Chain` and applies
`chain_blockCipher`. -/

namespace Poseidon

open Std.Do

/-- Window `i` of a satisfied chain, read off the list by index: `chainHolds` from
position `k0` puts the gate's `Holds` on every five-apart window, at the constant
table's row `k0 + i`. -/
private theorem chainHolds_window [CommRing F] {M : Kimchi.Gate.Poseidon.Mds F}
    {rc : List (F × F × F)} :
    ∀ (i k0 : ℕ) (l : List (F × F × F)), chainHolds M rc k0 l →
      5 * i + 5 < l.length →
      Kimchi.Gate.Poseidon.Holds M (rcRow rc (k0 + i))
        ⟨l.getD (5 * i) (0, 0, 0), l.getD (5 * i + 1) (0, 0, 0),
         l.getD (5 * i + 2) (0, 0, 0), l.getD (5 * i + 3) (0, 0, 0),
         l.getD (5 * i + 4) (0, 0, 0), l.getD (5 * i + 5) (0, 0, 0)⟩
  | 0, k0, s0 :: s1 :: s2 :: s3 :: s4 :: s5 :: rest, h, _ => by
    simp only [chainHolds] at h
    simpa using h.1
  | i + 1, k0, s0 :: s1 :: s2 :: s3 :: s4 :: s5 :: rest, h, hlen => by
    simp only [chainHolds] at h
    have ih := chainHolds_window i (k0 + 1) (s5 :: rest) h.2
      (by simp at hlen ⊢; omega)
    rw [show k0 + 1 + i = k0 + (i + 1) by omega] at ih
    simpa [show ∀ j, 5 * (i + 1) + j = (5 * i + j) + 5 from fun j => by omega,
      List.getD] using ih
  | _, _, [], h, hlen => by simp at hlen
  | _, _, [_], h, hlen => by
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  | _, _, [_, _], h, hlen => by
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  | _, _, [_, _, _], h, hlen => by
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  | _, _, [_, _, _, _], h, hlen => by
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  | _, _, [_, _, _, _, _], h, hlen => by
    simp only [List.length_cons, List.length_nil] at hlen
    omega

/-- The gadget is sound: under any satisfying valuation, at a full-size constant
table, the returned state's values are `Poseidon.blockCipher` of the input state's
values. -/
theorem poseidon_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = 5 * 11) (s : FVar F × FVar F × FVar F)
    (Q : PostCond (FVar F × FVar F × FVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : FVar F × FVar F × FVar F) =>
        (r.1.val V, r.2.1.val V, r.2.2.val V)
          = Poseidon.blockCipher p (s.1.val V, s.2.1.val V, s.2.2.val V)) Q⦄
    (poseidon (c := KimchiConstraint F) p s)
    ⦃Q⦄ := by
  simp only [poseidon]
  mvcgen
  rename_i st hpre
  intro outs _
  mvcgen
  intro u _ hpay
  mvcgen
  refine hpre _ _ ?_
  have hchain : chainHolds (mdsOf p.mds) p.roundConstants.toList 0
      (read st.V ⟨p.mds, p.roundConstants.toList, s :: outs.toList⟩) := hpay
  let vs : List (F × F × F) :=
    read st.V ⟨p.mds, p.roundConstants.toList, s :: outs.toList⟩
  have hlen : vs.length = 56 := by
    simp [vs, read]
  let w : ℕ → Kimchi.Gate.Poseidon.Witness F := fun k =>
    ⟨vs.getD (5 * k) (0, 0, 0), vs.getD (5 * k + 1) (0, 0, 0),
     vs.getD (5 * k + 2) (0, 0, 0), vs.getD (5 * k + 3) (0, 0, 0),
     vs.getD (5 * k + 4) (0, 0, 0), vs.getD (5 * k + 5) (0, 0, 0)⟩
  have hch : Kimchi.Gate.Poseidon.Chain (Kimchi.Gate.Poseidon.mdsOfParams p)
      (fun i => p.roundConstants.toList.getD i (0, 0, 0)) w 11 := by
    refine ⟨fun i hi => ?_, fun i _ => rfl⟩
    have hw := chainHolds_window i 0 vs hchain (by omega)
    rw [Nat.zero_add] at hw
    exact hw
  have hrc : ∀ i < 5 * 11, (fun i => p.roundConstants.toList.getD i (0, 0, 0)) i
      = Kimchi.Gate.Poseidon.paramsRc p i := by
    intro i _
    simp [Kimchi.Gate.Poseidon.paramsRc, List.getD_eq_getElem?_getD,
      Array.getD_eq_getD_getElem?]
  have hbc := Kimchi.Gate.Poseidon.chain_blockCipher p
    (fun i => p.roundConstants.toList.getD i (0, 0, 0)) w 11 hch (by omega) hsize hrc
  have h0 : (w 0).s0 = (s.1.val st.V, s.2.1.val st.V, s.2.2.val st.V) := rfl
  have h55 : (w 10).s5
      = (outs[54].1.val st.V, outs[54].2.1.val st.V, outs[54].2.2.val st.V) := by
    show vs.getD 55 (0, 0, 0) = _
    rw [List.getD_eq_getElem vs (0, 0, 0) (by omega)]
    simp [vs, read, Vector.getElem_toList]
  rw [h0, h55] at hbc
  exact hbc

end Poseidon

end Snarky.Kimchi
