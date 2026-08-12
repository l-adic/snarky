import Snarky.Circuit.Types
import Snarky.Kimchi.Constraint.Reduction

/-!
# The Poseidon reducer

Port of `Snarky.Constraint.Kimchi.Poseidon`
(packages/snarky-kimchi/src/Snarky/Constraint/Kimchi/Poseidon.purs): the sponge-state
payload — 56 three-element states covering the 55-round permutation — and `reduce`:
eleven `poseidon` rows of five states each in the PERMUTED register order
`s0 s4 s1 s2 s3`, with each row's fifteen round constants as its coefficient row, plus
a trailing `zero` row carrying the output state. The reduction ORDER is the byte
contract: the states in index order, each triple left to right.

Name map: `PoseidonConstraint` and `reduce` keep their names; `addRoundState`
and the final row stay named helpers. PS's `PoseidonField` class supplies
`getRoundConstants`; that renders as the explicit parameter `rc : ℕ → F × F × F`,
a caller-supplied constant table.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- `Vector 56 (Vector 3 _)` renders as a TRIPLE LIST (the width is an emitter
  invariant, not a type index): at 168 operands the per-operand law template of
  steps 4–7 cannot fit the heartbeat budget, and the list shape is what the
  recursion below is structural over. The chunking (`splitAt`/`chunks`)
  becomes the structural recursion `rowsFromStates`, which chunks five states per
  row while more than one remains and turns the last state into the `zero` row;
  off-shape tails (unrepresentable in PS's types) emit nothing.
- PS's `Rows` newtype over `Vector 12` renders as the bare row list.

No semantics is stated here, and the constraint layer stays free of `Kimchi`
imports; the byte-equality corpus is the oracle.
-/

namespace Snarky.Kimchi

open Snarky

/-- The Poseidon block constraint (PS `PoseidonConstraint`): the 56 chained
three-element sponge states, input first, permutation output last. -/
structure PoseidonConstraint (F : Type u) where
  /-- The states in round order, each a width-3 triple. -/
  state : List (FVar F × FVar F × FVar F)
  deriving Repr, DecidableEq

variable {F : Type} {m : Type → Type}

/-- Pin one state triple, left to right. -/
private def reduceState [Add F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F] [Monad m]
    [PlonkReductionM F m] (t : FVar F × FVar F × FVar F) :
    m (Variable × Variable × Variable) := do
  let a ← reduceToVariable t.1
  let b ← reduceToVariable t.2.1
  let c ← reduceToVariable t.2.2
  pure (a, b, c)

/-- Pin the states in index order (the PS nested `traverse` as the structural fold). -/
private def reduceStates [Add F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F] [Monad m]
    [PlonkReductionM F m] :
    List (FVar F × FVar F × FVar F) → m (List (Variable × Variable × Variable))
  | [] => pure []
  | t :: ts => do
    let v ← reduceState t
    let vs ← reduceStates ts
    pure (v :: vs)

/-- One `poseidon` row (PS `addRoundState`): the chunk's five states in the permuted
register order `s0 s4 s1 s2 s3`, and rounds `5k … 5k+4`'s constants as the
coefficient row. -/
private def addRoundState (rc : ℕ → F × F × F) (k : ℕ)
    (q0 q1 q2 q3 q4 : Variable × Variable × Variable) : KimchiRow F :=
  { kind := .poseidon,
    vars := ⟨⟨[some q0.1, some q0.2.1, some q0.2.2,
               some q4.1, some q4.2.1, some q4.2.2,
               some q1.1, some q1.2.1, some q1.2.2,
               some q2.1, some q2.2.1, some q2.2.2,
               some q3.1, some q3.2.1, some q3.2.2]⟩, by simp⟩,
    coeffs := [(rc (5 * k)).1, (rc (5 * k)).2.1, (rc (5 * k)).2.2,
               (rc (5 * k + 1)).1, (rc (5 * k + 1)).2.1, (rc (5 * k + 1)).2.2,
               (rc (5 * k + 2)).1, (rc (5 * k + 2)).2.1, (rc (5 * k + 2)).2.2,
               (rc (5 * k + 3)).1, (rc (5 * k + 3)).2.1, (rc (5 * k + 3)).2.2,
               (rc (5 * k + 4)).1, (rc (5 * k + 4)).2.1, (rc (5 * k + 4)).2.2] }

/-- The trailing `zero` row: the output state in cells `0 … 2`, which the last
`poseidon` row reads as its next-row `s5`. -/
private def PoseidonConstraint.finalRow (s : Variable × Variable × Variable) : KimchiRow F :=
  { kind := .zero,
    vars := ⟨⟨[some s.1, some s.2.1, some s.2.2, none, none, none, none, none,
               none, none, none, none, none, none, none]⟩, by simp⟩,
    coeffs := [] }

/-- Chunk the pinned states into rows: five per `poseidon` row while more than one
state remains (`k` counts rows for the constant offsets), the last state becomes the
`zero` row. Off-shape tails emit nothing (unreachable from the deployed
`11 × 5 + 1` emitter). -/
private def rowsFromStates (rc : ℕ → F × F × F) :
    ℕ → List (Variable × Variable × Variable) → List (KimchiRow F)
  | _, [] => []
  | _, [s] => [PoseidonConstraint.finalRow s]
  | k, q0 :: q1 :: q2 :: q3 :: q4 :: rest =>
    match rest with
    | [] => []
    | _ :: _ => addRoundState rc k q0 q1 q2 q3 q4 :: rowsFromStates rc (k + 1) rest
  | _, _ => []

/-- Reduce a Poseidon block (PS `reduce`): pin every state, then lay out the eleven
rows and the trailing `zero` row. -/
def PoseidonConstraint.reduce [Add F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F]
    [Monad m] [PlonkReductionM F m] (rc : ℕ → F × F × F) (c : PoseidonConstraint F) :
    m (List (KimchiRow F)) := do
  let vs ← reduceStates c.state
  pure (rowsFromStates rc 0 vs)

end Snarky.Kimchi
