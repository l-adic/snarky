import Snarky.Encoding
import Snarky.Kimchi.Constraint.Reduction

/-!
# The EndoScalar reducer

Port of packages/snarky-kimchi/src/Snarky/Constraint/Kimchi/EndoScalar.purs: the per-round
challenge-decomposition payload — six accumulator operands and eight crumb operands — and
`reduce`, one `endoScalar` row per round.

The reduction order is the byte contract: the crumbs in index order, then
`b8, a8, b0, a0, n8, n0`. It matters beyond cell numbering: `b0` and `a0` are both the
constant `2` in a challenge's first round, so whichever reduces first creates the pinned
variable and the other wires to it through the builder's constant cache.

The rounds and the crumbs are reduced by explicit recursion and eight explicit steps, not a
vector-level map, so the reduction stays kernel-reducible and peelable.

No row-shape law is stated here: the constraint layer imports nothing from the kimchi package.
-/

namespace Snarky.Kimchi

open Snarky

/-- One challenge-decomposition round: the three accumulator pairs and the eight 2-bit crumbs,
as in `Kimchi.Gate.EndoScalar.Witness`. -/
structure EndoScalarRound (F : Type u) where
  /-- The input `n` accumulator. -/
  n0 : FVar F
  /-- The output `n` accumulator. -/
  n8 : FVar F
  /-- The input `a` accumulator. -/
  a0 : FVar F
  /-- The output `a` accumulator. -/
  a8 : FVar F
  /-- The input `b` accumulator. -/
  b0 : FVar F
  /-- The output `b` accumulator. -/
  b8 : FVar F
  /-- The MSB-first 2-bit crumbs, eight per row. -/
  xs : Vector (FVar F) 8

/-- A challenge decomposition: its rounds in row order. -/
abbrev EndoScalar (F : Type u) := List (EndoScalarRound F)

variable {F : Type} {m : Type → Type}

/-- Reduce one round to its `endoScalar` row, in the module docstring's order. -/
def EndoScalarRound.reduce [Add F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F]
    [Monad m] [PlonkReductionM F m] (c : EndoScalarRound F) : m (KimchiRow F) := do
  let x0 ← reduceToVariable c.xs[0]
  let x1 ← reduceToVariable c.xs[1]
  let x2 ← reduceToVariable c.xs[2]
  let x3 ← reduceToVariable c.xs[3]
  let x4 ← reduceToVariable c.xs[4]
  let x5 ← reduceToVariable c.xs[5]
  let x6 ← reduceToVariable c.xs[6]
  let x7 ← reduceToVariable c.xs[7]
  let b8 ← reduceToVariable c.b8
  let a8 ← reduceToVariable c.a8
  let b0 ← reduceToVariable c.b0
  let a0 ← reduceToVariable c.a0
  let n8 ← reduceToVariable c.n8
  let n0 ← reduceToVariable c.n0
  pure { kind := .endoScalar,
         vars := ⟨⟨[some n0, some n8, some a0, some b0, some a8, some b8, some x0,
                    some x1, some x2, some x3, some x4, some x5, some x6, some x7,
                    none]⟩, by simp⟩,
         coeffs := [] }

/-- Reduce a decomposition round by round, in row order. -/
def EndoScalar.reduce [Add F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F]
    [Monad m] [PlonkReductionM F m] : EndoScalar F → m (List (KimchiRow F))
  | [] => pure []
  | c :: cs => do
    let row ← c.reduce
    let rest ← EndoScalar.reduce cs
    pure (row :: rest)

end Snarky.Kimchi
