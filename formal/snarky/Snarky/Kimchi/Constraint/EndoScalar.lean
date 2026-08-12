import Snarky.Circuit.Types
import Snarky.Kimchi.Constraint.Reduction

/-!
# The EndoScalar reducer

Port of `Snarky.Constraint.Kimchi.EndoScalar`
(packages/snarky-kimchi/src/Snarky/Constraint/Kimchi/EndoScalar.purs): the per-round
challenge-decomposition payload — six accumulator operands and eight crumb operands —
and `reduce`, one fourteen-cell `endoScalar` row per round.

The per-round reduction ORDER is the byte contract and is OCaml's right-to-left
record evaluation (`Endoscale_scalar_round.map`): the crumbs `xs` first (in index
order), then `b8, a8, b0, a0, n8, n0`. PS's own comment records why it matters beyond
cell numbering: `b0` and `a0` are both the constant `2` in a challenge's first round,
so whichever reduces first creates the pinned variable and the second WIRES to it
through the builder's constant cache.

Name map: `EndoScalarRound`, `EndoScalar`, and `reduce` keep their names (the
latter namespaced as `EndoScalar.reduce`/`EndoScalarRound.reduce`, one per PS
declaration level).

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- PS's per-module `Rows` newtype over an array renders as the bare
  `List (KimchiRow F)` with the identity `ToKimchiRows` instance (`Constraint/Types`).
- PS `traverse` over the round array renders as the structural fold it denotes, and
  the `traverse` over the width-8 crumb vector as its eight applications in index
  order — kernel-reducible and peelable where `Vector`-level `mapM` is neither.

No row-shape law is stated here: the constraint layer stays free of `Kimchi`
imports.
-/

namespace Snarky.Kimchi

open Snarky

/-- One challenge-decomposition round (PS `EndoScalarRound`): the three accumulator
pairs and the eight 2-bit crumbs, mirroring `Kimchi.Gate.EndoScalar.Witness`. -/
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
  deriving Repr, DecidableEq

/-- A challenge decomposition: its rounds in row order (PS `EndoScalar`). -/
abbrev EndoScalar (F : Type u) := List (EndoScalarRound F)

variable {F : Type} {m : Type → Type}

/-- Reduce one round to its `endoScalar` row (PS `reduceRound`): crumbs first in index
order, then `b8, a8, b0, a0, n8, n0` (OCaml right-to-left), cells laid out
`[n0, n8, a0, b0, a8, b8, x₀ … x₇]`. -/
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

/-- Reduce a decomposition roundwise, in row order (PS `reduce`, its `traverse` as the
structural fold). -/
def EndoScalar.reduce [Add F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F]
    [Monad m] [PlonkReductionM F m] : EndoScalar F → m (List (KimchiRow F))
  | [] => pure []
  | c :: cs => do
    let row ← c.reduce
    let rest ← EndoScalar.reduce cs
    pure (row :: rest)

/-! ## Examples -/

/-- Fourteen variable operands pin to themselves: cells `[n0 n8 a0 b0 a8 b8 | crumbs]`
in gate-column order, nothing allocated. -/
example :
    Id.run ((EndoScalarRound.reduce (m := TraceM Int)
        ({ n0 := .var 0, n8 := .var 1, a0 := .var 2, a8 := .var 4, b0 := .var 3,
           b8 := .var 5,
           xs := ⟨⟨[.var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12,
                    .var 13]⟩, by simp⟩ } : EndoScalarRound Int)).run
        ⟨14, [], []⟩) =
      ({ kind := .endoScalar,
         vars := ⟨⟨[some 0, some 1, some 2, some 3, some 4, some 5, some 6, some 7,
                    some 8, some 9, some 10, some 11, some 12, some 13, none]⟩,
           by simp⟩,
         coeffs := [] }, ⟨14, [], []⟩) := by decide

/-- The first-round constants: `b0` reduces BEFORE `a0` (right-to-left), so `b0` pins
fresh variable `14` and `a0` pins `15` — the builder's constant cache would then WIRE
`15` to `14`; the trace records both pins. -/
example :
    Id.run ((EndoScalarRound.reduce (m := TraceM Int)
        ({ n0 := .var 0, n8 := .var 1, a0 := .const 2, a8 := .var 4, b0 := .const 2,
           b8 := .var 5,
           xs := ⟨⟨[.var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12,
                    .var 13]⟩, by simp⟩ } : EndoScalarRound Int)).run
        ⟨14, [], []⟩) =
      ({ kind := .endoScalar,
         vars := ⟨⟨[some 0, some 1, some 15, some 14, some 4, some 5, some 6, some 7,
                    some 8, some 9, some 10, some 11, some 12, some 13, none]⟩,
           by simp⟩,
         coeffs := [] },
        ⟨16, [], [⟨1, some 15, 2, none⟩, ⟨1, some 14, 2, none⟩]⟩) := by decide

end Snarky.Kimchi
