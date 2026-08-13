import Snarky.Circuit.Types
import Snarky.Kimchi.Constraint.AddComplete
import Snarky.Kimchi.Constraint.Reduction

/-!
# The VarBaseMul reducer

Port of `Snarky.Constraint.Kimchi.VarBaseMul`
(packages/snarky-kimchi/src/Snarky/Constraint/Kimchi/VarBaseMul.purs): the per-round
scale payload — six accumulator points, five bits, five slopes, the two scalar
registers, and the base point — and `reduce`, one `varBaseMul`/`zero` ROW PAIR per
round (the gate's constraints span both rows).

The per-round reduction ORDER is the byte contract: accumulators pointwise in
index order, then bits, slopes, `nPrev`, `nNext`, and the base LAST. Unlike
AddComplete's `reduce_curve_point`, this module's local point reducer runs `x` BEFORE
`y` (PS `reducePointToVariable` is a `do`-block, not an OCaml record map — no
right-to-left reversal), so points here are pinned x-first.

Name map: `ScaleRound`, `VarBaseMul`, `reduce` keep their names (namespaced);
`AffinePoint` is `Constraint/AddComplete.lean`'s record — the PS import from
`Snarky.Data.EllipticCurve` resolves to it.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- The width-fixed vectors (`Vector 6` accumulators, `Vector 5` bits/slopes) render as
  NAMED FIELDS (`acc0 … acc5`, `bit0 … bit4`, `slope0 … slope4`) — the same choice
  `Kimchi.Gate.VarBaseMul.Witness` makes for its columns. The widths are gate
  constants, and named fields keep every operand access a plain projection: indexed
  `Vector` access re-runs its bounds tactic at every elaboration site, which summed
  over twenty-six operands in statements and proofs blows the heartbeat budget.
- PS's `Rows` newtype over `Array (Vector 2 row)` renders as the bare pair list
  `List (KimchiRow F × KimchiRow F)` with the concatenating `ToKimchiRows` instance
  below; the width-fixed `traverse`s unroll to their applications in index order.

No row-shape law is stated here: the constraint layer stays free of `Kimchi`
imports.
-/

namespace Snarky.Kimchi

open Snarky

/-- One scale round (PS `ScaleRound`): the accumulators `P₀ … P₅`, the five bits and
five slopes, the scalar registers, and the base point `T`. -/
structure ScaleRound (F : Type u) where
  /-- Accumulator point `P0` (input). -/
  acc0 : AffinePoint (FVar F)
  /-- Accumulator point `P1`. -/
  acc1 : AffinePoint (FVar F)
  /-- Accumulator point `P2`. -/
  acc2 : AffinePoint (FVar F)
  /-- Accumulator point `P3`. -/
  acc3 : AffinePoint (FVar F)
  /-- Accumulator point `P4`. -/
  acc4 : AffinePoint (FVar F)
  /-- Accumulator point `P5` (output). -/
  acc5 : AffinePoint (FVar F)
  /-- Scalar bit 0 of this round. -/
  bit0 : FVar F
  /-- Scalar bit 1 of this round. -/
  bit1 : FVar F
  /-- Scalar bit 2 of this round. -/
  bit2 : FVar F
  /-- Scalar bit 3 of this round. -/
  bit3 : FVar F
  /-- Scalar bit 4 of this round. -/
  bit4 : FVar F
  /-- First-addition slope of bit block 0. -/
  slope0 : FVar F
  /-- First-addition slope of bit block 1. -/
  slope1 : FVar F
  /-- First-addition slope of bit block 2. -/
  slope2 : FVar F
  /-- First-addition slope of bit block 3. -/
  slope3 : FVar F
  /-- First-addition slope of bit block 4. -/
  slope4 : FVar F
  /-- The input scalar register. -/
  nPrev : FVar F
  /-- The output scalar register. -/
  nNext : FVar F
  /-- The base point `T`. -/
  base : AffinePoint (FVar F)
  deriving Repr, DecidableEq

/-- A variable-base scalar multiplication: its rounds in row order (PS `VarBaseMul`). -/
abbrev VarBaseMul (F : Type u) := List (ScaleRound F)

/-- A pair list flattens pairwise, in order — the row-pair emitters' carrier (PS
`Rows` over `Array (Vector 2 _)`, its `concatMap`). -/
instance : ToKimchiRows F (List (KimchiRow F × KimchiRow F)) where
  toKimchiRows rs := rs.flatMap fun p => [p.1, p.2]

variable {F : Type} {m : Type → Type}

/-- Reduce one round to its `varBaseMul`/`zero` row pair (PS `reduceRound` +
`makeRows`): accumulators pointwise x-first, then bits, slopes, registers, base. -/
def ScaleRound.reduce [Add F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F]
    [Monad m] [PlonkReductionM F m] (c : ScaleRound F) :
    m (KimchiRow F × KimchiRow F) := do
  let va0x ← reduceToVariable c.acc0.x
  let va0y ← reduceToVariable c.acc0.y
  let va1x ← reduceToVariable c.acc1.x
  let va1y ← reduceToVariable c.acc1.y
  let va2x ← reduceToVariable c.acc2.x
  let va2y ← reduceToVariable c.acc2.y
  let va3x ← reduceToVariable c.acc3.x
  let va3y ← reduceToVariable c.acc3.y
  let va4x ← reduceToVariable c.acc4.x
  let va4y ← reduceToVariable c.acc4.y
  let va5x ← reduceToVariable c.acc5.x
  let va5y ← reduceToVariable c.acc5.y
  let vb0 ← reduceToVariable c.bit0
  let vb1 ← reduceToVariable c.bit1
  let vb2 ← reduceToVariable c.bit2
  let vb3 ← reduceToVariable c.bit3
  let vb4 ← reduceToVariable c.bit4
  let vs0 ← reduceToVariable c.slope0
  let vs1 ← reduceToVariable c.slope1
  let vs2 ← reduceToVariable c.slope2
  let vs3 ← reduceToVariable c.slope3
  let vs4 ← reduceToVariable c.slope4
  let vnp ← reduceToVariable c.nPrev
  let vnn ← reduceToVariable c.nNext
  let vbx ← reduceToVariable c.base.x
  let vby ← reduceToVariable c.base.y
  pure ({ kind := .varBaseMul,
          vars := ⟨⟨[some vbx, some vby, some va0x, some va0y, some vnp, some vnn,
                     none, some va1x, some va1y, some va2x, some va2y,
                     some va3x, some va3y, some va4x, some va4y]⟩, by simp⟩,
          coeffs := [] },
        { kind := .zero,
          vars := ⟨⟨[some va5x, some va5y, some vb0, some vb1, some vb2, some vb3,
                     some vb4, some vs0, some vs1, some vs2, some vs3,
                     some vs4, none, none, none]⟩, by simp⟩,
          coeffs := [] })

/-- Reduce a multiplication roundwise, in row order (PS `reduce`, its `traverse` as
the structural fold). -/
def VarBaseMul.reduce [Add F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F]
    [Monad m] [PlonkReductionM F m] :
    VarBaseMul F → m (List (KimchiRow F × KimchiRow F))
  | [] => pure []
  | c :: cs => do
    let pair ← c.reduce
    let rest ← VarBaseMul.reduce cs
    pure (pair :: rest)

end Snarky.Kimchi
