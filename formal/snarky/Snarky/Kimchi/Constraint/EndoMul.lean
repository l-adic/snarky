import Snarky.Encoding
import Snarky.Kimchi.Constraint.AddComplete
import Snarky.Kimchi.Constraint.Reduction

/-!
# The EndoMul reducer

Port of packages/snarky-kimchi/src/Snarky/Constraint/Kimchi/EndoMul.purs: the per-round GLV
window payload and `reduce` — one `endoMul` row per round, then a trailing `zero` row holding
the final accumulator and scalar, which the last round's two-row gate reads as its next-row
outputs.

The reduction order is the byte contract: the final accumulator `s` and scalar `nAcc` first,
then each round in row order — `t` and `p` x-first, `nAcc`, `r`, `s1`, `s3`, the four bits in
index order, `inv` last.

Deviations from the upstream:
- The rounds are a plain list; nonemptiness is the emitters' invariant, not the type's. The
  four window bits are named fields `bit0 … bit3`.
- The payload carries the endomorphism coefficient `endo` (upstream, a curve constant) so the
  semantics can read the gate at it. `reduce` ignores it: the row has no coefficient cells.
-/

namespace Snarky.Kimchi

open Snarky

/-- One GLV window round: the operands of one `endoMul` row, plus the outputs `s` and
`nAccNext` that the next row holds. -/
structure EndoMulRound (F : Type u) where
  /-- The base point `T`. -/
  t : AffinePoint (FVar F)
  /-- The input accumulator `P`. -/
  p : AffinePoint (FVar F)
  /-- The intermediate accumulator `R`, after the first window. -/
  r : AffinePoint (FVar F)
  /-- The output accumulator `S`; not reduced — the next row's `p` cells hold it. -/
  s : AffinePoint (FVar F)
  /-- The first window's slope. -/
  s1 : FVar F
  /-- The second window's slope. -/
  s3 : FVar F
  /-- The input scalar register. -/
  nAcc : FVar F
  /-- The output scalar register; not reduced — the next row's `nAcc` cell holds it. -/
  nAccNext : FVar F
  /-- Window bit `b₁` (first window's base choice). -/
  bit0 : FVar F
  /-- Window bit `b₂` (first window's sign). -/
  bit1 : FVar F
  /-- Window bit `b₃` (second window's base choice). -/
  bit2 : FVar F
  /-- Window bit `b₄` (second window's sign). -/
  bit3 : FVar F
  /-- The witnessed distinct-point inverse. -/
  inv : FVar F

/-- An endomorphism-optimized scalar multiplication: the rounds, the final accumulator and
scalar the trailing `zero` row carries, and the endomorphism coefficient. -/
structure EndoMul (F : Type u) where
  /-- The rounds, in row order. -/
  state : List (EndoMulRound F)
  /-- The final output accumulator. -/
  s : AffinePoint (FVar F)
  /-- The final scalar register. -/
  nAcc : FVar F
  /-- The endomorphism coefficient: parameter data, not a wire; `reduce` ignores it. -/
  endo : F

variable {F : Type} {m : Type → Type}

/-- Reduce one round to its `endoMul` row, with cells
`[xT yT inv _ xP yP n xR yR s1 s3 b₁ b₂ b₃ b₄]`. -/
def EndoMulRound.reduce [Add F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F]
    [Monad m] [PlonkReductionM F m] (c : EndoMulRound F) : m (KimchiRow F) := do
  let vtx ← reduceToVariable c.t.x
  let vty ← reduceToVariable c.t.y
  let vpx ← reduceToVariable c.p.x
  let vpy ← reduceToVariable c.p.y
  let vn ← reduceToVariable c.nAcc
  let vrx ← reduceToVariable c.r.x
  let vry ← reduceToVariable c.r.y
  let vs1 ← reduceToVariable c.s1
  let vs3 ← reduceToVariable c.s3
  let vb1 ← reduceToVariable c.bit0
  let vb2 ← reduceToVariable c.bit1
  let vb3 ← reduceToVariable c.bit2
  let vb4 ← reduceToVariable c.bit3
  let vinv ← reduceToVariable c.inv
  pure { kind := .endoMul,
         vars := ⟨⟨[some vtx, some vty, some vinv, none, some vpx, some vpy,
                    some vn, some vrx, some vry, some vs1, some vs3,
                    some vb1, some vb2, some vb3, some vb4]⟩, by simp⟩,
         coeffs := [] }

/-- The trailing `zero` row: the final accumulator and scalar in cells `4, 5, 6`, which the
last `endoMul` row reads as its outputs. -/
private def EndoMul.finalZeroRow (xs ys nAcc : Variable) : KimchiRow F :=
  { kind := .zero,
    vars := ⟨⟨[none, none, none, none, some xs, some ys, some nAcc, none, none,
               none, none, none, none, none, none]⟩, by simp⟩,
    coeffs := [] }

/-- Reduce the rounds in row order. -/
private def EndoMul.reduceRounds [Add F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F]
    [Monad m] [PlonkReductionM F m] : List (EndoMulRound F) → m (List (KimchiRow F))
  | [] => pure []
  | c :: cs => do
    let row ← c.reduce
    let rest ← EndoMul.reduceRounds cs
    pure (row :: rest)

/-- Reduce a multiplication: the final accumulator and scalar first, then the rounds, then
the trailing `zero` row. -/
def EndoMul.reduce [Add F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F]
    [Monad m] [PlonkReductionM F m] (c : EndoMul F) : m (List (KimchiRow F)) := do
  let xs ← reduceToVariable c.s.x
  let ys ← reduceToVariable c.s.y
  let nAcc ← reduceToVariable c.nAcc
  let rows ← EndoMul.reduceRounds c.state
  pure (rows ++ [EndoMul.finalZeroRow xs ys nAcc])

end Snarky.Kimchi
