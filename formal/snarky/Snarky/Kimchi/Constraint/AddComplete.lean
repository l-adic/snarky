import Snarky.Encoding
import Snarky.Kimchi.Constraint.Reduction

/-!
# The AddComplete reducer

Transcribes packages/snarky-kimchi/src/Snarky/Constraint/Kimchi/AddComplete.purs: the
complete-addition payload `AddComplete` (three affine points and five auxiliary operands)
and `AddComplete.reduce`, which pins every operand to a variable and emits one eleven-cell
`addComplete` row. The order in which operands are pinned is the byte contract; it follows
the upstream right-to-left evaluation.

`AffinePoint` is defined here generically, so the VarBaseMul payload and the circuit layer
share one record.

No semantics is stated here: the constraint layer imports nothing from `Kimchi`, and the
reducer's faithfulness is not proved in this package.
-/

namespace Snarky.Kimchi

open Snarky

/-- An affine point over an operand type: the coordinate pair `x`, `y`. -/
structure AffinePoint (α : Type u) where
  /-- The x-coordinate. -/
  x : α
  /-- The y-coordinate. -/
  y : α

/-- The complete-addition constraint payload: `p1 + p2 = p3` with the auxiliary columns the
gate consumes, field for field as in `Kimchi.Gate.AddComplete.Witness`. -/
structure AddComplete (F : Type u) where
  /-- The first addend. -/
  p1 : AffinePoint (FVar F)
  /-- The second addend. -/
  p2 : AffinePoint (FVar F)
  /-- The output sum. -/
  p3 : AffinePoint (FVar F)
  /-- The infinity flag: `1` when the sum is the point at infinity. -/
  inf : FVar F
  /-- The equal-x flag, pinned via the witnessed `x21Inv`. -/
  sameX : FVar F
  /-- The addition slope. -/
  s : FVar F
  /-- The witnessed inverse pinning the infinity flag. -/
  infZ : FVar F
  /-- The witnessed inverse of `x₂ − x₁` when nonzero. -/
  x21Inv : FVar F

variable {F : Type} {m : Type → Type}

/-- Pin a point's operands, `y` before `x`; the order is emission order, hence fixture
bytes. -/
private def reduceAffinePoint [Add F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F]
    [Monad m] [PlonkReductionM F m] (p : AffinePoint (FVar F)) :
    m (AffinePoint Variable) := do
  let y ← reduceToVariable p.y
  let x ← reduceToVariable p.x
  pure ⟨x, y⟩

/-- Reduce a complete-addition constraint to its one `addComplete` row: pin the three points,
then the auxiliary operands from `x21Inv` back to `inf`, and lay the eleven cells out in
gate-column order. -/
def AddComplete.reduce [Add F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F]
    [Monad m] [PlonkReductionM F m] (c : AddComplete F) : m (Rows F) := do
  let p1 ← reduceAffinePoint c.p1
  let p2 ← reduceAffinePoint c.p2
  let p3 ← reduceAffinePoint c.p3
  let x21Inv ← reduceToVariable c.x21Inv
  let infZ ← reduceToVariable c.infZ
  let s ← reduceToVariable c.s
  let sameX ← reduceToVariable c.sameX
  let inf ← reduceToVariable c.inf
  pure ⟨{ kind := .addComplete,
          vars := ⟨⟨[some p1.x, some p1.y, some p2.x, some p2.y, some p3.x,
                     some p3.y, some inf, some sameX, some s, some infZ,
                     some x21Inv] ++ List.replicate 4 none⟩, by simp⟩,
          coeffs := [] }⟩

end Snarky.Kimchi
