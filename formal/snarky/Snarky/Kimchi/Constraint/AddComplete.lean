import Snarky.Circuit.Types
import Snarky.Kimchi.Constraint.Reduction

/-!
# The AddComplete reducer

Port of `Snarky.Constraint.Kimchi.AddComplete`
(packages/snarky-kimchi/src/Snarky/Constraint/Kimchi/AddComplete.purs): the
complete-addition constraint payload — three affine points and the five auxiliary
columns — and `reduce`, which pins every operand to a variable and emits the one
eleven-cell `addComplete` row. The reduction ORDER is the byte contract, and it is
OCaml's right-to-left evaluation twice over: within a point `y` before `x`
(`reduce_curve_point`), and the auxiliary operands from `x21Inv` back to `inf` before
the cells are laid out left to right.

Name map: `AddComplete` and `reduce` keep their names, the latter namespaced as
`AddComplete.reduce` (`Snarky.Kimchi.reduce` is the Basic reducer — PS disambiguates by
module, Lean by the payload's namespace). The PS anonymous point records render as
`AffinePoint` — the name of the `Snarky.Data.EllipticCurve` type the VarBaseMul step
reduces onto, defined here generically so both use one record. `reduceAffinePoint`
stays a named helper.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- PS re-declares an identical `Rows` newtype (one row, singleton `toKimchiRows`); Lean
  reuses `Snarky.Kimchi.Rows`, which is that type.

No semantics is stated here: the constraint layer stays free of `Kimchi` imports,
and the reducer's faithfulness is deliberately not part of this package.
-/

namespace Snarky.Kimchi

open Snarky

/-- An affine point of paired operands (the PS anonymous `{x, y}` record here;
`Snarky.Data.EllipticCurve.AffinePoint` at the VarBaseMul step). -/
structure AffinePoint (α : Type u) where
  /-- The x-coordinate. -/
  x : α
  /-- The y-coordinate. -/
  y : α
  deriving Repr, DecidableEq

/-- The complete-addition constraint payload (PS `AddComplete`): `p1 + p2 = p3` with
the auxiliary columns the gate's constraints consume. The field roles mirror
`Kimchi.Gate.AddComplete.Witness`, column for column. -/
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
  deriving Repr, DecidableEq

variable {F : Type} {m : Type → Type}

/-- Pin a point's operands, `y` before `x` (PS `reduceAffinePoint`, transcribing
OCaml's right-to-left `reduce_curve_point`) — the order is emission order, hence
fixture bytes. -/
private def reduceAffinePoint [Add F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F]
    [Monad m] [PlonkReductionM F m] (p : AffinePoint (FVar F)) :
    m (AffinePoint Variable) := do
  let y ← reduceToVariable p.y
  let x ← reduceToVariable p.x
  pure ⟨x, y⟩

/-- Reduce a complete-addition constraint to its one `addComplete` row (PS `reduce`):
pin the three points, then the auxiliary operands right to left (`x21Inv` first, `inf`
last), and lay the eleven cells out in gate-column order. -/
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

/-- `reduceAffinePoint` is a seam. -/
private theorem reduceAffinePoint_seam [Add F] [Mul F] [Sub F] [Div F] [Zero F] [One F] [Neg F]
    [DecidableEq F]
    (p : AffinePoint (FVar F)) :
    Seam (reduceAffinePoint (m := PlonkBuilder F) p)
      (reduceAffinePoint (m := PlonkProver F) p) := by
  unfold reduceAffinePoint
  repeat first
    | exact Seam.pure _
    | refine Seam.bind (reduceToVariable_seam _) fun _ => ?_

/-- The complete-addition reducer is a seam: eleven pinned operands, one row. -/
theorem AddComplete.reduce_seam [Add F] [Mul F] [Sub F] [Div F] [Zero F] [One F] [Neg F]
    [DecidableEq F] (c : AddComplete F) :
    Seam (AddComplete.reduce (m := PlonkBuilder F) c)
      (AddComplete.reduce (m := PlonkProver F) c) := by
  unfold AddComplete.reduce
  repeat first
    | exact Seam.pure _
    | refine Seam.bind (reduceAffinePoint_seam _) fun _ => ?_
    | refine Seam.bind (reduceToVariable_seam _) fun _ => ?_

end Snarky.Kimchi
