import Snarky.Kimchi.Circuit.AddComplete

/-!
# The curve-tagged point

Port of PS `WeierstrassAffinePoint`
(packages/snarky-curves/src/Snarky/Data/EllipticCurve.purs): an affine point whose TYPE
names its curve. The plain `AffinePoint` stays checks-free (the `genericCheck`
convention, `Circuit/AddComplete`); a statement carries THIS type where its wire
refinement is a genuine curve point, so the whole-circuit seam can force the public
reading on-curve.

Name map: PS's phantom tag `g` with its `WeierstrassCurve f g` params class becomes the
two coefficient indices `a b : F` — the same information, value-indexed.

The on-curve check itself (OCaml `assert_on_curve`) is not here yet: it is a gadget, and
this module currently carries only what a statement's ENCODING needs.
-/

namespace Snarky.Kimchi

open Snarky

variable {F : Type}

/-- An affine point tagged with its curve's coefficients (PS
`WeierstrassAffinePoint g f`). The tag is phantom on the data — the constraint arrives
through `CheckedType`, not the carrier. -/
structure CurvePoint (a b : F) (α : Type) where
  /-- The untagged coordinates. -/
  point : AffinePoint α

/-- The tag is phantom: a tagged point is its point. -/
@[simps apply symm_apply] def CurvePoint.equivPoint {a b : F} {α : Type} :
    CurvePoint a b α ≃ AffinePoint α where
  toFun p := p.point
  invFun p := ⟨p⟩
  left_inv _ := rfl
  right_inv _ := rfl

open CompElliptic.Curves.Pasta in
/-- A point tagged with Vesta's coefficients — what an `Fq`-circuit's public points are. -/
abbrev VestaPoint := CurvePoint (a := Vesta.curve.A) (b := Vesta.curve.B)

/-- The tagged point encodes exactly as its coordinates, `[x, y]`. -/
instance instCurvePointCircuitType {a b : F} :
    CircuitType F (CurvePoint a b F) (CurvePoint a b (FVar F)) :=
  CircuitType.ofEquiv CurvePoint.equivPoint CurvePoint.equivPoint

end Snarky.Kimchi
