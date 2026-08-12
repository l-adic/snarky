import Snarky.Circuit.DSL.Utils
import Snarky.Kimchi.Constraint

/-!
# The complete-addition gadget

Port of `Snarky.Circuit.Kimchi.AddComplete`
(packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/AddComplete.purs): `addFast` seals
the two operand points, witnesses the gate's seven auxiliary columns in allocation
order (`sameX`, the mode-dependent `inf`, `infZ`, `x21Inv`, `s`, `x3`, `y3` — fixture
bytes), and emits one `KimchiConstraint.addComplete`. `addComplete` is the
`checkFinite` specialization (OCaml `add_fast` with its default).

Name map: `sealPoint`, `Finiteness` (constructors lowerCamel), `addFast`,
`addComplete` keep their names; the result record is `AddResult`; the witness
computations are named (`AddFast.sameXWit`, …) in the manner of the base `Field`
gadgets.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- `AffinePoint`'s `CircuitType`/`CheckedType` instances live here, beside their first
  Lean consumer — the PS home (`Snarky.Data.EllipticCurve`, package snarky-curves) is
  outside this port. The encoding is the PS generic one, `[x, y]`, checks free.
- Labels are not threaded (the base embedding's `labelOp` is inert; PS wraps
  `add_fast`/`seal_point`).

No law is stated here: the gadget-completeness bridge to the verified gate is
deliberately not part of this package.
-/

namespace Snarky.Kimchi

open Snarky

variable {F c : Type}

/-- Point bundles encode coordinatewise, `[x, y]` (the PS generic instance in
`Snarky.Data.EllipticCurve`; see the module docstring). -/
instance : CircuitType F (AffinePoint F) (AffinePoint (FVar F)) where
  size := 2
  valueToFields p := #v[p.x, p.y]
  fieldsToValue fs := ⟨fs[0], fs[1]⟩
  varToFields p := #v[p.x, p.y]
  fieldsToVar fs := ⟨fs[0], fs[1]⟩

/-- A point's coordinates carry no check of their own (PS `genericCheck`). -/
instance : CheckedType F c (AffinePoint (FVar F)) where
  check _ := .pure PUnit.unit

/-- Seal a point coordinatewise, `y` before `x` — OCaml's `seal` maps over the tuple
right to left (PS `sealPoint` preserves the order; emission order is fixture bytes). -/
private def sealPoint [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c]
    (p : AffinePoint (FVar F)) : CircuitM F c (AffinePoint (FVar F)) := do
  let y ← sealVar p.y
  let x ← sealVar p.x
  pure ⟨x, y⟩

/-- The finiteness mode (OCaml `add_fast ?check_finite`): `checkFinite` pins the
infinity flag to the constant `0` with no witness; `dontCheckFinite` witnesses it. -/
inductive Finiteness where
  /-- The sum is asserted finite: `inf` is the constant zero. -/
  | checkFinite
  /-- The sum may be the point at infinity: `inf` is witnessed. -/
  | dontCheckFinite

/-- `addFast`'s result: the output point and the (mode-dependent) infinity flag. -/
structure AddResult (F : Type) where
  /-- The output sum. -/
  p : AffinePoint (FVar F)
  /-- The infinity flag: constant `false` under `checkFinite`, else witnessed. -/
  isInfinity : BoolVar F

namespace AddFast

/-- `sameX`'s witness: whether the operand x-coordinates coincide. Public only for
the gadget laws. -/
private def sameXWit [Add F] [Mul F] [DecidableEq F] (p1 p2 : AffinePoint (FVar F)) :
    AsProver F Bool := do
  let x1 ← AsProver.readCVar p1.x
  let x2 ← AsProver.readCVar p2.x
  pure (decide (x1 = x2))

/-- `inf`'s witness (`dontCheckFinite` mode): same x-coordinates with different
y-coordinates — the inverse-pair test. Public only for the gadget laws. -/
private def infWit [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    (p1 p2 : AffinePoint (FVar F)) (sameX : BoolVar F) : AsProver F Bool := do
  let sx ← readVar (val := Bool) sameX
  let y1 ← AsProver.readCVar p1.y
  let y2 ← AsProver.readCVar p2.y
  pure (sx && !(decide (y1 = y2)))

/-- `infZ`'s witness: `0` on equal y-coordinates, else the inverse of `y₂ − y₁` when
the x-coordinates coincide (pinning the infinity flag), else `0`. Public only for the
gadget laws. -/
private def infZWit [Field F] [DecidableEq F] (p1 p2 : AffinePoint (FVar F))
    (sameX : BoolVar F) : AsProver F F := do
  let y1 ← AsProver.readCVar p1.y
  let y2 ← AsProver.readCVar p2.y
  if y1 = y2 then pure 0
  else do
    let sx ← readVar (val := Bool) sameX
    if sx then pure (y2 - y1)⁻¹ else pure 0

/-- `x21Inv`'s witness: the inverse of `x₂ − x₁` when the x-coordinates differ
(pinning `sameX`), else `0`. Public only for the gadget laws. -/
private def x21InvWit [Field F] [DecidableEq F] (p1 p2 : AffinePoint (FVar F))
    (sameX : BoolVar F) : AsProver F F := do
  let sx ← readVar (val := Bool) sameX
  if sx then pure 0
  else do
    let x1 ← AsProver.readCVar p1.x
    let x2 ← AsProver.readCVar p2.x
    pure (x2 - x1)⁻¹

/-- The slope's witness: tangent `3x₁²/(2y₁)` in the equal-x case, else the secant
`(y₂−y₁)/(x₂−x₁)`. Public only for the gadget laws. -/
private def slopeWit [Field F] [DecidableEq F] (p1 p2 : AffinePoint (FVar F))
    (sameX : BoolVar F) : AsProver F F := do
  let sx ← readVar (val := Bool) sameX
  if sx then do
    let x1 ← AsProver.readCVar p1.x
    let y1 ← AsProver.readCVar p1.y
    pure (3 * x1 * x1 / (2 * y1))
  else do
    let y1 ← AsProver.readCVar p1.y
    let y2 ← AsProver.readCVar p2.y
    let x1 ← AsProver.readCVar p1.x
    let x2 ← AsProver.readCVar p2.x
    pure ((y2 - y1) / (x2 - x1))

/-- `x3`'s witness: `s² − (x₁ + x₂)`. Public only for the gadget laws. -/
private def x3Wit [Add F] [Mul F] [Sub F] (p1 p2 : AffinePoint (FVar F)) (s : FVar F) :
    AsProver F F := do
  let sv ← AsProver.readCVar s
  let x1 ← AsProver.readCVar p1.x
  let x2 ← AsProver.readCVar p2.x
  pure (sv * sv - (x1 + x2))

/-- `y3`'s witness: `s·(x₁ − x₃) − y₁`. Public only for the gadget laws. -/
private def y3Wit [Add F] [Mul F] [Sub F] (p1 : AffinePoint (FVar F)) (s x3 : FVar F) :
    AsProver F F := do
  let sv ← AsProver.readCVar s
  let x1 ← AsProver.readCVar p1.x
  let x3v ← AsProver.readCVar x3
  let y1 ← AsProver.readCVar p1.y
  pure (sv * (x1 - x3v) - y1)

end AddFast

/-- Complete addition with explicit finiteness control (OCaml
`add_fast ~check_finite`): seal both points, witness the gate's auxiliary columns in
allocation order, emit one `addComplete` constraint. -/
def addFast [Field F] [DecidableEq F] (finiteness : Finiteness)
    (p1' p2' : AffinePoint (FVar F)) :
    CircuitM F (KimchiConstraint F) (AddResult F) := do
  let p1 ← sealPoint p1'
  let p2 ← sealPoint p2'
  let sameXU ← witness (val := UnChecked Bool) (.mk <$> AddFast.sameXWit p1 p2)
  let sameX := sameXU.val
  let inf ← match finiteness with
    | .checkFinite => pure false_
    | .dontCheckFinite => do
      let r ← witness (val := UnChecked Bool) (.mk <$> AddFast.infWit p1 p2 sameX)
      pure r.val
  let infZ ← witness (val := F) (AddFast.infZWit p1 p2 sameX)
  let x21Inv ← witness (val := F) (AddFast.x21InvWit p1 p2 sameX)
  let s ← witness (val := F) (AddFast.slopeWit p1 p2 sameX)
  let x3 ← witness (val := F) (AddFast.x3Wit p1 p2 s)
  let y3 ← witness (val := F) (AddFast.y3Wit p1 s x3)
  addConstraint (.addComplete
    { p1 := p1, p2 := p2, p3 := ⟨x3, y3⟩, inf := inf.toCVar,
      sameX := sameX.toCVar, s := s, infZ := infZ, x21Inv := x21Inv })
  pure ⟨⟨x3, y3⟩, inf⟩

/-- Complete addition assuming finite inputs (OCaml `add_fast`'s default mode). -/
def addComplete [Field F] [DecidableEq F] (p1 p2 : AffinePoint (FVar F)) :
    CircuitM F (KimchiConstraint F) (AddResult F) :=
  addFast .checkFinite p1 p2

end Snarky.Kimchi
