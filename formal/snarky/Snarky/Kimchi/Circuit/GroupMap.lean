import Snarky.Circuit.DSL.Field
import Snarky.Circuit.DSL.Assert
import Snarky.Circuit.DSL.Boolean
import Snarky.Kimchi.Constraint

/-!
# The BW19 hash-to-curve gadget

Port of `Snarky.Circuit.Kimchi.GroupMap`
(packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/GroupMap.purs; mina
`group_map/bw19.ml`; Wahby–Boneh 2019, https://eprint.iacr.org/2019/403): map a
field element onto a curve `y² = x³ + b`. Three candidate abscissae are computed
from the `setup()` parameters; per candidate, `sqrtFlagged` witnesses a
residuosity flag and a root of either the candidate ordinate square or its
non-residue twist; at least one flag is asserted set, and the point is the
first-flagged candidate, selected by mutually exclusive boolean products.

The value level (`potentialXs`, `groupMap`) is the same map the poseidon package's
fixture-validated `Poseidon.GroupMap` computes at the deployed Pasta fields; the
laws here stay generic and quote the module's own pure model, PS-parity.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- PS `groupMapParams` builds the parameter record from the `HasBW19` FFI and a
  non-residue search; the port takes `GroupMapParams` as data — the deployed
  values live with their curves (the poseidon package's `setup()` constants).
- PS's advice consults the `HasSqrt` class; the port threads an explicit
  `sqrtF : F → Option F` — like `endoInv`'s advice parameters, soundness never
  consults it, and completeness states the coherence it needs.
- PS's advice throws on an impossible root (`unsafeThrow`); the port is total
  (`Option.getD 0`, the pure map falling back to `(0, 0)`) — unreachable for
  honest inputs, where a flagged candidate always has its root.
-/

namespace Snarky.Kimchi

open Snarky Std.Do

variable {F c : Type}

/-- The BW19 `setup()` parameters (PS `GroupMapParams`): the seed `u`, its curve
image `f(u) = u³ + b`, the square-root and inverse constants, the curve constant,
and a known quadratic non-residue for the flagged-root trick. -/
structure GroupMapParams (F : Type) where
  /-- The SvdW seed `u`. -/
  u : F
  /-- `f(u) = u³ + b`. -/
  fu : F
  /-- `(√(-3u²) − u) / 2`. -/
  sqrtNeg3U2MinusUOver2 : F
  /-- `√(-3u²)`. -/
  sqrtNeg3U2 : F
  /-- `(3u²)⁻¹`. -/
  inv3U2 : F
  /-- The curve constant `b` of `y² = x³ + b`. -/
  b : F
  /-- A known quadratic non-residue. -/
  nonResidue : F

/-- The three candidate abscissae (PS `potentialXs`): one of them is the abscissa
of a curve point — Shallue–van de Woestijne's theorem, which the laws take as a
hypothesis rather than prove. Division is the field's total one (`0⁻¹ = 0`),
matching the gadget's `div`. -/
def potentialXs [Field F] (params : GroupMapParams F) (t : F) : F × F × F :=
  let t2 := t * t
  let alphaInv := (t2 + params.fu) * t2
  let alpha := 1 / alphaInv
  let t4 := t2 * t2
  let x1 := params.sqrtNeg3U2MinusUOver2 - t4 * alpha * params.sqrtNeg3U2
  let x2 := -params.u - x1
  let t2PlusFu := t2 + params.fu
  let t2Inv := alpha * t2PlusFu
  let x3 := params.u - (t2PlusFu * t2PlusFu) * t2Inv * params.inv3U2
  (x1, x2, x3)

/-- The pure map (PS `groupMap`): the first candidate whose ordinate square has a
root under `sqrtF`, as a coordinate pair. The no-candidate branch returns `(0, 0)`
(PS throws) — unreachable when some candidate is a square and `sqrtF` is total on
squares. -/
def groupMapPure [Field F] (sqrtF : F → Option F) (params : GroupMapParams F)
    (t : F) : F × F :=
  let ySquared := fun x => x * x * x + params.b
  let (x1, x2, x3) := potentialXs params t
  match sqrtF (ySquared x1) with
  | some y => (x1, y)
  | none =>
    match sqrtF (ySquared x2) with
    | some y => (x2, y)
    | none =>
      match sqrtF (ySquared x3) with
      | some y => (x3, y)
      | none => (0, 0)

/-- The residuosity flag's advice: whether `sqrtF` finds a root. -/
private def isQRWit [Field F] (sqrtF : F → Option F) (x : FVar F) :
    AsProver F Bool := do
  let v ← AsProver.readCVar x
  pure (sqrtF v).isSome

/-- The root's advice: `sqrtF`'s root of the selected operand (`0` when there is
none — unreachable honestly). -/
private def sqrtWit [Field F] (sqrtF : F → Option F) (x : FVar F) :
    AsProver F F := do
  let v ← AsProver.readCVar x
  pure ((sqrtF v).getD 0)

/-- In-circuit square root with a residuosity flag (PS `sqrtFlagged`): witness the
flag, select the operand or its non-residue twist, witness a root, and pin it with
one `square` row — `y² = if isQR then x else nonResidue·x`. -/
private def sqrtFlagged [Field F] [DecidableEq F] [BasicSystem F c]
    (sqrtF : F → Option F) (nonResidue : F) (x : FVar F) :
    CircuitM F c (FVar F × BoolVar F) := do
  let isQR ← witness (val := Bool) (isQRWit sqrtF x)
  let mX := CVar.scale_ nonResidue x
  let xOrMx ← select isQR x mX
  let sqrtVal ← witness (val := F) (sqrtWit sqrtF xOrMx)
  assertSquare sqrtVal xOrMx
  pure (sqrtVal, isQR)

/-- The in-circuit BW19 map (PS `groupMapCircuit`): the candidate abscissae from
seven `mul`s and one `div`, a flagged root per candidate, at least one flag
asserted set, and the first-flagged candidate selected by mutually exclusive
boolean products. -/
def groupMapCircuit [Field F] [DecidableEq F] [BasicSystem F c]
    (sqrtF : F → Option F) (params : GroupMapParams F) (t : FVar F) :
    CircuitM F c (AffinePoint (FVar F)) := do
  let t2 ← mul t t
  let t2PlusFu := CVar.add_ t2 (.const params.fu)
  let alphaInv ← mul t2PlusFu t2
  let alpha ← div (.const 1) alphaInv
  let t4 ← mul t2 t2
  let t4Alpha ← mul t4 alpha
  let temp1 ← mul t4Alpha (.const params.sqrtNeg3U2)
  let x1 := CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) temp1
  let x2 := CVar.sub_ (.const (-params.u)) x1
  let t2Inv ← mul alpha t2PlusFu
  let t2PlusFuSq ← mul t2PlusFu t2PlusFu
  let temp2a ← mul t2PlusFuSq t2Inv
  let temp2 ← mul temp2a (.const params.inv3U2)
  let x3 := CVar.sub_ (.const params.u) temp2
  let ySquared := fun (x : FVar F) => do
    let xSq ← mul x x
    let xCu ← mul xSq x
    pure (CVar.add_ xCu (.const params.b))
  let y1Sq ← ySquared x1
  let (y1, b1) ← sqrtFlagged sqrtF params.nonResidue y1Sq
  let y2Sq ← ySquared x2
  let (y2, b2) ← sqrtFlagged sqrtF params.nonResidue y2Sq
  let y3Sq ← ySquared x3
  let (y3, b3) ← sqrtFlagged sqrtF params.nonResidue y3Sq
  assertNonZero (CVar.add_ (CVar.add_ (↑b1) (↑b2)) (↑b3))
  let nb1 := Snarky.not b1
  let x2First ← Snarky.and nb1 b2
  let nb2AndB3 ← Snarky.and (Snarky.not b2) b3
  let x3First ← Snarky.and nb1 nb2AndB3
  let t3y ← mul (↑x3First) y3
  let t2y ← mul (↑x2First) y2
  let t1y ← mul (↑b1) y1
  let yResult := CVar.add_ (CVar.add_ t1y t2y) t3y
  let t3x ← mul (↑x3First) x3
  let t2x ← mul (↑x2First) x2
  let t1x ← mul (↑b1) x1
  let xResult := CVar.add_ (CVar.add_ t1x t2x) t3x
  pure ⟨xResult, yResult⟩

end Snarky.Kimchi
