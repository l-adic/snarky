import Mathlib.Data.ZMod.Basic
import CompElliptic.CurveForms.ShortWeierstrass
import Lean.Data.Json

/-!
# JSON decoders for proof-systems fixtures

The shared vocabulary of the fixture and vector files under `formal/fixtures` (produced by
`tools/fixture-dump`), consumed by the `scripts/check_*` drivers: field elements are
canonical decimal strings, affine points are two-element coordinate arrays, and `(0, 0)` is
the identity sentinel where a decoder admits it. Decoders compose over a supplied
element parser, so a driver fixes its fields once (`parseZMod` at the concrete cardinality)
and builds the rest from these.
-/

namespace Kimchi.Fixture

open Lean

/-- A decimal string as a natural number. -/
def parseNat (j : Json) : Except String ℕ := do
  let s ← j.getStr?
  match s.toNat? with
  | some n => .ok n
  | none => .error s!"not a decimal natural: {s.take 40}"

/-- A decimal string as an element of `ZMod n` (the canonical value, reduced mod `n`). -/
def parseZMod {n : ℕ} (j : Json) : Except String (ZMod n) := do
  return ((← parseNat j) : ZMod n)

/-- An array, elementwise through `f`. -/
def parseArrOf {α : Type} (f : Json → Except String α) (j : Json) :
    Except String (Array α) := do
  (← j.getArr?).mapM f

/-- A two-element array as a pair, both components through `f`. -/
def parsePair {α : Type} (f : Json → Except String α) (j : Json) :
    Except String (α × α) := do
  let a ← j.getArr?
  unless a.size = 2 do throw "expected a two-element array"
  return (← f a[0]!, ← f a[1]!)

/-- A `[x, y]` coordinate pair, uninspected. -/
def parsePoint {F : Type} (f : Json → Except String F) (j : Json) :
    Except String (F × F) :=
  parsePair f j

open CompElliptic.CurveForms.ShortWeierstrass in
/-- A `[x, y]` coordinate pair validated on the curve `y² = x³ + a·x + b` — or the `(0, 0)`
identity sentinel (`Valid`, decided disjunct-wise: `Valid` itself carries no `Decidable`
instance). -/
def parsePointOnCurve {F : Type} [Field F] [DecidableEq F]
    (f : Json → Except String F) (a b : F) (j : Json) : Except String (F × F) := do
  let p ← parsePair f j
  unless decide (OnCurve a b p) || decide (p = ((0 : F), (0 : F))) do
    throw "point not on the curve"
  return p

end Kimchi.Fixture
