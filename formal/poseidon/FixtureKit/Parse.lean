import Mathlib.Data.ZMod.Basic
import CompElliptic.CurveForms.ShortWeierstrass
import Lean.Data.Json

/-!
# JSON decoders for proof-systems fixtures

The shared vocabulary of the fixture and vector files in each package's `fixtures/`
directory, produced by `tools/fixture-dump` and consumed by each package's check drivers.
Field elements are canonical decimal strings, affine points are two-element coordinate
arrays, and `(0, 0)` is the identity sentinel where a decoder admits it.

Decoders compose over a supplied element parser, so a driver fixes its fields once
(`parseZMod` at the concrete cardinality) and builds the rest from these.
-/

namespace FixtureKit

open Lean

/-- A decimal string as a natural number. -/
def parseNat (j : Json) : Except String ℕ := do
  let s ← j.getStr?
  match s.toNat? with
  | some n => .ok n
  | none => .error s!"not a decimal natural: {s.take 40}"

/- Decoders built on these read the keys they need and drop the rest: an unknown key is
ignored, not rejected. The drivers consume `fixture-dump` output, which carries none. -/

/-- A decimal string as an element of `ZMod n`, *rejecting* non-canonical numerals (`≥ n`).
This matches the upstream deserializer, which errors on an out-of-range field element
rather than reducing it. At `n = 0` every numeral is rejected. -/
def parseZMod {n : ℕ} (j : Json) : Except String (ZMod n) := do
  let v ← parseNat j
  if v < n then return (v : ZMod n)
  else throw s!"numeral {v} out of canonical range for ZMod {n}"

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

open CompElliptic.CurveForms.ShortWeierstrass in
/-- A coordinate pair as a point on `E`: on the curve or the `(0, 0)` identity sentinel,
with the validity proof carried in the point (decided disjunct-wise). -/
def swPointOfCoords {F : Type} [Field F] [DecidableEq F] (E : SWCurve F) (p : F × F) :
    Except String (SWPoint E) :=
  if h : OnCurve E.A E.B p then return ⟨p.1, p.2, Or.inl h⟩
  else if h0 : p = ((0 : F), (0 : F)) then return ⟨p.1, p.2, Or.inr h0⟩
  else throw "point not on the curve"

open CompElliptic.CurveForms.ShortWeierstrass in
/-- A `[x, y]` coordinate pair as a point on `E` (`swPointOfCoords`). -/
def parseSWPoint {F : Type} [Field F] [DecidableEq F] (f : Json → Except String F)
    (E : SWCurve F) (j : Json) : Except String (SWPoint E) := do
  swPointOfCoords E (← parsePair f j)

end FixtureKit
