import Bulletproof.Wire

/-!
# The SRS files, loaded

`loadSRS` reads a proof-systems `.srs` file (`srs-cache/{vesta,pallas}.srs`, the SRS the
PureScript suite proves against) into a library `SRS`. It is the one entry point; the
file format is an implementation detail of this module — MessagePack `[g, h]`, `g` an
`array32` of `bin8` 33-byte arkworks-compressed points, `h` one more — so that the reader
can be replaced without touching its callers.
-/

namespace Bulletproof.Fixture.SRSLoader

open CompElliptic.CurveForms.ShortWeierstrass

/-- A point from its coordinates: on the curve, or the `(0, 0)` identity sentinel. -/
private def pointOfCoords (C : Ipa.KimchiCurve) (x y : C.BaseField) :
    Except String C.Point :=
  if h : OnCurve C.E.A C.E.B (x, y) then return ⟨x, y, Or.inl h⟩
  else if h0 : (x, y) = ((0 : C.BaseField), (0 : C.BaseField)) then return ⟨x, y, Or.inr h0⟩
  else throw "point not on the curve"

/-- A compressed point (arkworks' `serialize_compressed`): the `x` coordinate and a flag.
`sqrt` is the base field's square root; the flag picks the root — `0x80` the one above
`(p-1)/2`, `0x00` the one below — and `0x40` is the identity. -/
private def pointOfCompressed (C : Ipa.KimchiCurve) (sqrt : C.BaseField → Option C.BaseField)
    (x : ℕ) (flag : ℕ) : Except String C.Point := do
  if flag = 0x40 then return ← pointOfCoords C 0 0
  let x : C.BaseField := x
  let some y0 := sqrt (x * x * x + C.E.A * x + C.E.B)
    | throw "compressed point: x is not on the curve"
  let big : C.BaseField → Bool := fun y => decide ((C.base - 1) / 2 < y.val)
  let y := if (flag = 0x80) = big y0 then y0 else -y0
  pointOfCoords C x y

/-- The file's first `2^k` generators and its blinding base. -/
private def srsOfBytes (C : Ipa.KimchiCurve) (sqrt : C.BaseField → Option C.BaseField)
    (k : ℕ) (b : ByteArray) : Except String (SRS C.Point) := do
  let byte (i : ℕ) : ℕ := if h : i < b.size then (b[i]).toNat else 0
  unless 6 ≤ b.size ∧ byte 0 = 0x92 ∧ byte 1 = 0xdd do
    throw "expected a two-element array headed by an array32 of generators"
  let count := (byte 2 <<< 24) + (byte 3 <<< 16) + (byte 4 <<< 8) + byte 5
  unless 2 ^ k ≤ count do throw s!"{count} generators, need 2^{k}"
  unless 6 + 35 * count + 35 ≤ b.size do throw "truncated"
  let point (off : ℕ) : Except String C.Point := do
    unless byte off = 0xc4 ∧ byte (off + 1) = 0x21 do throw "expected a 33-byte point"
    let x := (List.range 32).foldr (fun i acc => acc * 256 + byte (off + 2 + i)) 0
    pointOfCompressed C sqrt x (byte (off + 34))
  let g ← (Array.range (2 ^ k)).mapM fun i => point (6 + 35 * i)
  if h : g.size = 2 ^ k then
    return { k, g := fun i => g[i.val]'(by have := i.isLt; omega)
             h := ← point (6 + 35 * count), U := 0 }
  else throw "generator count"

/-- The SRS at `path`, cut to its first `2^k` generators — the SRS a `k`-round proof of
the curve was made against, as the generators are fixed by index. `sqrt` is the base
field's square root (the points are stored compressed). `U` is transcript-derived and
never read; it is filled with `0`. -/
def loadSRS (C : Ipa.KimchiCurve) (sqrt : C.BaseField → Option C.BaseField) (k : ℕ)
    (path : System.FilePath) : IO (SRS C.Point) := do
  match srsOfBytes C sqrt k (← IO.FS.readBinFile path) with
  | .ok σ => return σ
  | .error e => throw (IO.userError s!"{path}: srs file: {e}")

end Bulletproof.Fixture.SRSLoader
