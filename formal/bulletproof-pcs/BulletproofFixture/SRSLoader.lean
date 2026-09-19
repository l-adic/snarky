import BulletproofFixture

/-!
# The SRS files, loaded

`loadSRS` reads a proof-systems `.srs` file (`srs-cache/{vesta,pallas}.srs`, the SRS the
PureScript suite proves against) into a library `SRS`. It is the one entry point; the
file format is an implementation detail of this module — MessagePack `[g, h]`, `g` an
`array32` of `bin8` 33-byte arkworks-compressed points (`pointOfCompressed`), `h` one more —
so that the reader can be replaced without touching its callers.
-/

namespace Bulletproof.Fixture.SRSLoader

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
