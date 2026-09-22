import Bulletproof.Wire
import FixtureKit.Parse
import Lean.Data.Json

/-!
# IPA fixture ingestion

Decoders for the IPA wire-format fixtures that `tools/fixture-dump/src/bin/ipa_dump.rs`
writes, and executable combiners the fixture scripts check against the recorded production
values. Every commitment is an array of chunk points and every evaluation a chunk list; one
chunk is the one-element case of the same schema.

The two fixture kinds are the two ways production folds chunks:

* Combine-then-open (`Raw`): each polynomial's chunks are combined at `x ^ (2 ^ k)` and the
  combined polynomial is opened. The fixture records the combined commitments and values, and
  `recombinePoint`/`recombineScalar` recompute them from the chunks.
* Chunked batch (`RawBatch`): every chunk enters the batch as its own segment,
  polynomial-outer and chunk-inner, one consecutive polyscale power per segment. The fixture
  records the flat combination targets, `segmentCombinePoint`/`segmentCombineScalar`
  recompute them, and `RawBatch.toFlatInput` hands the segments to the wire verifier as a
  flat batch.
-/

namespace Bulletproof.Fixture

open FixtureKit

open Lean FixtureKit Bulletproof Bulletproof
open CompElliptic.CurveForms.ShortWeierstrass

/-- A JSON point of `C`, its coordinates decoded as base-field elements. -/
def parsePt (C : Ipa.KimchiCurve) : Json → Except String C.Point :=
  parseSWPoint (parseZMod (n := C.base)) C.E

/-- An arkworks-compressed point from its `x` coordinate and flag byte: `0x40` is the
identity; otherwise `y` is the square root of `x³ + A·x + B` above `(p-1)/2` under flag
`0x80` and the one below under any other flag. -/
def pointOfCompressed (C : Ipa.KimchiCurve) (sqrt : C.BaseField → Option C.BaseField)
    (x : ℕ) (flag : ℕ) : Except String C.Point := do
  if flag = 0x40 then return ← swPointOfCoords C.E (0, 0)
  let x : C.BaseField := x
  let some y0 := sqrt (x * x * x + C.E.A * x + C.E.B)
    | throw "compressed point: x is not on the curve"
  let big : C.BaseField → Bool := fun y => decide ((C.base - 1) / 2 < y.val)
  let y := if (flag = 0x80) = big y0 then y0 else -y0
  swPointOfCoords C.E (x, y)

/-- The fixture's generators and blinding base as an `SRS` with `k` rounds, failing unless
there are `2 ^ k` generators. The verifier derives `U` from the transcript and never reads
this one, so it is `0`. -/
def parseSRSAt (C : Ipa.KimchiCurve) (k : ℕ) (j : Json) :
    Except String (SRS C.Point) := do
  let g ← parseArrOf (parsePt C) (← j.getObjVal? "srs_g")
  if h : g.size = 2 ^ k then
    return { k := k
             g := fun i => g[i.val]'(by have := i.isLt; omega)
             h := ← parsePt C (← j.getObjVal? "srs_h")
             U := 0 }
  else throw s!"srs_g size {g.size} ≠ 2 ^ {k}"

/-- `parseSRSAt` at the fixture's own `k` field. -/
def parseSRS (C : Ipa.KimchiCurve) (j : Json) : Except String (SRS C.Point) := do
  parseSRSAt C (← (← j.getObjVal? "k").getNat?) j

/-- The fixture's opening proof. -/
def parseProof (C : Ipa.KimchiCurve) (j : Json) :
    Except String (Ipa.Wire.Proof C) := do
  let parseS : Json → Except String C.ScalarField := parseZMod
  let fld (k : String) : Except String Json := j.getObjVal? k
  return { lr := ← parseArrOf (parsePair (parsePt C)) (← fld "lr")
           delta := ← parsePt C (← fld "delta")
           z1 := ← parseS (← fld "z1")
           z2 := ← parseS (← fld "z2")
           sg := ← parsePt C (← fld "sg") }

/-- A combine-then-open fixture: the chunks, their production combination, and the
opening proof of the combined polynomials. -/
structure Raw (C : Ipa.KimchiCurve) where
  /-- The chunk points per polynomial. -/
  chunkComms : Array (Array C.Point)
  /-- The production-combined commitment per polynomial. -/
  combinedComms : Array C.Point
  /-- The evaluation points. -/
  xs : Array C.ScalarField
  /-- The claimed evaluations per chunk, `[poly][point][chunk]`. -/
  chunkEvals : Array (Array (Array C.ScalarField))
  /-- The production-combined claimed evaluations, `[poly][point]`. -/
  evals : Array (Array C.ScalarField)
  /-- The polynomial-combination scalar `ξ`. -/
  polyscale : C.ScalarField
  /-- The evaluation-point-combination scalar `r`. -/
  evalscale : C.ScalarField
  /-- The opening proof. -/
  proof : Ipa.Wire.Proof C

/-- A combine-then-open fixture, failing unless its recorded curve is `curveName`. -/
def parseRaw (C : Ipa.KimchiCurve) (curveName : String) (j : Json) :
    Except String (Raw C) := do
  let parseS : Json → Except String C.ScalarField := parseZMod
  let fld (k : String) : Except String Json := j.getObjVal? k
  let curve ← (← fld "curve").getStr?
  unless curve = curveName do throw s!"unexpected curve: {curve}"
  return { chunkComms := ← parseArrOf (parseArrOf (parsePt C)) (← fld "commitments")
           combinedComms := ← parseArrOf (parsePt C) (← fld "combined_commitments")
           xs := ← parseArrOf parseS (← fld "xs")
           chunkEvals := ← parseArrOf (parseArrOf (parseArrOf parseS))
             (← fld "chunk_evals")
           evals := ← parseArrOf (parseArrOf parseS) (← fld "evals")
           polyscale := ← parseS (← fld "polyscale")
           evalscale := ← parseS (← fld "evalscale")
           proof := ← parseProof C j }

/-- The chunk points recombined, `∑ i, yⁱ • Pᵢ`; the identity at one chunk. -/
def recombinePoint (C : Ipa.KimchiCurve) (y : C.ScalarField)
    (chunks : Array C.Point) : C.Point :=
  Ipa.msm C (fun i : Fin chunks.size => chunks.getD i 0) (fun i => y ^ (i : ℕ))

/-- The chunk evaluations recombined, `∑ i, yⁱ · eᵢ`; the identity at one chunk. -/
def recombineScalar (C : Ipa.KimchiCurve) (y : C.ScalarField)
    (chunks : Array C.ScalarField) : C.ScalarField :=
  (List.range chunks.size).foldr (fun i acc => y ^ i * chunks.getD i 0 + acc) 0

/-- The combined commitments and evaluations as the wire verifier's input. -/
def Raw.toInput {C : Ipa.KimchiCurve} (raw : Raw C) : Ipa.Wire.Input C :=
  { commitments := raw.combinedComms
    xs := raw.xs
    evals := raw.evals
    polyscale := raw.polyscale
    evalscale := raw.evalscale
    proof := raw.proof }

/-- A chunked-batch fixture: the chunks, the production flat combination targets, and the
opening proof. -/
structure RawBatch (C : Ipa.KimchiCurve) where
  /-- The chunk points per polynomial, each chunk one segment. -/
  chunkComms : Array (Array C.Point)
  /-- The evaluation points. -/
  xs : Array C.ScalarField
  /-- The claimed evaluations per chunk, `[poly][point][chunk]`. -/
  chunkEvals : Array (Array (Array C.ScalarField))
  /-- The polynomial-combination scalar `ξ`, one consecutive power per segment. -/
  polyscale : C.ScalarField
  /-- The evaluation-point-combination scalar `r`. -/
  evalscale : C.ScalarField
  /-- The production combined inner product, the flat scalar-side target. -/
  cip : C.ScalarField
  /-- The production combined commitment, the flat group-side target. -/
  batchCombined : C.Point
  /-- The opening proof. -/
  proof : Ipa.Wire.Proof C

/-- A chunked-batch fixture, failing unless its recorded curve is `curveName`. -/
def parseRawBatch (C : Ipa.KimchiCurve) (curveName : String) (j : Json) :
    Except String (RawBatch C) := do
  let parseS : Json → Except String C.ScalarField := parseZMod
  let fld (k : String) : Except String Json := j.getObjVal? k
  let curve ← (← fld "curve").getStr?
  unless curve = curveName do throw s!"unexpected curve: {curve}"
  return { chunkComms := ← parseArrOf (parseArrOf (parsePt C)) (← fld "commitments")
           xs := ← parseArrOf parseS (← fld "xs")
           chunkEvals := ← parseArrOf (parseArrOf (parseArrOf parseS))
             (← fld "chunk_evals")
           polyscale := ← parseS (← fld "polyscale")
           evalscale := ← parseS (← fld "evalscale")
           cip := ← parseS (← fld "combined_inner_product")
           batchCombined := ← parsePt C (← fld "batch_combined_commitment")
           proof := ← parseProof C j }

/-- The segments' commitment combination: polynomial-outer, chunk-inner, one consecutive
`ξ` power per segment. -/
def segmentCombinePoint (C : Ipa.KimchiCurve) (ξ : C.ScalarField)
    (comms : Array (Array C.Point)) : C.Point :=
  (comms.foldl (fun acc chunks =>
      chunks.foldl (fun (a : C.Point × C.ScalarField) P => (a.1 + a.2.val • P, a.2 * ξ))
        acc)
    ((0 : C.Point), (1 : C.ScalarField))).1

/-- The segments' combined inner product: segment `(i, c)` contributes its values combined
over the points by powers of `r`, at the segment's `ξ` power. `evals` is `[poly][point][chunk]`. -/
def segmentCombineScalar (C : Ipa.KimchiCurve) (ξ r : C.ScalarField)
    (evals : Array (Array (Array C.ScalarField))) : C.ScalarField :=
  (evals.foldl (fun (acc : C.ScalarField × C.ScalarField) perPoint =>
      (List.range (perPoint.getD 0 #[]).size).foldl (fun a c =>
        let term := (List.range perPoint.size).foldr
          (fun j t => r ^ j * (perPoint.getD j #[]).getD c 0 + t) 0
        (a.1 + a.2 * term, a.2 * ξ)) acc)
    (0, 1)).1

/-- The segments as a flat batch, every chunk its own claim row. The production opening of
the chunked batch opens this flat batch, so the wire verifier accepting it checks the
segment layout. -/
def RawBatch.toFlatInput {C : Ipa.KimchiCurve} (raw : RawBatch C) :
    Ipa.Wire.Input C :=
  { commitments := raw.chunkComms.flatMap id
    xs := raw.xs
    evals := raw.chunkEvals.flatMap (fun perPoint =>
      (Array.range (perPoint.getD 0 #[]).size).map
        (fun c => perPoint.map (fun ch => ch.getD c 0)))
    polyscale := raw.polyscale
    evalscale := raw.evalscale
    proof := raw.proof }

/-! ## The Lagrange basis

A kimchi key's Lagrange-basis commitments are not wire data: `Ipa.lagrangeBasis` computes them
from the SRS the proof was made against (`Bulletproof.Fixture.SRSLoader.loadSRS`). -/

/-- A point as the fixtures' `[x, y]` decimal pair. -/
private def pointJson {C : Ipa.KimchiCurve} (p : C.Point) : Json :=
  Json.arr #[Json.str (toString p.x.val), Json.str (toString p.y.val)]

/-- One memoised commitment, failing unless it has `nc` chunks. -/
private def parseChunks (C : Ipa.KimchiCurve) (nc : ℕ) (j : Json) :
    Except String (Vector C.Point nc) := do
  let pts ← parseArrOf (parsePt C) j
  if h : pts.size = nc then return ⟨pts, h⟩
  else throw s!"a memoised commitment of {pts.size} chunks, expected {nc}"

/-- `Ipa.lagrangeBasis` memoised at `path`: read back when the file holds at least `count`
commitments of `nc` chunks, computed and written otherwise. The path must name the curve, the
domain and the SRS size, which fix the basis. -/
def lagrangeBasisCached (C : Ipa.KimchiCurve) (path : System.FilePath) (σ : SRS C.Point)
    (nc n : ℕ) (ω : C.ScalarField) (count : ℕ) : IO (Array (Vector C.Point nc)) := do
  if ← path.pathExists then
    if let .ok pts := Json.parse (← IO.FS.readFile path) >>= parseArrOf (parseChunks C nc) then
      if count ≤ pts.size then return pts.extract 0 count
  let pts := Ipa.lagrangeBasis C σ nc n ω count
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path
    (Json.arr (pts.map fun v => Json.arr (v.toArray.map pointJson))).compress
  return pts

end Bulletproof.Fixture
