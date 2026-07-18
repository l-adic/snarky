import Bulletproof.Wire
import FixtureKit.Parse
import Lean.Data.Json

/-!
# IPA fixture ingestion — the unified chunked schema

Decoders for the IPA wire-format fixtures (`tools/fixture-dump`'s `ipa_dump`), shared by
the fixture scripts. Chunking is the general case: every commitment is an array of chunk
points and every evaluation a chunk list — a single chunk is the one-element instance of the
same schema, exactly as `PolyComm` is always a chunk vector in proof-systems.

Two fixture kinds, one per production chunk-fold mechanism:

* **Combine-then-open** (`Raw`, mechanism (a)): per polynomial, the chunk points are
  combined by `chunk_commitment(x^(2^k))` and the combined polynomial is opened. The
  fixture records the production-combined commitment and value per polynomial, so a
  script can adjudicate the chunk layer's recombination formulas
  (`Chunk.lean`) against production output; the recombinators here
  (`recombinePoint`/`recombineScalar`) are those formulas, executably.
* **Chunked batch** (`RawBatch`, mechanism (b)): the multi-chunk `PolyComm`s enter the
  batch as-is — each chunk one segment, polynomial-outer, chunk-inner, one consecutive
  polyscale power per segment. The fixture records the production flat combination
  targets (`combine_commitments` at `rand_base = 1`, `combined_inner_product`); the
  combiners here (`segmentCombinePoint`/`segmentCombineScalar`) are the chunked-batch
  combiners of `Batch.lean`, executably, and `toFlatInput` is the
  flattening lemma as data — the segment stream presented to the wire verifier.
-/

namespace Bulletproof.Fixture

open FixtureKit

open Lean FixtureKit Bulletproof Bulletproof
open CompElliptic.CurveForms.ShortWeierstrass

def parsePt (C : Ipa.CommitmentCurve) : Json → Except String C.Point :=
  parseSWPoint (parseZMod (n := C.base)) C.E

/-- The fixture's `srs_g`/`srs_h` as a library SRS at a given round count `k` (the
IPA fixtures carry `k` directly; the kimchi-proof fixture derives it from the domain
size — see `parseSRS`). The abstract randomisation base `U` is transcript-derived by
the verifier and never read; it is filled with `0`. -/
def parseSRSAt (C : Ipa.CommitmentCurve) (k : ℕ) (j : Json) :
    Except String (SRS C.Point) := do
  let g ← parseArrOf (parsePt C) (← j.getObjVal? "srs_g")
  if h : g.size = 2 ^ k then
    return { k := k
             g := fun i => g[i.val]'(by have := i.isLt; omega)
             h := ← parsePt C (← j.getObjVal? "srs_h")
             U := 0 }
  else throw s!"srs_g size {g.size} ≠ 2 ^ {k}"

/-- `parseSRSAt` at the fixture's own `k` field. -/
def parseSRS (C : Ipa.CommitmentCurve) (j : Json) : Except String (SRS C.Point) := do
  parseSRSAt C (← (← j.getObjVal? "k").getNat?) j

def parseProof (C : Ipa.CommitmentCurve) (j : Json) : Except String (Ipa.Proof C) := do
  let parseS : Json → Except String C.ScalarField := parseZMod
  let fld (k : String) : Except String Json := j.getObjVal? k
  return { lr := ← parseArrOf (parsePair (parsePt C)) (← fld "lr")
           delta := ← parsePt C (← fld "delta")
           z1 := ← parseS (← fld "z1")
           z2 := ← parseS (← fld "z2")
           sg := ← parsePt C (← fld "sg") }

/-- One parsed combine-then-open fixture: the chunked wire view (chunk points and chunk
evaluations per polynomial), the production-combined view, and the opening proof. -/
structure Raw (C : Ipa.CommitmentCurve) where
  chunkComms : Array (Array C.Point)
  combinedComms : Array C.Point
  xs : Array C.ScalarField
  chunkEvals : Array (Array (Array C.ScalarField))
  evals : Array (Array C.ScalarField)
  polyscale : C.ScalarField
  evalscale : C.ScalarField
  proof : Ipa.Proof C

def parseRaw (C : Ipa.CommitmentCurve) (curveName : String) (j : Json) :
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

/-- Commitment recombination, executably: `∑ i, yⁱ • Pᵢ` — `commit_combine`'s
group-side formula. The identity at one chunk. -/
def recombinePoint (C : Ipa.CommitmentCurve) (y : C.ScalarField)
    (chunks : Array C.Point) : C.Point :=
  Ipa.msm C (fun i : Fin chunks.size => chunks.getD i 0) (fun i => y ^ (i : ℕ))

/-- Evaluation recombination, executably: `∑ i, yⁱ · eᵢ` — `eval_eq_sum_chunkPoly`'s
formula. The identity at one chunk. -/
def recombineScalar (C : Ipa.CommitmentCurve) (y : C.ScalarField)
    (chunks : Array C.ScalarField) : C.ScalarField :=
  (List.range chunks.size).foldr (fun i acc => y ^ i * chunks.getD i 0 + acc) 0

/-- The combined view as the executable verifier's input. -/
def Raw.toInput {C : Ipa.CommitmentCurve} (raw : Raw C) : Ipa.Input C :=
  { commitments := raw.combinedComms
    xs := raw.xs
    evals := raw.evals
    polyscale := raw.polyscale
    evalscale := raw.evalscale
    proof := raw.proof }

/-- One parsed chunked-batch fixture: the chunked wire view, the production flat
combination targets (`combine_commitments` at `rand_base = 1`, `combined_inner_product`),
and the opening proof. -/
structure RawBatch (C : Ipa.CommitmentCurve) where
  chunkComms : Array (Array C.Point)
  xs : Array C.ScalarField
  chunkEvals : Array (Array (Array C.ScalarField))
  polyscale : C.ScalarField
  evalscale : C.ScalarField
  cip : C.ScalarField
  batchCombined : C.Point
  proof : Ipa.Proof C

def parseRawBatch (C : Ipa.CommitmentCurve) (curveName : String) (j : Json) :
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

/-- The chunked batch's segment-stream commitment combination (`combine_commitments` at
`rand_base = 1`), executably: polynomial-outer, chunk-inner, one consecutive `ξ` power
per segment — `chunkedCombinedCommitment`'s formula. -/
def segmentCombinePoint (C : Ipa.CommitmentCurve) (ξ : C.ScalarField)
    (comms : Array (Array C.Point)) : C.Point :=
  (comms.foldl (fun acc chunks =>
      chunks.foldl (fun (a : C.Point × C.ScalarField) P => (a.1 + a.2.val • P, a.2 * ξ))
        acc)
    ((0 : C.Point), (1 : C.ScalarField))).1

/-- The chunked combined inner product (`combined_inner_product`), executably: segment
`(i, c)` contributes its evalscale-combined point values at the segment's `ξ` power —
`chunkedCombinedInnerProduct`'s formula. `evals` is `[poly][point][chunk]`. -/
def segmentCombineScalar (C : Ipa.CommitmentCurve) (ξ r : C.ScalarField)
    (evals : Array (Array (Array C.ScalarField))) : C.ScalarField :=
  (evals.foldl (fun (acc : C.ScalarField × C.ScalarField) perPoint =>
      (List.range (perPoint.getD 0 #[]).size).foldl (fun a c =>
        let term := (List.range perPoint.size).foldr
          (fun j t => r ^ j * (perPoint.getD j #[]).getD c 0 + t) 0
        (a.1 + a.2 * term, a.2 * ξ)) acc)
    (0, 1)).1

/-- The flattened segment view — every chunk as its own claim row, the flattening lemmas
(`chunkedCombined*_eq_flat`) as data. The production opening of a chunked batch IS the
opening of this flat batch, so the executable verifier adjudicates the whole
segment layout by accepting it. -/
def RawBatch.toFlatInput {C : Ipa.CommitmentCurve} (raw : RawBatch C) : Ipa.Input C :=
  { commitments := raw.chunkComms.flatMap id
    xs := raw.xs
    evals := raw.chunkEvals.flatMap (fun perPoint =>
      (Array.range (perPoint.getD 0 #[]).size).map
        (fun c => perPoint.map (fun ch => ch.getD c 0)))
    polyscale := raw.polyscale
    evalscale := raw.evalscale
    proof := raw.proof }

end Bulletproof.Fixture
