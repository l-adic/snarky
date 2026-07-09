import Kimchi.Verifier.Ipa
import Kimchi.Fixture.Parse
import Lean.Data.Json

/-!
# IPA fixture ingestion — the unified chunked schema

Decoders for the IPA wire-format fixtures (`tools/fixture-dump`'s `ipa_dump`), shared by
the fixture scripts. Chunking is the general case: every commitment is an array of chunk
points and every evaluation a chunk list — `nc = 1` is the one-element instance of the
same schema, exactly as `PolyComm` is always a chunk vector in proof-systems. The
fixtures also record the production-combined commitment and value per polynomial, so a
script can adjudicate the chunk layer's recombination formulas
(`Kimchi/Commitment/IPA/Chunk.lean`) against production output; the recombinators here
(`recombinePoint`/`recombineScalar`) are those formulas, executably.
-/

namespace Kimchi.Fixture.Ipa

open Lean Kimchi.Fixture Kimchi.Commitment.IPA Kimchi.Verifier
open CompElliptic.CurveForms.ShortWeierstrass

def parsePt (C : Ipa.CommitmentCurve) : Json → Except String C.Point :=
  parseSWPoint (parseZMod (n := C.base)) C.E

/-- The fixture's `srs_g`/`srs_h` as a library SRS. The abstract randomisation base `U`
is transcript-derived by the verifier and never read; it is filled with `0`. -/
def parseSRS (C : Ipa.CommitmentCurve) (j : Json) : Except String (SRS C.Point) := do
  let g ← parseArrOf (parsePt C) (← j.getObjVal? "srs_g")
  let k ← (← j.getObjVal? "k").getNat?
  if h : g.size = 2 ^ k then
    return { k := k
             g := fun i => g[i.val]'(by have := i.isLt; omega)
             h := ← parsePt C (← j.getObjVal? "srs_h")
             U := 0 }
  else throw s!"srs_g size {g.size} ≠ 2 ^ {k}"

/-- One parsed fixture: the chunked wire view (chunk points and chunk evaluations per
polynomial), the production-combined view, and the opening proof. -/
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
           proof := { lr := ← parseArrOf (parsePair (parsePt C)) (← fld "lr")
                      delta := ← parsePt C (← fld "delta")
                      z1 := ← parseS (← fld "z1")
                      z2 := ← parseS (← fld "z2")
                      sg := ← parsePt C (← fld "sg") } }

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

end Kimchi.Fixture.Ipa
