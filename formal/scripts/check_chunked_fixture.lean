import Kimchi.Verifier.Ipa
import Kimchi.Fixture.Parse
import Lean.Data.Json

/-! Adjudicate the chunk layer's recombination formulas against production kimchi output
(`fixtures/ipa_chunked_{vesta,pallas}.json`, from `tools/fixture-dump`'s `ipa_dump`):
a degree-`< 3·2^k` polynomial committed in 3 chunks, the production
`chunk_commitment(y)` combination at `y = x^(2^k)`, and an `nc = 1` opening of the
combined polynomial. The checks:

* **commitment recombination** (`commit_combine`'s formula): the `y`-power MSM of the
  raw chunk points equals the production combined commitment;
* **eval recombination** (`eval_eq_sum_chunkPoly`'s formula): the `y`-power fold of the
  raw chunk evaluations equals the claimed combined value;
* **the executable verifier accepts** the combined claim (and rejects a corrupted one).
-/

open Lean Kimchi.Fixture Kimchi.Commitment.IPA Kimchi.Verifier
open CompElliptic.CurveForms.ShortWeierstrass

def parsePt (C : Ipa.CommitmentCurve) : Json → Except String C.Point :=
  parseSWPoint (parseZMod (n := C.base)) C.E

def parseSRS (C : Ipa.CommitmentCurve) (j : Json) : Except String (SRS C.Point) := do
  let g ← parseArrOf (parsePt C) (← j.getObjVal? "srs_g")
  let k ← (← j.getObjVal? "k").getNat?
  if h : g.size = 2 ^ k then
    return { k := k
             g := fun i => g[i.val]'(by have := i.isLt; omega)
             h := ← parsePt C (← j.getObjVal? "srs_h")
             U := 0 }
  else throw s!"srs_g size {g.size} ≠ 2 ^ {k}"

def parseInput (C : Ipa.CommitmentCurve) (curveName : String) (j : Json) :
    Except String (Ipa.Input C) := do
  let parseS : Json → Except String C.ScalarField := parseZMod
  let fld (k : String) : Except String Json := j.getObjVal? k
  let curve ← (← fld "curve").getStr?
  unless curve = curveName do throw s!"unexpected curve: {curve}"
  return { commitments := ← parseArrOf (parsePt C) (← fld "commitments")
           xs := ← parseArrOf parseS (← fld "xs")
           evals := ← parseArrOf (parseArrOf parseS) (← fld "evals")
           polyscale := ← parseS (← fld "polyscale")
           evalscale := ← parseS (← fld "evalscale")
           proof := { lr := ← parseArrOf (parsePair (parsePt C)) (← fld "lr")
                      delta := ← parsePt C (← fld "delta")
                      z1 := ← parseS (← fld "z1")
                      z2 := ← parseS (← fld "z2")
                      sg := ← parsePt C (← fld "sg") } }

def checkFixture (C : Ipa.CommitmentCurve) (curveName : String) (path : String) :
    IO Bool := do
  let raw ← IO.FS.readFile path
  let (σ, inp, chunkPts, chunkEvals) ← match Json.parse raw >>= fun j => do
      let pts ← parseArrOf (parsePt C) (← j.getObjVal? "chunk_commitments")
      let evs ← parseArrOf (parseZMod (n := C.scalar)) (← j.getObjVal? "chunk_evals")
      return (← parseSRS C j, ← parseInput C curveName j, pts, evs) with
    | .ok v => pure v
    | .error e => throw (IO.userError s!"{path}: fixture parse error: {e}")
  unless inp.commitments.size = 1 ∧ inp.xs.size = 1 do
    throw (IO.userError s!"{path}: expected the combined 1×1 view")
  let x := inp.xs.getD 0 0
  let y := x ^ (2 ^ σ.k)
  -- commitment recombination: ∑ i, yⁱ • Pᵢ against the production combination
  let combinedOurs : C.Point :=
    Ipa.msm C (fun i : Fin chunkPts.size => chunkPts.getD i 0)
      (fun i => y ^ (i : ℕ))
  let hComm := decide (combinedOurs = inp.commitments.getD 0 0)
  IO.println s!"  {if hComm then "✓" else "✗"} {curveName}: commitment recombination \
    matches production chunk_commitment"
  -- eval recombination: ∑ i, yⁱ · eᵢ against the claimed combined value
  let vOurs : C.ScalarField :=
    (List.range chunkEvals.size).foldr
      (fun i acc => y ^ i * chunkEvals.getD i 0 + acc) 0
  let hEval := decide (vOurs = (inp.evals.getD 0 #[]).getD 0 0)
  IO.println s!"  {if hEval then "✓" else "✗"} {curveName}: eval recombination matches \
    the combined claim"
  -- the executable verifier accepts the combined opening
  let ok := Ipa.verify C σ inp
  IO.println s!"  {if ok then "✓" else "✗"} {curveName}: executable verifier accepts \
    the combined opening ({chunkPts.size} chunks, {σ.k} rounds)"
  let bad := { inp with evals := inp.evals.modify 0 (·.modify 0 (· + 1)) }
  let rejected := !Ipa.verify C σ bad
  IO.println s!"  {if rejected then "✓" else "✗"} {curveName}: corrupted combined value \
    rejected"
  return hComm && hEval && ok && rejected

def main : IO Unit := do
  let okV ← checkFixture IpaVesta.curve "vesta" "fixtures/ipa_chunked_vesta.json"
  let okP ← checkFixture IpaPallas.curve "pallas" "fixtures/ipa_chunked_pallas.json"
  unless okV && okP do throw (IO.userError "chunked fixture check FAILED")
  IO.println "✓ the chunk layer's recombination matches production kimchi on both curves"

#eval main
