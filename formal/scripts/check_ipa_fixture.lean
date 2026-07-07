import Kimchi.Verifier.Ipa
import Kimchi.Fixture.Parse
import Lean.Data.Json

/-!
# End-to-end IPA verification of kimchi/proof-systems fixtures

Runs the executable IPA verifier (`Kimchi.Verifier.Ipa`) on fixtures produced by the
production prover (`tools/fixture-dump`), over both Pasta curves. The parser reads exactly
the wire data — the SRS (into the library's `Kimchi.Commitment.IPA.SRS`), commitments,
evaluation points and claimed evaluations, combination scalars, opening proof — and every
point carries its on-curve proof from parsing; all Fiat-Shamir derivation happens inside
`verify`. A corrupted claimed evaluation must be rejected.

Run (after `lake build Kimchi`): `scripts/check_ipa_fixture.sh`.
-/

open Lean Kimchi.Fixture Kimchi.Commitment.IPA Kimchi.Verifier

def parsePt (C : Ipa.CommitmentCurve) : Json → Except String C.Point :=
  parseSWPoint (parseZMod (n := C.base)) C.E

/-- The fixture's `srs_g`/`srs_h` as a library SRS. The abstract randomisation base `U` is
transcript-derived by the verifier and never read; it is filled with `0`. -/
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
  let parseS : Json → Except String C.Fr := parseZMod
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

/-- Verify one fixture end-to-end; when `negative` is set, also check that corrupting the
first claimed evaluation flips the verdict to REJECT. -/
def checkFixture (C : Ipa.CommitmentCurve) (curveName : String) (path : String)
    (negative : Bool) : IO Bool := do
  let raw ← IO.FS.readFile path
  let (σ, inp) ← match Json.parse raw >>= fun j => do
      return (← parseSRS C j, ← parseInput C curveName j) with
    | .ok v => pure v
    | .error e => throw (IO.userError s!"{path}: fixture parse error: {e}")
  let ok := Ipa.verify C σ inp
  IO.println s!"{path}: {inp.commitments.size} poly(s) × {inp.xs.size} point(s), \
    {σ.k} rounds — verify: {if ok then "ACCEPT" else "REJECT"}"
  if negative then
    let bad := { inp with evals := inp.evals.modify 0 (·.modify 0 (· + 1)) }
    let rejected := !Ipa.verify C σ bad
    IO.println s!"{path}: corrupted evaluation — \
      {if rejected then "REJECT (expected)" else "ACCEPT (BUG)"}"
    return ok && rejected
  return ok

def main : IO Unit := do
  let okV1 ← checkFixture IpaVesta.curve "vesta" "fixtures/ipa_opening_vesta.json"
    (negative := true)
  let okV2 ← checkFixture IpaVesta.curve "vesta" "fixtures/ipa_batch_vesta.json"
    (negative := false)
  let okP1 ← checkFixture IpaPallas.curve "pallas" "fixtures/ipa_opening_pallas.json"
    (negative := true)
  let okP2 ← checkFixture IpaPallas.curve "pallas" "fixtures/ipa_batch_pallas.json"
    (negative := false)
  unless okV1 && okV2 && okP1 && okP2 do
    throw (IO.userError "IPA end-to-end verification FAILED")
  IO.println "✓ the executable verifiers over both Pasta curves accept the \
    kimchi/proof-systems proofs from wire data"

#eval main
