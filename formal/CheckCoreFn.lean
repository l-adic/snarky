import Kimchi.CoreFn

/-!
# CheckCoreFn — evaluate compiled PureScript inside Lean and cross-validate

Runs the CoreFn interpreter (`Kimchi/CoreFn.lean`) on the *actual compiled artifact* of
`Snarky.Types.Shifted.forbiddenShiftedValues` — the shift-protocol wraparound guard: the n-bit
values whose Type1-shifted form collides mod the scalar order (the list the deployed
`shiftedEqualType1`/forbidden-value checks are built from).

The expected value is computed from an *independent* Lean statement of the spec: all
`0 ≤ x < 2ⁿ` with `x ≡ −2ⁿ (mod r)` or `x ≡ −2ⁿ−1 (mod r)`, sorted, deduplicated. Agreement
means the deployed computation — dictionaries, `unfoldr`, `sort`, `nub`, BigInt arithmetic and
all — reproduces the formal spec, with only the `purs` frontend and the interpreter trusted.

Run from `formal/` (needs the PS build's `output/` at the repo root):

    lake env lean --run CheckCoreFn.lean
-/

open Kimchi.CoreFn

/-- The spec, stated independently: n-bit representatives of `−2ⁿ` and `−2ⁿ−1` mod `r`. -/
def expectedForbidden (r : Int) (n : Nat) : List Int :=
  let twoN : Int := 2 ^ n
  let reps (x : Int) : List Int :=
    let base := x.emod r
    (List.range (((twoN - base) / r).toNat + 1)).map (fun k => base + r * Int.ofNat k)
      |>.filter (· < twoN)
  ((reps (-twoN)) ++ (reps (-twoN - 1))).eraseDups.mergeSort (· ≤ ·)

/-- Decode a little-endian hex field element (the fixture encoding). -/
def hexLe (s : String) : Int := Id.run do
  let mut acc : Int := 0
  let cs := s.toList
  let nib (c : Char) : Int :=
    if c.isDigit then Int.ofNat (c.toNat - '0'.toNat)
    else Int.ofNat (c.toLower.toNat - 'a'.toNat + 10)
  -- bytes little-endian: byte i = cs[2i], cs[2i+1]
  for i in (List.range (cs.length / 2)).reverse do
    acc := acc * 256 + (nib cs[2*i]! * 16 + nib cs[2*i+1]!)
  return acc

/-- The elaborator check: run a compiled `compile`-pipeline inside Lean and compare its
    (kind, coeffs) rows against the dumped fixture's non-public rows. -/
def checkElaborator (ctx : Ctx) (entry fixture : String) : IO Bool := do
  let result ← run ctx "Test.Snarky.Circuit.Kimchi.DumpAddComplete" entry []
  let rows ← match ← runST ctx result with
    | .vArr es => es.toList.mapM fun v => do
        match v with
        | .vObj fs => do
            let some (_, .vStr typ) := fs.find? (·.1 == "typ")
              | throw (IO.userError "row: no typ")
            let some (_, .vArr cs) := fs.find? (·.1 == "coeffs")
              | throw (IO.userError "row: no coeffs")
            let coeffs ← cs.toList.mapM fun c => do
              match c with
              | .vBig b => pure b
              | v => throw (IO.userError s!"coeff: {v.describe}")
            pure (typ, coeffs)
        | v => throw (IO.userError s!"row: {v.describe}")
    | v => throw (IO.userError s!"expected row array, got {v.describe}")
  -- the fixture
  let txt ← IO.FS.readFile fixture
  let json ← match Lean.Json.parse txt with
    | .ok j => pure j
    | .error e => throw (IO.userError s!"fixture parse: {e}")
  let pubSize := (json.getObjVal? "publicInputSize").toOption.bind (·.getInt?.toOption)
    |>.getD 0 |>.toNat
  let gates ← match json.getObjVal? "gates" with
    | .ok (.arr a) => pure a
    | _ => throw (IO.userError "fixture: no gates")
  let fixRows ← (gates.toList.drop pubSize).mapM fun g => do
    let typ := ((g.getObjVal? "typ").toOption.bind (·.getStr?.toOption)).getD "?"
    let coeffs := match g.getObjVal? "coeffs" with
      | .ok (.arr cs) => cs.toList.filterMap (·.getStr?.toOption) |>.map hexLe
      | _ => []
    pure (typ, coeffs)
  IO.println s!"[{entry}] interpreted rows: {rows.length}, fixture non-public: {fixRows.length}"
  let norm (l : List (String × List Int)) :=
    l.map fun (t, cs) => (t, cs.map (fun c => Int.emod c vestaScalarModulus))
  if norm rows == norm fixRows then do
    IO.println s!"MATCH [{entry}]: interpreted elaboration ≡ fixture (kinds + coeffs) = true"
    pure true
  else do
    IO.println s!"MISMATCH: first interp row {rows.head?} vs fixture {fixRows.head?}"
    pure false

def main : IO Unit := do
  let ctx ← Ctx.new "../output"
  -- Vesta.ScalarField modulus (= the Pallas base field cardinality)
  let r : Int :=
    0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
  let n : Nat := 255
  let arg := Value.vObj [("modulus", .vBig r), ("sizeInBits", .vInt (Int.ofNat n))]
  let result ← run ctx "Snarky.Types.Shifted" "forbiddenShiftedValues" [arg]
  let got ← match result with
    | .vArr es => es.toList.mapM fun v => do
        match v with
        | .vBig b => pure b
        | v => throw (IO.userError s!"non-bigint in result: {v.describe}")
    | v => throw (IO.userError s!"expected array result, got {v.describe}")
  let expected := expectedForbidden r n
  IO.println s!"corefn-evaluated forbiddenShiftedValues: {got.length} values"
  IO.println s!"independent Lean spec:                   {expected.length} values"
  if got == expected then
    IO.println "MATCH: compiled PureScript ≡ Lean spec (via CoreFn evaluation) = true"
  else do
    IO.println s!"MISMATCH!\n  got:      {got.take 4}...\n  expected: {expected.take 4}..."
    throw (IO.userError "cross-validation failed")
  -- the elaborator itself
  unless (← checkElaborator ctx "addCompleteKindsCoeffs" "fixtures/add_complete_step.json") do
    throw (IO.userError "elaborator cross-validation failed (addComplete)")
  let okVbm ← try
    checkElaborator ctx "varBaseMulKindsCoeffs" "fixtures/varbasemul_step.json"
  catch ex => do
    dumpTrace ctx
    throw ex
  unless okVbm do
    throw (IO.userError "elaborator cross-validation failed (varBaseMul)")
