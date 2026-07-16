import Kimchi.Verifier.Kimchi
import Bulletproof.Fixture
import Lean.Data.Json

/-! The verifier-key ↔ index correspondence, by value: every committed column of the
production verifier key (`fixtures/kimchi_proof_vesta.json`) must equal the value-MSM
of the production Lagrange-basis commitments against the corresponding derived column
(`fixtures/index_vesta.json` — the same circuit; its columns are separately pinned to
the Index model's derivations by `check_index_fixture`). This is
`Kimchi.Verifier.VKCorresponds` for the production key, adjudicated numerically
through `commitPoly_columnPoly`'s formula: `commit (columnPoly v) = ∑ vⱼ • Lcommⱼ`. -/

open Lean FixtureKit Bulletproof Bulletproof.Fixture Kimchi.Verifier

abbrev C := IpaVesta.curve
abbrev F := C.ScalarField

def parseF : Json → Except String F := parseZMod

/-- The value-MSM of a column against the basis commitments. -/
def basisMSM (basis : Array C.Point) (col : Array F) : C.Point :=
  Ipa.msm C (fun j : Fin basis.size => basis.getD j 0)
    (fun j => col.getD j 0)

def main : IO Unit := do
  let dir := (← IO.getEnv "KIMCHI_FIXTURES_DIR").getD "fixtures"
  let idxPath := s!"{dir}/index_vesta.json"
  let vkPath := s!"{dir}/kimchi_proof_vesta.json"
  let idxJ ← IO.FS.readFile idxPath
  let vkJ ← IO.FS.readFile vkPath
  let r : Except String (Array (String × Array F × C.Point) × ℕ) := do
    let ji ← Json.parse idxJ
    let jv ← Json.parse vkJ
    let basis ← parseArrOf (parsePt C) (← jv.getObjVal? "lagrange_basis")
    let h ← parsePt C (← jv.getObjVal? "srs_h")
    let selJ ← ji.getObjVal? "selectors"
    let col (j : Json) (k : String) : Except String (Array F) := do
      parseArrOf parseF (← j.getObjVal? k)
    let cols15 (k : String) : Except String (Array (Array F)) := do
      parseArrOf (parseArrOf parseF) (← ji.getObjVal? k)
    let pt (k : String) : Except String C.Point := do parsePt C (← jv.getObjVal? k)
    let pts (k : String) : Except String (Array C.Point) := do
      parseArrOf (parsePt C) (← jv.getObjVal? k)
    let sigmaCols ← cols15 "sigma"
    let coeffCols ← cols15 "coefficients"
    let sigmaComm ← pts "sigma_comm"
    let coeffComm ← pts "coefficients_comm"
    unless sigmaCols.size = 7 ∧ sigmaComm.size = 7 ∧ coeffCols.size = 15
        ∧ coeffComm.size = 15 do throw "column family size mismatch"
    -- the six selectors carry production's fixed blinder (mask_fixed = +1·h,
    -- verifier_index.rs:173); σ and coefficient columns are unblinded
    let mut checks : Array (String × Array F × C.Point) := #[]
    for i in [0:7] do
      checks := checks.push (s!"sigma[{i}]", sigmaCols.getD i #[], sigmaComm.getD i 0)
    for i in [0:15] do
      checks := checks.push (s!"coeff[{i}]", coeffCols.getD i #[], coeffComm.getD i 0)
    let sel (name comm : String) : Except String (String × Array F × C.Point) := do
      return (name, ← col selJ name, (← pt comm) - h)
    checks := checks.push (← sel "generic" "generic_comm")
    checks := checks.push (← sel "poseidon" "psm_comm")
    checks := checks.push (← sel "completeAdd" "complete_add_comm")
    checks := checks.push (← sel "varBaseMul" "mul_comm")
    checks := checks.push (← sel "endoMul" "emul_comm")
    checks := checks.push (← sel "endoScalar" "endomul_scalar_comm")
    return (checks, basis.size)
  match r with
  | .error e => throw (IO.userError s!"fixture parse error: {e}")
  | .ok (checks, bsize) =>
    let basis ← match Json.parse vkJ >>= fun j => do
        parseArrOf (parsePt C) (← j.getObjVal? "lagrange_basis") with
      | .ok b => pure b
      | .error e => throw (IO.userError e)
    let mut bad : Array String := #[]
    for (name, v, comm) in checks do
      unless basisMSM basis v = comm do bad := bad.push name
    IO.println s!"{vkPath}: {checks.size} committed columns vs value-MSM of the \
      {bsize}-point Lagrange basis — \
      {if bad.isEmpty then "all match" else s!"MISMATCH: {bad}"}"
    unless bad.isEmpty do throw (IO.userError "VK correspondence check FAILED")
    IO.println "✓ the production verifier key corresponds to the index: every \
      committed column is the value-MSM of its derived column"

#eval main
