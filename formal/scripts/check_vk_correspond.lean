import Kimchi.Fixture.Kimchi
import Lean.Data.Json

/-! The verifier-key ↔ index correspondence, by value: every committed column of the
production verifier key (`fixtures/kimchi_proof_vesta.json`) must equal the value-MSM
of the **computed** Lagrange-basis commitments against the corresponding derived column
(`fixtures/index_vesta.json` — the same circuit; its columns are separately pinned to
the Index model's derivations by `check_index_fixture`). This is
`Kimchi.Verifier.VKCorresponds` for the production key, adjudicated numerically through
`commitPoly_columnPoly`'s formula `commit (columnPoly v) = ∑ⱼ vⱼ • Lcommⱼ` — and since
the basis is computed here by `lagrangeComm` (not dumped), the 28-column match also
validates that def across the whole domain (a wrong `ω^(−ij)` exponent at any `i`
breaks it). -/

open Lean Kimchi.Fixture Kimchi.Fixture.Ipa Kimchi.Fixture.Kimchi Kimchi.Verifier

abbrev C := IpaVesta.curve
abbrev F := C.ScalarField

def parseF : Json → Except String F := parseZMod

def main : IO Unit := do
  let idxPath := "fixtures/index_vesta.json"
  let vkPath := "fixtures/kimchi_proof_vesta.json"
  let idxJ ← IO.FS.readFile idxPath
  let vkJ ← IO.FS.readFile vkPath
  let r : Except String (Array (String × Array F × C.Point) × Array C.Point) := do
    let ji ← Json.parse idxJ
    let jv ← Json.parse vkJ
    let vk ← parseVK C KimchiVesta.frParams jv
    let σ ← parseSRSAt C vk.domainLog2 jv
    let h ← parsePt C (← jv.getObjVal? "srs_h")
    -- the Lagrange basis, computed lazily (no longer carried in the fixture)
    let basis := (Array.range vk.n).map (fun i => lagrangeComm C σ vk.omega i)
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
    return (checks, basis)
  match r with
  | .error e => throw (IO.userError s!"fixture parse error: {e}")
  | .ok (checks, basis) =>
    let basisMSM (v : Array F) : C.Point :=
      Ipa.msm C (fun j : Fin basis.size => basis.getD j 0) (fun j => v.getD j 0)
    let mut bad : Array String := #[]
    for (name, v, comm) in checks do
      unless basisMSM v = comm do bad := bad.push name
    IO.println s!"{vkPath}: {checks.size} committed columns vs value-MSM of the \
      computed {basis.size}-point Lagrange basis — \
      {if bad.isEmpty then "all match" else s!"MISMATCH: {bad}"}"
    unless bad.isEmpty do throw (IO.userError "VK correspondence check FAILED")
    IO.println "✓ the production verifier key corresponds to the index: every \
      committed column is the value-MSM of its (computed) derived Lagrange basis"

#eval main
