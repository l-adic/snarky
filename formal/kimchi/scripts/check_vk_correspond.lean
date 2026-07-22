import Kimchi.Verifier.Kimchi
import Kimchi.Verifier.Wire
import KimchiFixture.Kimchi
import Lean.Data.Json

/-! The CHUNKED verifier-key ↔ index correspondence, by value: every committed column
of the production `nc = 2` verifier key (`fixtures/kimchi_proof_vesta_nc2.json`) must,
CHUNK BY CHUNK, equal the value-MSM of the production Lagrange-basis chunk commitments
against the corresponding derived column (`fixtures/index_vesta.json` — the same
circuit and seed). This adjudicates the chunked indexer model of
`Reduction/Soundness.lean` numerically: `commitPolyChunk (columnPoly v) c = ∑ⱼ vⱼ • Lⱼ[c]`
(chunking is linear, so the value-MSM formula holds per chunk window), and the six
selector columns carry production's fixed blinder PER CHUNK (`mask_custom` with the
all-ones blinder over the chunk vector — the model choice `commitPolyMaskedChunk`
makes; a wrong per-chunk mask fails here).

CAUTION — the σ-column ZEROING (latent-bug reproducer): production ZEROES the σ
columns on rows `[n − zk_rows + 2, n − 1)` ("Zero out the sigmas in the zk rows, to
ensure that the permutation aggregation is quasi-random for those rows",
constraints.rs:538–544) — the interior mask rows, exactly where the THREE-factor
`permutation_vanishing_polynomial` lets the recurrence run. The range is EMPTY at
`zk_rows = 3`, so the `nc = 1` fixtures never exercised it; at `zk_rows = 5` rows
`29, 30` are zeroed. The index fixture carries the `zk_rows = 3` σ values, so this
script applies the zeroing itself before the MSM (the raw index-fixture columns are
the un-zeroed wiring addresses). The formal Index model mirrors the zeroing in
`Index.sigmaAddrRow` / `Permutation.sigmaCell` — this check documents and adjudicates
that semantic. -/

open Lean FixtureKit Bulletproof Bulletproof.Fixture Kimchi.Verifier

abbrev C := IpaVesta.curve
abbrev F := C.ScalarField

def parseF : Json → Except String F := parseZMod

/-- The value-MSM of a column against one chunk slice of the basis commitments. -/
def basisChunkMSM (basis : Array (Array C.Point)) (c : ℕ) (col : Array F) : C.Point :=
  Ipa.msm C (fun j : Fin basis.size => (basis.getD j #[]).getD c 0)
    (fun j => col.getD j 0)

def main : IO Unit := do
  let dir := (← IO.getEnv "KIMCHI_FIXTURES_DIR").getD "fixtures"
  let idxPath := s!"{dir}/index_vesta.json"
  let vkPath := s!"{dir}/kimchi_proof_vesta_nc2.json"
  let idxJ ← IO.FS.readFile idxPath
  let vkJ ← IO.FS.readFile vkPath
  let r : Except String
      (Array (String × Array F × Array C.Point) × Array (Array C.Point) × ℕ) := do
    let ji ← Json.parse idxJ
    let jv ← Json.parse vkJ
    let basis ← parseArrOf (Kimchi.Fixture.parseComm C)
      (← jv.getObjVal? "lagrange_basis")
    let h ← parsePt C (← jv.getObjVal? "srs_h")
    let nc ← match (← (← jv.getObjVal? "n").getStr?).toNat?,
        (← (← jv.getObjVal? "max_poly_size").getStr?).toNat? with
      | some n, some mps =>
        if mps = 0 ∨ n % mps ≠ 0 then throw "bad n/max_poly_size" else pure (n / mps)
      | _, _ => throw "bad n/max_poly_size"
    let selJ ← ji.getObjVal? "selectors"
    let col (j : Json) (k : String) : Except String (Array F) := do
      parseArrOf parseF (← j.getObjVal? k)
    let cols15 (k : String) : Except String (Array (Array F)) := do
      parseArrOf (parseArrOf parseF) (← ji.getObjVal? k)
    let cpt (k : String) : Except String (Array C.Point) := do
      Kimchi.Fixture.parseComm C (← jv.getObjVal? k)
    let cpts (k : String) : Except String (Array (Array C.Point)) := do
      parseArrOf (Kimchi.Fixture.parseComm C) (← jv.getObjVal? k)
    let zkRows ← match (← (← jv.getObjVal? "zk_rows").getStr?).toNat? with
      | some z => pure z
      | none => throw "bad zk_rows"
    let nDom ← match (← (← jv.getObjVal? "n").getStr?).toNat? with
      | some n => pure n
      | none => throw "bad n"
    -- production zeroes σ on the interior mask rows [n − zk + 2, n − 1)
    let zeroMask (v : Array F) : Array F :=
      v.mapIdx (fun r x => if nDom + 2 - zkRows ≤ r ∧ r < nDom - 1 then 0 else x)
    let sigmaCols ← (fun a : Array (Array F) => a.map zeroMask) <$> cols15 "sigma"
    let coeffCols ← cols15 "coefficients"
    let sigmaComm ← cpts "sigma_comm"
    let coeffComm ← cpts "coefficients_comm"
    unless sigmaCols.size = 7 ∧ sigmaComm.size = 7 ∧ coeffCols.size = 15
        ∧ coeffComm.size = 15 do throw "column family size mismatch"
    let mut checks : Array (String × Array F × Array C.Point) := #[]
    for i in [0:7] do
      checks := checks.push (s!"sigma[{i}]", sigmaCols.getD i #[], sigmaComm.getD i #[])
    for i in [0:15] do
      checks := checks.push (s!"coeff[{i}]", coeffCols.getD i #[], coeffComm.getD i #[])
    -- selectors: production's fixed blinder, PER CHUNK
    let sel (name comm : String) :
        Except String (String × Array F × Array C.Point) := do
      return (name, ← col selJ name, (← cpt comm).map (· - h))
    checks := checks.push (← sel "generic" "generic_comm")
    checks := checks.push (← sel "poseidon" "psm_comm")
    checks := checks.push (← sel "completeAdd" "complete_add_comm")
    checks := checks.push (← sel "varBaseMul" "mul_comm")
    checks := checks.push (← sel "endoMul" "emul_comm")
    checks := checks.push (← sel "endoScalar" "endomul_scalar_comm")
    return (checks, basis, nc)
  match r with
  | .error e => throw (IO.userError s!"fixture parse error: {e}")
  | .ok (checks, basis, nc) =>
    let mut bad : Array String := #[]
    for (name, v, comms) in checks do
      unless comms.size = nc do bad := bad.push s!"{name} (chunk count)"
      for c in [0:nc] do
        unless basisChunkMSM basis c v = comms.getD c 0 do
          bad := bad.push s!"{name}[chunk {c}]"
    IO.println s!"{vkPath}: {checks.size} committed columns × {nc} chunks vs \
      value-MSM of the {basis.size}-basis chunk commitments — \
      {if bad.isEmpty then "all match" else s!"MISMATCH: {bad}"}"
    unless bad.isEmpty do throw (IO.userError "chunked VK correspondence check FAILED")
    IO.println "✓ the production chunked verifier key corresponds to the index: every \
      committed column chunk is the value-MSM of its derived column against the \
      Lagrange chunk commitments (selectors per-chunk masked)"

#eval main
