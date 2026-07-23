import Kimchi.Index.Basic
import Kimchi.Verifier.Kimchi
import Kimchi.Verifier.Wire
import KimchiFixture.Kimchi
import Lean.Data.Json

/-! The verifier-key ↔ index correspondence, by value, at BOTH production chunking
regimes: every committed column of the production verifier keys —
`fixtures/kimchi_proof_vesta.json` (`nc = 1`, `zk_rows = 3`) and
`fixtures/kimchi_proof_vesta_nc2.json` (`nc = 2`, `zk_rows = 5`; the same circuit and
seed over a half-domain SRS) — must, CHUNK BY CHUNK, equal the value-MSM of that key's
Lagrange-basis chunk commitments against the corresponding derived column of the same
circuit (`fixtures/index_vesta.json` — same circuit and seed; Pallas has no index
fixture, so the correspondence is adjudicated on Vesta only). This adjudicates the
chunked indexer model of `Reduction/Soundness.lean` numerically:
`commitPolyChunk (columnPoly v) c = ∑ⱼ vⱼ • Lⱼ[c]` (chunking is linear, so the
value-MSM formula holds per chunk window), and the six selector columns carry
production's fixed blinder PER CHUNK (`mask_custom` with the all-ones blinder over the
chunk vector — the model choice `commitPolyMaskedChunk` makes; a wrong per-chunk mask
fails here).

CAUTION — the σ-column ZEROING (latent-bug reproducer): production ZEROES the σ
columns on rows `[n − zk_rows + 2, n − 1)` ("Zero out the sigmas in the zk rows, to
ensure that the permutation aggregation is quasi-random for those rows",
constraints.rs:538–544) — the interior mask rows, exactly where the THREE-factor
`permutation_vanishing_polynomial` lets the recurrence run. The σ columns checked here
are NOT read from a fixture: they are the model's own derivation — `Index.build?` on
the dumped gate table at each regime's `zk_rows`, then `Index.sigmaAddrRow`
(`Kimchi/Index/Basic.lean`), whose zeroing branch is that same range. So this check
adjudicates the production σ commitments AGAINST the model's own `sigmaAddrRow`: a
sign or off-by-one drift in the model's zeroing branch at `zk_rows = 5` (rows `29, 30`
at `n = 32`) makes the σ value-MSMs miss the production commitments and fails the
`nc = 2` run. At `zk_rows = 3` the range is EMPTY — the `nc = 1` run therefore pins
the UN-zeroed correspondence, the raw wiring addresses. -/

open Lean FixtureKit Bulletproof Bulletproof.Fixture Kimchi Kimchi.Index

abbrev C := IpaVesta.curve
abbrev F := C.ScalarField

def parseF : Json → Except String F := parseZMod

/-- The index-fixture data a regime run consumes: the gate table (types, coefficients,
wire pointers), the domain/permutation constants, and the production-derived selector
and coefficient columns. σ columns are deliberately NOT read — the model derives them
(see the module docstring). -/
structure IdxData where
  n : ℕ
  publicCount : ℕ
  omega : F
  endoBase : F
  shifts : Array F
  typs : Array GateType
  coeffs : Array (Array F)
  wires : Array (Array (ℕ × ℕ))
  selJ : Json
  coefficients : Array (Array F)

def parseGateType : String → Except String GateType
  | "zero" => .ok .zero
  | "generic" => .ok .generic
  | "poseidon" => .ok .poseidon
  | "completeAdd" => .ok .completeAdd
  | "varBaseMul" => .ok .varBaseMul
  | "endoMul" => .ok .endoMul
  | "endoScalar" => .ok .endoScalar
  | t => .error s!"unknown gate type: {t}"

def parseIdx (ji : Json) : Except String IdxData := do
  let fld (k : String) : Except String Json := ji.getObjVal? k
  let gatesJ ← (← fld "gates").getArr?
  let typs ← gatesJ.mapM fun g => do parseGateType (← (← g.getObjVal? "typ").getStr?)
  let coeffs ← gatesJ.mapM fun g => do parseArrOf parseF (← g.getObjVal? "coeffs")
  let wires ← gatesJ.mapM fun g => do
    (← (← g.getObjVal? "wires").getArr?).mapM fun w => do
      let a ← w.getArr?
      return (← a[0]!.getNat?, ← a[1]!.getNat?)
  return { n := ← parseNat (← fld "n")
           publicCount := ← parseNat (← fld "public_count")
           omega := ← parseF (← fld "omega")
           endoBase := ← parseF (← fld "endo_base")
           shifts := ← parseArrOf parseF (← fld "shifts")
           typs, coeffs, wires
           selJ := ← fld "selectors"
           coefficients := ← parseArrOf (parseArrOf parseF) (← fld "coefficients") }

def buildGates (d : IdxData) {n : ℕ} (_hn : d.n = n) :
    Except String (Fin n → GateRow F n) := do
  unless d.typs.size = n && d.wires.size = n && d.coeffs.size = n do
    throw "gate table size mismatch"
  let rows ← (Array.range n).mapM fun i => do
    let ws ← (d.wires[i]!).mapM fun (col, row) => do
      if h : col < permCols ∧ row < n then
        return ((⟨col, h.1⟩ : Fin permCols), (⟨row, h.2⟩ : Fin n))
      else throw s!"wire out of range at row {i}"
    let t : GateType := d.typs[i]!
    let cf : Array F := d.coeffs[i]!
    if h7 : ws.size = permCols then
      return { typ := t
               coeffs := fun c => cf[(c : ℕ)]!
               wires := fun c => ws[(c : ℕ)]'(by omega) : GateRow F n }
    else throw "wire count"
  if hsz : rows.size = n then
    return fun i => rows[(i : ℕ)]'(by omega)
  else throw "row count"

/-- The value-MSM of a column against one chunk slice of the basis commitments. -/
def basisChunkMSM (basis : Array (Array C.Point)) (c : ℕ) (col : Array F) : C.Point :=
  Ipa.msm C (fun j : Fin basis.size => (basis.getD j #[]).getD c 0)
    (fun j => col.getD j 0)

/-- The MODEL's σ columns at the given `zk_rows`: `Index.build?` on the dumped gate
table (every index law decided), then `Index.sigmaAddrRow` — the wiring addresses
through the model's own zeroing branch. -/
def sigmaColsOf (d : IdxData) (zkRows : ℕ) : Except String (Array (Array F)) :=
  if hpos : 0 < d.n then
    haveI : NeZero d.n := ⟨Nat.pos_iff_ne_zero.mp hpos⟩
    do
      let gates ← buildGates d rfl
      let some idx := Index.build? gates d.publicCount zkRows d.omega d.endoBase
          (Kimchi.Verifier.mdsOfParams Kimchi.Verifier.Wire.KimchiVesta.frParams)
          (fun i => d.shifts[(i : ℕ)]!)
        | throw s!"Index.build? rejected the index data at zk_rows = {zkRows}"
      return (List.finRange permCols).toArray.map fun c =>
        ((List.finRange d.n).map (idx.sigmaAddrRow c)).toArray
  else throw "empty domain"

/-- One chunking regime: the VK fixture at `vkPath` against the index data, with the
σ columns derived by the model itself at this regime's `zk_rows`. -/
def runRegime (d : IdxData) (vkPath : String) : IO Unit := do
  let vkJ ← IO.FS.readFile vkPath
  let r : Except String
      (Array (String × Array F × Array C.Point) × Array (Array C.Point) × ℕ × ℕ) := do
    let jv ← Json.parse vkJ
    let basis ← parseArrOf (Kimchi.Fixture.parseComm C)
      (← jv.getObjVal? "lagrange_basis")
    let h ← parsePt C (← jv.getObjVal? "srs_h")
    let nat (k : String) : Except String ℕ := do
      match (← (← jv.getObjVal? k).getStr?).toNat? with
      | some v => pure v
      | none => throw s!"field {k} is not a numeral"
    let nDom ← nat "n"
    let mps ← nat "max_poly_size"
    let nc ← if mps = 0 ∨ nDom % mps ≠ 0 then throw "bad n/max_poly_size"
      else pure (nDom / mps)
    let zkRows ← nat "zk_rows"
    unless nDom = d.n do throw "the VK and index fixtures disagree on the domain size"
    let cpt (k : String) : Except String (Array C.Point) := do
      Kimchi.Fixture.parseComm C (← jv.getObjVal? k)
    let cpts (k : String) : Except String (Array (Array C.Point)) := do
      parseArrOf (Kimchi.Fixture.parseComm C) (← jv.getObjVal? k)
    let sigmaComm ← cpts "sigma_comm"
    let coeffComm ← cpts "coefficients_comm"
    -- the model's own σ columns at THIS regime's zk_rows (see the module docstring)
    let sigmaCols ← sigmaColsOf d zkRows
    unless sigmaComm.size = permCols ∧ d.coefficients.size = coeffCols
        ∧ coeffComm.size = coeffCols do throw "column family size mismatch"
    let mut checks : Array (String × Array F × Array C.Point) := #[]
    for i in [0:permCols] do
      checks := checks.push (s!"sigma[{i}]", sigmaCols.getD i #[], sigmaComm.getD i #[])
    for i in [0:coeffCols] do
      checks := checks.push
        (s!"coeff[{i}]", d.coefficients.getD i #[], coeffComm.getD i #[])
    -- selectors: production's fixed blinder, PER CHUNK
    let col (j : Json) (k : String) : Except String (Array F) := do
      parseArrOf parseF (← j.getObjVal? k)
    let sel (name comm : String) :
        Except String (String × Array F × Array C.Point) := do
      return (name, ← col d.selJ name, (← cpt comm).map (· - h))
    checks := checks.push (← sel "generic" "generic_comm")
    checks := checks.push (← sel "poseidon" "psm_comm")
    checks := checks.push (← sel "completeAdd" "complete_add_comm")
    checks := checks.push (← sel "varBaseMul" "mul_comm")
    checks := checks.push (← sel "endoMul" "emul_comm")
    checks := checks.push (← sel "endoScalar" "endomul_scalar_comm")
    return (checks, basis, nc, zkRows)
  match r with
  | .error e => throw (IO.userError s!"{vkPath}: fixture parse error: {e}")
  | .ok (checks, basis, nc, zkRows) =>
    let mut bad : Array String := #[]
    for (name, v, comms) in checks do
      unless comms.size = nc do bad := bad.push s!"{name} (chunk count)"
      for c in [0:nc] do
        unless basisChunkMSM basis c v = comms.getD c 0 do
          bad := bad.push s!"{name}[chunk {c}]"
    IO.println s!"{vkPath}: {checks.size} committed columns × {nc} chunks \
      (zk_rows = {zkRows}) vs value-MSM of the {basis.size}-basis chunk commitments — \
      {if bad.isEmpty then "all match" else s!"MISMATCH: {bad}"}"
    unless bad.isEmpty do
      throw (IO.userError s!"{vkPath}: chunked VK correspondence check FAILED")

def main : IO Unit := do
  let dir := (← IO.getEnv "KIMCHI_FIXTURES_DIR").getD "fixtures"
  let idxJ ← IO.FS.readFile s!"{dir}/index_vesta.json"
  let d ← match Json.parse idxJ >>= parseIdx with
    | .ok d => pure d
    | .error e => throw (IO.userError s!"index fixture parse error: {e}")
  -- nc = 1, zk_rows = 3: the σ-zeroing range is empty — the un-zeroed correspondence
  runRegime d s!"{dir}/kimchi_proof_vesta.json"
  -- nc = 2, zk_rows = 5: rows 29, 30 zeroed by the model's sigmaAddrRow branch
  runRegime d s!"{dir}/kimchi_proof_vesta_nc2.json"
  IO.println "✓ the production verifier keys (nc = 1 and nc = 2) correspond to the \
    index: every committed column chunk is the value-MSM of its derived column \
    against the Lagrange chunk commitments — σ columns from the model's own \
    Index.sigmaAddrRow, selectors per-chunk masked"

#eval main
