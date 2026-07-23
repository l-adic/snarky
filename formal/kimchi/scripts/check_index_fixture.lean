import Kimchi.Index.Satisfies
import Kimchi.Verifier.Kimchi
import Kimchi.Verifier.Wire
import KimchiFixture.Kimchi
import FixtureKit.Parse
import Lean.Data.Json

/-!
# The index model against mixed-gate kimchi fixtures, at both chunking regimes

Replays the index model on production data from `tools/fixture-dump`'s `index_dump`
(a circuit with a public row, wired generic rows, a full Poseidon gadget, a CompleteAdd
row, and an EndoMulScalar block — kimchi's own row checker and the full production
prove+verify asserted at dump time). Three fixtures across BOTH Pasta curves and BOTH
production chunking regimes:

* `fixtures/index_vesta.json` — the UNCHUNKED regression (Vesta, `zk_rows = 3`, so the
  σ interior-mask range `[n − zk + 2, n − 1)` is EMPTY);
* `fixtures/index_vesta_nc2.json` / `fixtures/index_pallas_nc2.json` — the CHUNKED twins
  on both curves (`zk_rows = 5`, so the σ interior-mask range is NONEMPTY — rows 29, 30
  at `n = 32`).

For each fixture the driver checks:

* **construction by decision**: `Index.build?` must accept the dumped table — deciding
  the primitive-root and coset certificates, the row bounds, and the wiring laws on the
  production data;
* **the derived columns**: the model's `selectorRow`/`coeffRow`/`sigmaAddrRow` must
  reproduce the production selector, coefficient, and sigma column evaluations row by
  row — pinning the table→columns derivation. At `zk_rows = 5` this is a DIRECT
  row-level pin of the σ-zeroing branch on rows 29, 30 (a sign or off-by-one there now
  fails here, not only indirectly through the VK-correspondence commitment check);
* **satisfiability**: `decide (Satisfies idx pub wTab)` on the production witness — the
  checker is the `Decidable` instance of the predicate itself, nothing else;
* **negatives**: a corrupted gate cell, a corrupted wired cell, and a corrupted public
  input must each be rejected.

The whole body is generic over the commitment curve `C` (so both Pasta scalar fields run
through one code path); the per-curve Poseidon MDS is derived from the curve bundle as the
`Index.build?` parameter `mdsOfParams C.frParams`.
-/

open Lean FixtureKit Bulletproof Bulletproof.Fixture Kimchi Kimchi.Index Kimchi.Verifier

def parseGateType : String → Except String GateType
  | "zero" => .ok .zero
  | "generic" => .ok .generic
  | "poseidon" => .ok .poseidon
  | "completeAdd" => .ok .completeAdd
  | "varBaseMul" => .ok .varBaseMul
  | "endoMul" => .ok .endoMul
  | "endoScalar" => .ok .endoScalar
  | t => .error s!"unknown gate type: {t}"

/-- The index-fixture data a run consumes, over the commitment curve's scalar field. -/
structure RawFixture (C : Ipa.CommitmentCurve) where
  /-- The domain size `n` (a power of two). -/
  n : ℕ
  /-- The zero-knowledge row count (`3` unchunked, `5` at `nc = 2`). -/
  zkRows : ℕ
  /-- The number of public-input rows. -/
  publicCount : ℕ
  /-- The public-input values. -/
  pub : Array C.ScalarField
  /-- The domain's primitive root of unity. -/
  omega : C.ScalarField
  /-- The base-field endo coefficient `cs.endo`. -/
  endoBase : C.ScalarField
  /-- The permutation coset shifts. -/
  shifts : Array C.ScalarField
  /-- The per-row gate types. -/
  typs : Array GateType
  /-- The per-row coefficient vectors. -/
  coeffs : Array (Array C.ScalarField)
  /-- The per-row wire pointers `(col, row)`. -/
  wires : Array (Array (ℕ × ℕ))
  /-- The padded witness table (column-major). -/
  witness : Array (Array C.ScalarField)
  /-- The production selector columns, tagged by gate type. -/
  selectors : Array (GateType × Array C.ScalarField)
  /-- The production coefficient columns. -/
  coefficients : Array (Array C.ScalarField)
  /-- The production σ (sigma) columns. -/
  sigma : Array (Array C.ScalarField)

def parseRaw (C : Ipa.CommitmentCurve) (j : Json) : Except String (RawFixture C) := do
  let fld (k : String) : Except String Json := j.getObjVal? k
  let pF : Json → Except String C.ScalarField := parseZMod
  let gatesJ ← (← fld "gates").getArr?
  let typs ← gatesJ.mapM fun g => do parseGateType (← (← g.getObjVal? "typ").getStr?)
  let coeffs ← gatesJ.mapM fun g => do parseArrOf pF (← g.getObjVal? "coeffs")
  let wires ← gatesJ.mapM fun g => do
    (← (← g.getObjVal? "wires").getArr?).mapM fun w => do
      let a ← w.getArr?
      return (← a[0]!.getNat?, ← a[1]!.getNat?)
  let selJ ← fld "selectors"
  let sel (name : String) (t : GateType) : Except String (GateType × Array C.ScalarField) := do
    return (t, ← parseArrOf pF (← selJ.getObjVal? name))
  return { n := ← parseNat (← fld "n")
           zkRows := ← parseNat (← fld "zk_rows")
           publicCount := ← parseNat (← fld "public_count")
           pub := ← parseArrOf pF (← fld "public")
           omega := ← pF (← fld "omega")
           endoBase := ← pF (← fld "endo_base")
           shifts := ← parseArrOf pF (← fld "shifts")
           typs := typs
           coeffs := coeffs
           wires := wires
           witness := ← parseArrOf (parseArrOf pF) (← fld "witness")
           selectors := #[← sel "generic" .generic, ← sel "poseidon" .poseidon,
             ← sel "completeAdd" .completeAdd, ← sel "varBaseMul" .varBaseMul,
             ← sel "endoMul" .endoMul, ← sel "endoScalar" .endoScalar]
           coefficients := ← parseArrOf (parseArrOf pF) (← fld "coefficients")
           sigma := ← parseArrOf (parseArrOf pF) (← fld "sigma") }

def buildGates {C : Ipa.CommitmentCurve} (fx : RawFixture C) {n : ℕ} (_hn : fx.n = n) :
    Except String (Fin n → GateRow C.ScalarField n) := do
  unless fx.typs.size = n && fx.wires.size = n && fx.coeffs.size = n do
    throw "gate table size mismatch"
  let rows ← (Array.range n).mapM fun i => do
    let ws ← (fx.wires[i]!).mapM fun (col, row) => do
      if h : col < permCols ∧ row < n then
        return ((⟨col, h.1⟩ : Fin permCols), (⟨row, h.2⟩ : Fin n))
      else throw s!"wire out of range at row {i}"
    let t : GateType := fx.typs[i]!
    let cf : Array C.ScalarField := fx.coeffs[i]!
    if h7 : ws.size = permCols then
      return { typ := t
               coeffs := fun c => cf[(c : ℕ)]!
               wires := fun c => ws[(c : ℕ)]'(by omega) : GateRow C.ScalarField n }
    else throw "wire count"
  if hsz : rows.size = n then
    return fun i => rows[(i : ℕ)]'(by omega)
  else throw "row count"

def checks {C : Ipa.CommitmentCurve} (fx : RawFixture C) {n : ℕ} [NeZero n]
    (idx : Index C.ScalarField n) : List (String × Bool) :=
  let wTab : Fin n → Fin wCols → C.ScalarField :=
    fun i c => (fx.witness[(c : ℕ)]!)[(i : ℕ)]!
  let pub : Fin idx.publicCount → C.ScalarField := fun i => fx.pub[(i : ℕ)]!
  let sat (w : Fin n → Fin wCols → C.ScalarField)
      (p : Fin idx.publicCount → C.ScalarField) : Bool :=
    decide (Satisfies idx p w)
  -- Corruption targets derived from the index, not from the dumper's layout: a
  -- constrained non-generic row (all modeled gates read column 0), and a nontrivially
  -- wired cell. Their absence is a fixture-quality failure, reported loudly.
  let gateRow? : Option (Fin n) := (List.finRange n).find? fun i =>
    (idx.gates i).typ != GateType.zero && (idx.gates i).typ != GateType.generic
  let wired? : Option (Fin permCols × Fin n) := (List.finRange n).findSome? fun r =>
    ((List.finRange permCols).find? fun col => idx.wiringMap (col, r) != (col, r)).map
      fun col => (col, r)
  let bump (r : Fin n) (c : ℕ) : Fin n → Fin wCols → C.ScalarField :=
    fun i c' => if i = r ∧ (c' : ℕ) = c then wTab i c' + 1 else wTab i c'
  [ ("selector columns match production",
      fx.selectors.all fun (t, col) =>
        (List.finRange n).all fun i => idx.selectorRow t i == col[(i : ℕ)]!),
    ("coefficient columns match production",
      (List.finRange coeffCols).all fun c =>
        (List.finRange n).all fun i =>
          idx.coeffRow c i == (fx.coefficients[(c : ℕ)]!)[(i : ℕ)]!),
    ("sigma columns match production (incl. the interior-mask zeroing at zk_rows = 5)",
      (List.finRange permCols).all fun c =>
        (List.finRange n).all fun i =>
          idx.sigmaAddrRow c i == (fx.sigma[(c : ℕ)]!)[(i : ℕ)]!),
    ("Satisfies (decided from the predicate)", sat wTab pub),
    ("corrupted gate cell rejected (target derived from the table)",
      match gateRow? with
      | some r => !sat (bump r 0) pub
      | none => false),
    ("corrupted wired cell rejected (target derived from the wiring)",
      match wired? with
      | some (col, r) => !sat (bump r (col : ℕ)) pub
      | none => false),
    ("corrupted public input rejected", !sat wTab (fun i => pub i + 1)) ]

def run {C : Ipa.CommitmentCurve}
    {n : ℕ} [NeZero n] (fx : RawFixture C) (hn : fx.n = n) : IO Unit := do
  let gates ← IO.ofExcept (buildGates fx hn)
  let some idx := Index.build? gates fx.publicCount fx.zkRows fx.omega fx.endoBase
      (mdsOfParams C.frParams) (fun i => fx.shifts[(i : ℕ)]!)
    | throw (IO.userError "Index.build? rejected the production data")
  IO.println "  ✓ Index.build? accepts (all laws decided on production data)"
  let results := checks fx (n := n) idx
  for (name, ok) in results do
    IO.println s!"  {if ok then "✓" else "✗"} {name}"
  unless results.all (·.2) do
    throw (IO.userError "index fixture check FAILED")
  IO.println s!"✓ the index model matches kimchi on this fixture \
    (n={n}, zk_rows={fx.zkRows}, gates incl. generic/poseidon/completeAdd/endoScalar)"

/-- Read, parse, and run one index fixture over its commitment curve. -/
def runFile (C : Ipa.CommitmentCurve) (path : String) : IO Unit := do
  IO.println s!"— {path} —"
  let raw ← IO.FS.readFile path
  let fx ← match Json.parse raw >>= parseRaw C with
    | .ok fx => pure fx
    | .error e => throw (IO.userError s!"index fixture parse error: {e}")
  if hpos : 0 < fx.n then
    haveI : NeZero fx.n := ⟨Nat.pos_iff_ne_zero.mp hpos⟩
    run fx rfl
  else
    throw (IO.userError "empty domain")

def main : IO Unit := do
  let dir := (← IO.getEnv "KIMCHI_FIXTURES_DIR").getD "fixtures"
  -- Vesta, unchunked (zk_rows = 3): σ interior-mask range empty.
  runFile IpaVesta.curve s!"{dir}/index_vesta.json"
  -- Vesta and Pallas, nc = 2 (zk_rows = 5): σ interior-mask range = rows 29, 30.
  runFile IpaVesta.curve s!"{dir}/index_vesta_nc2.json"
  runFile IpaPallas.curve s!"{dir}/index_pallas_nc2.json"
  IO.println "✓ the index model matches kimchi on the mixed-gate fixtures across both \
    Pasta curves and both chunking regimes (nc = 1 and nc = 2)"

#eval main
