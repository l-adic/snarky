/-
The CS-equality seam: compile the gadget circuits with the Lean kimchi backend and
compare the assembled constraint system — gate types, coefficients, wiring, RAW
PER-CELL VARIABLE IDS, public size, witness, and public values — against the
recorded PureScript dumps (`KimchiFixture.PS` decodes the JSON schema; the fixture
witness table is column-major, so the comparison transposes). The witness comparison
re-solves with the fixture's own public input, so it checks the deterministic
pipeline, not the sampled randomness. The variable-ids check is the allocation-order
contract: cell values and wire cycles are allocation-order-INSENSITIVE, so only the
ids pin the shared counter's numbering.

The circuits transcribe `Test.Pickles.CircuitDiffs.Main`
(packages/pickles-circuit-diffs/test/): every witness-carrying circuit built from the
`Basic` gadget vocabulary.

The dumps are the PS suite's gitignored export: generate with
`CIRCUIT_DIFFS_WITNESS_EXPORT=1 npx spago test -p pickles-circuit-diffs`. CI runs
this check against the exports its own commit just produced.

Run from `formal/snarky/`:  lake env lean --run scripts/check_cs_equality.lean
(`KIMCHI_PS_RESULTS_DIR` overrides the default export location).
-/
import KimchiFixture.PS
import Snarky.DSL
import Snarky.Kimchi.Backend.Compile
import Snarky.Kimchi.Circuit.AddComplete

open Lean Snarky Snarky.Kimchi Kimchi Kimchi.Index Kimchi.Fixture.PS CompElliptic.Fields.Pasta

/-- Where the circuit-diffs results live (package-relative default, env override). -/
def resultsDir : IO System.FilePath := do
  match (← IO.getEnv "KIMCHI_PS_RESULTS_DIR") with
  | some d => return d
  | none =>
    return ".." / ".." / "packages" / "pickles-circuit-diffs" / "circuits" / "results"

/-- The emitter tag as the index model's gate type (the mapping step 1 deferred to
the assembly). -/
def kindType : GateKind → GateType
  | .genericPlonk => .generic
  | .addComplete => .completeAdd
  | .poseidon => .poseidon
  | .varBaseMul => .varBaseMul
  | .endoMul => .endoMul
  | .endoScalar => .endoScalar
  | .zero => .zero

/-- Round constants are inert for the Poseidon-free gadget circuits. -/
def rc0 : ℕ → Fp × Fp × Fp := fun _ => (0, 0, 0)

/-- `unpack`'s bit reads go through the canonical representative. -/
instance : ToNat Fp := ⟨ZMod.val⟩

/-- The kimchi constraint sum at the corpus field, the one instantiation every
circuit below runs at. -/
abbrev C := KimchiConstraint Fp

/-! ## The gadget circuits (transcribed from `Test.Pickles.CircuitDiffs.Main`) -/

/-- `mul_step_circuit`: witness a zero, multiply. -/
def mulCircuit (x : FVar Fp) : CircuitM Fp C (FVar Fp) := do
  let y ← witness (val := Fp) (pure 0)
  mul x y

/-- `inv_step_circuit` (the fixture input is nonzero — `inv`'s honest domain). -/
def invCircuit (x : FVar Fp) : CircuitM Fp C (FVar Fp) :=
  inv x

/-- `div_step_circuit`: the divisor's witness must be nonzero for the solver. -/
def divCircuit (x : FVar Fp) : CircuitM Fp C (FVar Fp) := do
  let y ← witness (val := Fp) (pure 1)
  div x y

/-- `if_step_circuit`: witnessed branch and selector, muxed. -/
def ifCircuit (x : FVar Fp) : CircuitM Fp C (FVar Fp) := do
  let y ← witness (val := Fp) (pure 0)
  let b ← witness (val := Bool) (pure true)
  select b x y

/-- `equals_step_circuit`. -/
def equalsCircuit (x : FVar Fp) : CircuitM Fp C (BoolVar Fp) := do
  let y ← witness (val := Fp) (pure 0)
  equals x y

/-- `pow7_step_circuit`. -/
def pow7Circuit (x : FVar Fp) : CircuitM Fp C (FVar Fp) :=
  pow x 7

/-- `pow8_step_circuit`. -/
def pow8Circuit (x : FVar Fp) : CircuitM Fp C (FVar Fp) :=
  pow x 8

/-- `assert_equal_step_circuit`. -/
def assertEqualCircuit (x : FVar Fp) : CircuitM Fp C PUnit := do
  let y ← witness (val := Fp) (pure 0)
  assertEqual x y

/-- `app_circuit_two_phase_chain_make_zero`: assert the input equals zero. -/
def makeZeroAppCircuit (x : FVar Fp) : CircuitM Fp C PUnit :=
  assertEqual x (.const 0)

/-- `app_circuit_two_phase_chain_increment`: assert the input equals `prev + 1`. -/
def incrementAppCircuit (x : FVar Fp) : CircuitM Fp C PUnit := do
  let prev ← witness (val := Fp) (pure 0)
  assertEqual x (CVar.add_ (.const 1) prev)

/-- `assert_square_step_circuit`. -/
def assertSquareCircuit (x : FVar Fp) : CircuitM Fp C PUnit := do
  let y ← witness (val := Fp) (pure 0)
  assertSquare x y

/-- `assert_non_zero_step_circuit` (the fixture input is nonzero). -/
def assertNonZeroCircuit (x : FVar Fp) : CircuitM Fp C PUnit :=
  assertNonZero x

/-- `assert_not_equal_step_circuit`. -/
def assertNotEqualCircuit (x : FVar Fp) : CircuitM Fp C PUnit := do
  let y ← witness (val := Fp) (pure 0)
  assertNotEqual x y

/-- `unpack_step_circuit`: 254 checked bits, repacked and pinned. -/
def unpackCircuit (x : FVar Fp) : CircuitM Fp C PUnit := do
  let _ ← unpack x 254
  pure PUnit.unit

/-- `bool_and_step_circuit`. -/
def boolAndCircuit (x : BoolVar Fp) : CircuitM Fp C (BoolVar Fp) := do
  let y ← witness (val := Bool) (pure true)
  Snarky.and x y

/-- `bool_or_step_circuit`. -/
def boolOrCircuit (x : BoolVar Fp) : CircuitM Fp C (BoolVar Fp) := do
  let y ← witness (val := Bool) (pure true)
  Snarky.or x y

/-- `bool_xor_step_circuit`. -/
def boolXorCircuit (x : BoolVar Fp) : CircuitM Fp C (BoolVar Fp) := do
  let y ← witness (val := Bool) (pure true)
  Snarky.xor x y

/-- `bool_all_step_circuit`. -/
def boolAllCircuit (x : BoolVar Fp) : CircuitM Fp C (BoolVar Fp) := do
  let y ← witness (val := Bool) (pure true)
  let w ← witness (val := Bool) (pure true)
  Snarky.all [x, y, w]

/-- `bool_any_step_circuit`. -/
def boolAnyCircuit (x : BoolVar Fp) : CircuitM Fp C (BoolVar Fp) := do
  let y ← witness (val := Bool) (pure true)
  let w ← witness (val := Bool) (pure true)
  Snarky.any [x, y, w]

/-- `bool_assert_step_circuit`. -/
def boolAssertCircuit (x : BoolVar Fp) : CircuitM Fp C PUnit :=
  Snarky.assert x

/-- `add_complete_step_circuit`: complete addition of two points, infinity
witnessed. -/
def addCompleteCircuit (p : AffinePoint (FVar Fp) × AffinePoint (FVar Fp)) :
    CircuitM Fp C (AffinePoint (FVar Fp)) :=
  (·.p) <$> addFast .dontCheckFinite p.1 p.2

/-! ## The comparison -/

/-- An assembled circuit in the fixture's `Raw` shape (witness transposed to the
column-major recording) — the index round-trip ingests the LEAN output, so it holds
with or without byte-agreement. -/
def assembledRaw (rows : List (KimchiRow Fp)) (gates : List (AssembledGate Fp))
    (pubSize : Nat) (wit : List (Vector Fp 15)) (pubs : List Fp) : Raw :=
  { publicInputSize := pubSize
    typs := (gates.map (kindType ·.kind)).toArray
    coeffs := (gates.map (·.coeffs.toArray)).toArray
    wires := (gates.map fun g =>
      (g.wires.toList.map fun w => (w.col, w.row)).toArray).toArray
    vars := (rows.map fun r => r.vars.toList.toArray).toArray
    witness := ((List.range 15).map fun j =>
      (wit.map fun row => row.toList.getD j 0).toArray).toArray
    pub := pubs.toArray }

/-- The round-trip law, decided per circuit: the compiled output padded into the
index model builds by decision (`Index.build?` — domain shape, wiring bijectivity,
public-row form) and the solved witness satisfies the verified checker. -/
def indexRoundTrip (rows : List (KimchiRow Fp)) (gates : List (AssembledGate Fp))
    (pubSize : Nat) (wit : List (Vector Fp 15)) (pubs : List Fp) : Bool :=
  match Kimchi.Fixture.PS.build (assembledRaw rows gates pubSize wit pubs) with
  | .error _ => false
  | .ok inst =>
    haveI : NeZero inst.n := inst.nz
    decide (Satisfies inst.idx inst.wit.pub inst.wit.tab)

/-- Compare one circuit's assembled system and re-solved witness against its dump:
the CS data (types, coefficients, wires, public size) is input-independent; the
witness re-solve seeds the fixture's recorded public inputs. -/
def compareWith {a b avar bvar : Type} [A : CircuitType Fp a avar]
    [CheckedType Fp C avar] [B : CircuitType Fp b bvar]
    (main : avar → CircuitM Fp C bvar) (raw : Raw) : List (String × Bool) :=
  let (rows, gates, pubSize) := kimchiGateData (a := a) (b := b) rc0 main
  let csChecks :=
    [ ("publicInputSize", pubSize == raw.publicInputSize),
      ("gate count", gates.length == raw.typs.size),
      ("gate types", (gates.map (kindType ·.kind)).toArray == raw.typs),
      ("coefficients", (gates.map (·.coeffs.toArray)).toArray == raw.coeffs),
      ("wires",
        (gates.map fun g =>
          (g.wires.toList.map fun w => (w.col, w.row)).toArray).toArray
          == raw.wires),
      ("variables",
        (rows.map fun r => r.vars.toList.toArray).toArray == raw.vars) ]
  let input : a := A.fieldsToValue (Vector.ofFn fun i => raw.pub.getD i 0)
  let witChecks := if raw.witness.isEmpty then [] else
    match kimchiSolve (a := a) (b := b) rc0 main input with
    | .error _ => [("solve", false)]
    | .ok (_, env) =>
      let (wit, pubs) := makeWitness env rows ((allocRange 0 pubSize).toList)
      [ ("witness",
          (List.range 15).map (fun j => wit.map fun row => row.toList.getD j 0)
            == raw.witness.toList.map (·.toList)),
        ("public values", pubs == raw.pub.toList),
        ("index round-trip", indexRoundTrip rows gates pubSize wit pubs) ]
  csChecks ++ witChecks

/-- The corpus under comparison: every witness-carrying `Basic`-gadget circuit. -/
def targets : List (String × (Raw → List (String × Bool))) :=
  [ ("mul_step_circuit", compareWith (a := Fp) (b := Fp) mulCircuit),
    ("inv_step_circuit", compareWith (a := Fp) (b := Fp) invCircuit),
    ("div_step_circuit", compareWith (a := Fp) (b := Fp) divCircuit),
    ("if_step_circuit", compareWith (a := Fp) (b := Fp) ifCircuit),
    ("equals_step_circuit", compareWith (a := Fp) (b := Bool) equalsCircuit),
    ("pow7_step_circuit", compareWith (a := Fp) (b := Fp) pow7Circuit),
    ("pow8_step_circuit", compareWith (a := Fp) (b := Fp) pow8Circuit),
    ("assert_equal_step_circuit", compareWith (a := Fp) (b := PUnit) assertEqualCircuit),
    ("app_circuit_two_phase_chain_make_zero",
      compareWith (a := Fp) (b := PUnit) makeZeroAppCircuit),
    ("app_circuit_two_phase_chain_increment",
      compareWith (a := Fp) (b := PUnit) incrementAppCircuit),
    ("assert_square_step_circuit", compareWith (a := Fp) (b := PUnit) assertSquareCircuit),
    ("assert_non_zero_step_circuit",
      compareWith (a := Fp) (b := PUnit) assertNonZeroCircuit),
    ("assert_not_equal_step_circuit",
      compareWith (a := Fp) (b := PUnit) assertNotEqualCircuit),
    ("unpack_step_circuit", compareWith (a := Fp) (b := PUnit) unpackCircuit),
    ("bool_and_step_circuit", compareWith (a := Bool) (b := Bool) boolAndCircuit),
    ("bool_or_step_circuit", compareWith (a := Bool) (b := Bool) boolOrCircuit),
    ("bool_xor_step_circuit", compareWith (a := Bool) (b := Bool) boolXorCircuit),
    ("bool_all_step_circuit", compareWith (a := Bool) (b := Bool) boolAllCircuit),
    ("bool_any_step_circuit", compareWith (a := Bool) (b := Bool) boolAnyCircuit),
    ("bool_assert_step_circuit", compareWith (a := Bool) (b := PUnit) boolAssertCircuit),
    ("add_complete_step_circuit",
      compareWith (a := AffinePoint Fp × AffinePoint Fp) (b := AffinePoint Fp)
        addCompleteCircuit) ]

def main : IO Unit := do
  let dir ← resultsDir
  let mut failures := 0
  for (name, compare) in targets do
    let path := dir / s!"{name}.json"
    let raw ← IO.FS.readFile path
    match Json.parse raw >>= parseComparison? with
    | .error e =>
      failures := failures + 1
      IO.println s!"✗ {name}: parse error: {e}"
    | .ok none =>
      failures := failures + 1
      IO.println s!"✗ {name}: not a comparison dump"
    | .ok (some fixture) =>
      let bad := (compare fixture).filter (!·.2)
      if bad.isEmpty then
        IO.println s!"✓ {name}"
      else
        failures := failures + 1
        IO.println s!"✗ {name}: {String.intercalate ", " (bad.map (·.1))}"
  if failures > 0 then
    throw <| IO.userError s!"CS-equality FAILED ({failures} circuit(s))"
  IO.println s!"── CS equality OK ({targets.length} circuits) ──"
