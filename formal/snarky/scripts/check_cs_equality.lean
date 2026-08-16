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
`Basic` gadget vocabulary, the landed gate gadgets (poseidon, endo_scalar,
endo_mul), and the gadget-complete pickles sub-circuits (pow2_pow, b_correct,
bullet_reduce_one_step, bullet_reduce_step — composition fixtures, the bullet pair
composing endoInv + endoMul + addComplete; their dumps are witness-less, so the
checks are CS-side only). Deferred, with the blocker each waits on:
- ftcomm_*, xhat_* (and everything downstream: ivp, verify, wrap/step mains) — the
  pickles buildout (var_base_mul and scale_fast2_128 themselves are ACTIVE below:
  the VarBaseMul gadget's own oracle checks);
- hash_messages_*, finalize_other_proof_*, schnorr_verify — the sponge circuit layer
  (packages/random-oracle; FOP additionally the OptSponge variant);
- group_map_step — activatable now (Basic-only), transcription pending a
  Tonelli–Shanks sqrt witness helper;
- group_map_wrap, combine_poly_wrap — gadget-complete but Fq-side: this corpus is
  Fp-typed throughout, so the wrap column needs an Fq mirror of the plumbing;
- app_circuit_chunks2 — Basic-only but a 39MB dump (~2^16 rows): ingestion cost.

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
import Snarky.Kimchi.Circuit.Poseidon
import Snarky.Kimchi.Circuit.EndoScalar
import Snarky.Kimchi.Circuit.EndoMul
import Snarky.Kimchi.Circuit.VarBaseMul
import Poseidon.Basic
import Pasta.Endo

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

/-- `poseidon_step_circuit` (the PS gadget `Snarky.Circuit.Kimchi.Poseidon.poseidon`
at the step field's parameters; the PS `Vector 3` interface renders as the gadget's
triples at the boundary). -/
def poseidonCircuit (s : Vector (FVar Fp) 3) : CircuitM Fp C (Vector (FVar Fp) 3) := do
  let (a, b, c) ← poseidon Poseidon.fpParams (s[0], s[1], s[2])
  pure #v[a, b, c]

/-- The Vesta endomorphism's scalar eigenvalue at the step field (PS
`endoScalar @Vesta.BaseField @Fp`; `Pasta.vestaLam`). -/
def endoVestaLam : Fp := (Pasta.vestaLam : ℤ)

/-- `endo_scalar_step_circuit` (the PS gadget `Snarky.Circuit.Kimchi.EndoScalar.toField`
at 8 rows and the constant Vesta eigenvalue). -/
def endoScalarCircuit (scalar : FVar Fp) : CircuitM Fp C (FVar Fp) :=
  EndoScalar.toField 8 scalar (.const endoVestaLam)

/-- `endo_mul_step_circuit` (the PS gadget `Snarky.Circuit.Kimchi.EndoMul.endo` at
128 bits / 32 rounds and the Pallas endo coefficient). -/
def endoMulCircuit (input : AffinePoint (FVar Fp) × FVar Fp) :
    CircuitM Fp C (AffinePoint (FVar Fp)) :=
  endoMul Pasta.pallasEndo 32 input.1 ⟨input.2⟩

/-- `var_base_mul_step_circuit` (the PS gadget
`Snarky.Circuit.Kimchi.VarBaseMul.scaleFast1` at 51 chunks — the full 255-bit
ladder). -/
def varBaseMulCircuit (input : AffinePoint (FVar Fp) × FVar Fp) :
    CircuitM Fp C (AffinePoint (FVar Fp)) :=
  scaleFast1 255 51 input.1 ⟨input.2⟩

/-- `scale_fast2_128_step_circuit` (the PS gadget
`Snarky.Circuit.Kimchi.VarBaseMul.scaleFast2'` at 26 chunks / 127 `sDiv2` bits — the
128-bit split-scalar path, exercising `splitFieldVar` and `scaleFast2`). -/
def scaleFast2_128Circuit (input : AffinePoint (FVar Fp) × FVar Fp) :
    CircuitM Fp C (AffinePoint (FVar Fp)) :=
  scaleFast2' 255 26 127 input.1 input.2

/-! ## Pickles sub-circuits

Composition circuits from `packages/pickles`, transcribed against their dumps the
same way the gadget circuits are — these are the first fixtures exercising the
gadgets IN COMPOSITION. Their dumps are witness-less (`exactMatchEff`
registrations), so the comparison checks the constraint-system side only: gate
types, coefficients, wires, per-cell variable ids, public size. -/

/-- `pow2_pow_step_circuit` (`Pickles.Util.Pow2.pow2PowSquare` at 16 squarings —
sixteen `square` rows chained). -/
def pow2PowCircuit (input : Vector (FVar Fp) 1) : CircuitM Fp C PUnit := do
  let _ ← (List.range 16).foldlM (fun acc _ => square acc) input[0]
  pure PUnit.unit

/-- The Type1 shifted-scalar unshift constant `2^255 + 1` (PS `Shifted.shift1` at the
255-bit step field): `fromShiftedType1Circuit t = 2·t + c`, constraint-free. -/
def shift1c : Fp := 2 ^ 255 + 1

/-- The challenge polynomial `∏ᵢ (1 + cᵢ·pt^(2^(k-1-i)))` (PS `IPA.bPolyCircuit`):
`k−1` squarings (as generic `mul` rows, matching OCaml's `Field.( * )`), then the
`k`-term product folded left, allocation order verbatim. -/
def bPolyCircuit (chals : List (FVar Fp)) (pt : FVar Fp) :
    CircuitM Fp C (FVar Fp) := do
  let (squares, _) ← mapAccumM
    (fun (prev : FVar Fp) (_ : Unit) => do
      let sq ← mul prev prev
      pure (sq, sq))
    pt (List.replicate (chals.length - 1) ())
  let powTwoPows := pt :: squares
  match chals.zip powTwoPows.reverse with
  | [] => pure (.const 1)
  | (c0, pw0) :: rest => do
    let cp0 ← mul c0 pw0
    let init := CVar.add_ (.const 1) cp0
    rest.foldlM
      (fun acc (cpw : FVar Fp × FVar Fp) => do
        let cp ← mul cpw.1 cpw.2
        let term := CVar.add_ (.const 1) cp
        mul term acc)
      init

/-- `b_correct_step_circuit` (PS `bCorrectStepCircuit` over `IPA.bCorrectCircuit`):
16 raw 128-bit challenges expanded through `EndoScalar.toField` at 8 rows — in
REVERSE order, OCaml's right-to-left evaluation — then
`b(ζ) + evalscale·b(ζω)` compared against the Type1-unshifted claimed `b`.
Input layout: challenges 0–15, `ζ` 16, `ζω` 17, `evalscale` 18, claimed `b` 19. -/
def bCorrectCircuit (input : Vector (FVar Fp) 20) : CircuitM Fp C PUnit := do
  let inl := input.toList
  let endoVar : FVar Fp := .const endoVestaLam
  let expandedRev ← ((inl.take 16).reverse).mapM
    (fun c => EndoScalar.toField 8 c endoVar)
  let expanded := expandedRev.reverse
  let zero : FVar Fp := .const 0
  let expectedB : FVar Fp :=
    CVar.add_ (CVar.scale_ 2 (inl.getD 19 zero)) (.const shift1c)
  let bZetaOmega ← bPolyCircuit expanded (inl.getD 17 zero)
  let scaledB ← mul (inl.getD 18 zero) bZetaOmega
  let bZeta ← bPolyCircuit expanded (inl.getD 16 zero)
  let computedB := CVar.add_ bZeta scaledB
  let _ ← equals expectedB computedB
  pure PUnit.unit

/-- The step-side `endoInv` scalar-field data: the Pallas group order is prime
(`pallas_card` carries the `Fact` over to the numeral). -/
def pallasOrderPrime : Nat.Prime PALLAS_SCALAR_CARD :=
  Pasta.pallas_card ▸ (Fact.out : Nat.Prime CompElliptic.Curves.Pasta.Pallas.curve.toAffine.order)

/-- One IPA fold step (`bullet_reduce_one_step_circuit`, the PS wrapper's inline body):
`endoInv(L, u) + endo(R, u)` — the first fixture composing endoInv, endoMul, and
addComplete. Input layout: `L` 0–1, `R` 2–3, the 128-bit challenge 4. -/
def bulletReduceOneCircuit (input : Vector (FVar Fp) 5) : CircuitM Fp C PUnit := do
  let l : AffinePoint (FVar Fp) := ⟨input[0], input[1]⟩
  let r : AffinePoint (FVar Fp) := ⟨input[2], input[3]⟩
  let lScaled ← endoInv Pasta.pallasEndo CompElliptic.Curves.Pasta.Pallas.curve.toAffine
    PALLAS_SCALAR_CARD pallasOrderPrime ((Pasta.pallasLam : ℤ) : ZMod PALLAS_SCALAR_CARD)
    l ⟨input[4]⟩
  let rScaled ← endoMul Pasta.pallasEndo 32 r ⟨input[4]⟩
  let _ ← addComplete lScaled rScaled
  pure PUnit.unit

/-- The IPA `lr_prod` fold (`bullet_reduce_step_circuit`, PS `IPA.bulletReduceCircuit`
at 15 pairs): per pair `endoInv(Lᵢ, uᵢ) + endo(Rᵢ, uᵢ)`, then the running
`addComplete` sum. Input layout: pair `j`'s points at `4j…4j+3`, challenges 60–74. -/
def bulletReduceCircuit (input : Vector (FVar Fp) 75) : CircuitM Fp C PUnit := do
  let inl := input.toList
  let zero : FVar Fp := .const 0
  let pt := fun i => inl.getD i zero
  let terms ← (List.range 15).mapM (fun j => do
    let l : AffinePoint (FVar Fp) := ⟨pt (4 * j), pt (4 * j + 1)⟩
    let r : AffinePoint (FVar Fp) := ⟨pt (4 * j + 2), pt (4 * j + 3)⟩
    let u := pt (60 + j)
    let lScaled ← endoInv Pasta.pallasEndo CompElliptic.Curves.Pasta.Pallas.curve.toAffine
      PALLAS_SCALAR_CARD pallasOrderPrime ((Pasta.pallasLam : ℤ) : ZMod PALLAS_SCALAR_CARD)
      l ⟨u⟩
    let rScaled ← endoMul Pasta.pallasEndo 32 r ⟨u⟩
    addComplete lScaled rScaled)
  match terms with
  | [] => pure PUnit.unit
  | head :: tail => do
    let _ ← tail.foldlM (fun acc q => (·.p) <$> addComplete acc q.p) head.p
    pure PUnit.unit

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
  let (rows, gates, pubSize) := kimchiGateData (a := a) (b := b) main
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
    match kimchiSolve (a := a) (b := b) main input with
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
        addCompleteCircuit),
    ("poseidon_step_circuit",
      compareWith (a := Vector Fp 3) (b := Vector Fp 3) poseidonCircuit),
    ("endo_scalar_step_circuit",
      compareWith (a := Fp) (b := Fp) endoScalarCircuit),
    ("endo_mul_step_circuit",
      compareWith (a := AffinePoint Fp × Fp) (b := AffinePoint Fp) endoMulCircuit),
    ("var_base_mul_step_circuit",
      compareWith (a := AffinePoint Fp × Fp) (b := AffinePoint Fp) varBaseMulCircuit),
    ("scale_fast2_128_step_circuit",
      compareWith (a := AffinePoint Fp × Fp) (b := AffinePoint Fp) scaleFast2_128Circuit),
    ("pow2_pow_step_circuit", compareWith (a := Vector Fp 1) (b := PUnit) pow2PowCircuit),
    ("b_correct_step_circuit",
      compareWith (a := Vector Fp 20) (b := PUnit) bCorrectCircuit),
    ("bullet_reduce_one_step_circuit",
      compareWith (a := Vector Fp 5) (b := PUnit) bulletReduceOneCircuit),
    ("bullet_reduce_step_circuit",
      compareWith (a := Vector Fp 75) (b := PUnit) bulletReduceCircuit) ]

def main : IO Unit := do
  let dir ← resultsDir
  let mut failures := 0
  for (name, compare) in targets do
    let path := dir / s!"{name}.json"
    let raw ← IO.FS.readFile path
    match Json.parse raw >>= parseComparisonCs? with
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
