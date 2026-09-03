/-
The CS-equality seam: compile the gadget circuits with the Lean kimchi backend and
compare the assembled constraint system — gate types, coefficients, wiring, per-cell
variable ids, public size, witness, and public values — against the recorded
PureScript dumps (`KimchiFixture.PS` decodes the JSON schema; the fixture witness
table is column-major, so the comparison transposes). The witness comparison
re-solves with the fixture's own public input, so it checks the deterministic
pipeline, not the sampled randomness.

The variable-ids check is the allocation-order contract, compared UP TO A GLOBAL
RENAMING: this backend numbers the reduction's internal variables above the circuit's
rather than interleaved with them, and witnesses the public outputs rather than
preallocating them (`Snarky.Kimchi.kimchiGateData`), so the two counters agree only
up to a bijection. What the renaming-invariant form still pins — and what `wires`
does not see, since a cell holding a once-used variable and an empty cell both wire
to themselves — is the per-cell OCCUPANCY pattern and the identification the ids
induce across cells.

The circuits transcribe `Test.Pickles.CircuitDiffs.Main`
(packages/pickles-circuit-diffs/test/): every witness-carrying circuit built from the
`Basic` gadget vocabulary, the landed gate gadgets (poseidon, endo_scalar,
endo_mul), the gadget-complete pickles sub-circuits (pow2_pow, b_correct,
bullet_reduce_one_step, bullet_reduce_step — composition fixtures, the bullet pair
composing endoInv + endoMul + addComplete; their dumps are witness-less, so the
checks are CS-side only), ft_eval0_step (the proved `Pickles.ftEval0Circuit` under
the linearization prelude, against the PS `FtEval0Common` harness), and cip_{step,wrap}
(the proved `Pickles.combinedInnerProduct` over `Pickles.bPolyCircuit`, against the PS
`Cip` harness — the wrap column's first pickles sub-circuit). Deferred, with the
blocker each waits on:
- ftcomm_*, xhat_* (and everything downstream: ivp, verify, wrap/step mains) — the
  pickles buildout (var_base_mul and scale_fast2_128 themselves are ACTIVE below:
  the VarBaseMul gadget's own oracle checks);
- hash_messages_*, finalize_other_proof_*, schnorr_verify — the sponge circuit layer
  (packages/random-oracle; FOP additionally the OptSponge variant);
- group_map_step — activatable now (Basic-only), transcription pending a
  Tonelli–Shanks sqrt witness helper;
- combine_poly_wrap — gadget-complete, pending a transcription of `combinePolynomials`;
- app_circuit_chunks2 — Basic-only but a 39MB dump (~2^16 rows): ingestion cost.

The corpus has two columns. The step circuits run at `Fp` (Pallas's base field) and the
wrap circuits at `Fq` (Vesta's base field): the plumbing is generic in the field, and each
target carries its side's constants (`KimchiFixture.PS.Side`: the multiplicative generator,
the endomorphism coefficient and the MDS matrix). The wrap column holds the group map at
Vesta's parameters and the wrap linearization over `Pickles.Linearization.fqTokens`, so
both deployed token streams are compared against their PureScript circuits.

The dumps are the PS suite's gitignored export: generate with
`CIRCUIT_DIFFS_WITNESS_EXPORT=1 npx spago test -p pickles-circuit-diffs`. CI runs
this check against the exports its own commit just produced.

Run from `formal/`:  lake env lean --run scripts/check_cs.lean

This is a WORKSPACE script rather than a package one: the corpus spans packages — the
`Basic` and gate gadgets come from `snarky`, the linearization circuit from `pickles`,
which requires snarky — so no single package can import every circuit under comparison.
(`KIMCHI_PS_RESULTS_DIR` overrides the default export location).
-/
import Std.Data.HashMap
import KimchiFixture.PS
import Snarky
import Snarky.Kimchi.Backend.Compile
import Pickles.Linearization.Circuit
import Pickles.FtEval0
import Pickles.IPA
import Pickles.CombinedInnerProduct
import Pickles.PermScalar
import Pickles.Linearization.Fp
import Pickles.Linearization.Fq
import Snarky.Kimchi.Circuit.AddComplete
import Snarky.Kimchi.Circuit.GroupMap
import Snarky.Kimchi.Circuit.Poseidon
import Snarky.Kimchi.Circuit.EndoScalar
import Snarky.Kimchi.Circuit.EndoMul
import Snarky.Kimchi.Circuit.VarBaseMul
import Poseidon.Basic
import Pasta.Endo

open Lean Snarky Snarky.Kimchi Kimchi Kimchi.Index Kimchi.Fixture.PS CompElliptic.Fields.Pasta

/-- Where the circuit-diffs results live (workspace-relative default, env override). -/
def resultsDir : IO System.FilePath := do
  match (← IO.getEnv "KIMCHI_PS_RESULTS_DIR") with
  | some d => return d
  | none =>
    return ".." / "packages" / "pickles-circuit-diffs" / "circuits" / "results"

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

instance : ToNat Fq := ⟨ZMod.val⟩

/-- The kimchi constraint sum at the step field. -/
abbrev C := KimchiConstraint Fp

/-- The kimchi constraint sum at the wrap field. -/
abbrev Cq := KimchiConstraint Fq

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

/-! ## The comparison -/

/-- An assembled circuit in the fixture's `Raw` shape (witness transposed to the
column-major recording) — the index round-trip ingests the LEAN output, so it holds
with or without byte-agreement. -/
def assembledRaw {F : Type} [Zero F] (rows : List (KimchiRow F))
    (gates : List (AssembledGate F)) (pubSize : Nat) (wit : List (Vector F 15))
    (pubs : List F) : Raw F :=
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
def indexRoundTrip {p : ℕ} [Fact p.Prime] (side : Kimchi.Fixture.PS.Side p)
    (rows : List (KimchiRow (ZMod p))) (gates : List (AssembledGate (ZMod p)))
    (pubSize : Nat) (wit : List (Vector (ZMod p) 15)) (pubs : List (ZMod p)) : Bool :=
  match Kimchi.Fixture.PS.build side (assembledRaw rows gates pubSize wit pubs) with
  | .error _ => false
  | .ok inst =>
    haveI : NeZero inst.n := inst.nz
    decide (Satisfies inst.idx inst.wit.pub inst.wit.tab)

/-- `poseidon_step_circuit` (the PS gadget `Snarky.Circuit.Kimchi.Poseidon.poseidon`
at the step field's parameters; the PS `Vector 3` interface renders as the gadget's
`SpongeState` at the boundary). -/
def poseidonCircuit (s : Vector (FVar Fp) 3) : CircuitM Fp C (Vector (FVar Fp) 3) := do
  let r ← poseidon Poseidon.fpParams ⟨s[0], s[1], s[2]⟩
  pure #v[r.s0, r.s1, r.s2]

/-- Vesta's GLV eigenvalue, as a scalar-field element. -/
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

/-- The Pallas BW19 `setup()` parameters at the step field (PS
`groupMapParams (Proxy @PallasG)`): the poseidon package's `Poseidon.GroupMapPallas.spec`,
with PS's search-from-2 non-residue, `5`. The gates carry them as coefficients, so a wrong
value fails the byte comparison itself. -/
def groupMapParamsFp : GroupMapParams Fp := .ofSpec Poseidon.GroupMapPallas.spec 5

/-- `group_map_step_circuit` (the PS gadget
`Snarky.Circuit.Kimchi.GroupMap.groupMapCircuit` at the step field and Pallas
parameters; the dump carries no witness, so the advice is inert here). -/
def groupMapCircuitFp (input : FVar Fp) : CircuitM Fp C PUnit := do
  let _ ← groupMapCircuit (fun _ => none) groupMapParamsFp input
  pure ⟨⟩

/-- The complete-addition gadget, in its `dontCheckFinite` mode. -/
def addCompleteCircuit (p : AffinePoint (FVar Fp) × AffinePoint (FVar Fp)) :
    CircuitM Fp C (AffinePoint (FVar Fp)) :=
  (·.p) <$> addFast .dontCheckFinite p.1 p.2

/-! ## The gadget-complete pickles sub-circuits

Composition fixtures: PS sub-circuits built only from gadgets this tree already
carries, transcribed from `Test.Pickles.CircuitDiffs.Main` the same way the gadget
circuits are — these are the first fixtures exercising the gadgets IN COMPOSITION.
Their dumps are witness-less (`exactMatchEff` registrations), so the comparison
checks the constraint-system side only: gate types, coefficients, wires, per-cell
variable ids, public size. -/

/-- `pow2_pow_step_circuit` (`Pickles.Util.Pow2.pow2PowSquare` at 16 squarings —
sixteen `square` rows chained). -/
def pow2PowCircuit (input : Vector (FVar Fp) 1) : CircuitM Fp C PUnit := do
  let _ ← (List.range 16).foldlM (fun acc _ => square acc) input[0]
  pure PUnit.unit

/-- `b_correct_step_circuit` (PS `bCorrectStepCircuit`): the 16 raw 128-bit challenges
expanded by `Pickles.computeChallenges`, then `Pickles.bCorrectCircuit` against the
Type1-unshifted claim. Input layout: challenges 0–15, `ζ` 16, `ζω` 17, `evalscale` 18,
claimed `b` 19. -/
def bCorrectCircuit (input : Vector (FVar Fp) 20) : CircuitM Fp C PUnit := do
  let inl := input.toList
  let zero : FVar Fp := .const 0
  let expanded ← Pickles.computeChallenges (.const endoVestaLam) (inl.take 16)
  let _ ← Pickles.bCorrectCircuit expanded (inl.getD 16 zero) (inl.getD 17 zero)
    (inl.getD 18 zero) (Type1.fromShiftedCircuit 255 ⟨inl.getD 19 zero⟩)
  pure PUnit.unit

/-- The wrap-side scalar-challenge endomorphism (OCaml `Endo.Step_inner_curve.scalar`):
Pallas's `λ` at the wrap field. -/
def endoPallasLam : Fq := (Pasta.pallasLam : ℤ)

/-- `b_correct_wrap_circuit` (PS `bCorrectWrapCircuit`): the step layout at the wrap field,
the challenges expanded through `endoPallasLam`, the claim Type2-unshifted. -/
def bCorrectWrapCircuit (input : Vector (FVar Fq) 20) : CircuitM Fq Cq PUnit := do
  let inl := input.toList
  let zero : FVar Fq := .const 0
  let expanded ← Pickles.computeChallenges (.const endoPallasLam) (inl.take 16)
  let _ ← Pickles.bCorrectCircuit expanded (inl.getD 16 zero) (inl.getD 17 zero)
    (inl.getD 18 zero) (Type2.fromShiftedCircuit 255 ⟨inl.getD 19 zero⟩)
  pure PUnit.unit

/-- The step-side `endoInv` scalar-field data: the Pallas group order is prime
(`pallas_card` carries the `Fact` over to the numeral). -/
def pallasOrderPrime : Nat.Prime PALLAS_SCALAR_CARD :=
  Pasta.pallas_card ▸
    (Fact.out : Nat.Prime CompElliptic.Curves.Pasta.Pallas.curve.toAffine.order)

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
  let _ ← addFast .checkFinite lScaled rScaled
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
    addFast .checkFinite lScaled rScaled)
  match terms with
  | [] => pure PUnit.unit
  | head :: tail => do
    let _ ← tail.foldlM (fun acc q => (·.p) <$> addFast .checkFinite acc q.p) head.p
    pure PUnit.unit

/-- The per-cell variable ids, compared up to a global renaming: walk both cell
sequences in row-major order building the id map both ways, and require a
well-defined injection. A cell occupied on one side and empty on the other fails
immediately, as does any pair of cells the two sides identify differently. -/
def varsAgreeUpToRenaming {F : Type} (rows : List (KimchiRow F))
    (dumped : Array (Array (Option ℕ))) : Bool := Id.run do
  let lhs := rows.map (·.vars.toList)
  let rhs := dumped.toList.map (·.toList)
  if lhs.length != rhs.length then return false
  let mut fwd : Std.HashMap ℕ ℕ := {}
  let mut bwd : Std.HashMap ℕ ℕ := {}
  for (lrow, rrow) in lhs.zip rhs do
    if lrow.length != rrow.length then return false
    for (l, r) in lrow.zip rrow do
      match l, r with
      | none, none => pure ()
      | some v, some w =>
        match fwd[v]?, bwd[w]? with
        | none, none =>
          fwd := fwd.insert v w
          bwd := bwd.insert w v
        | some w', some v' => if w' != w || v' != v then return false
        | _, _ => return false
      | _, _ => return false
  return true

/-- Compare one circuit's assembled system and re-solved witness against its dump:
the CS data (types, coefficients, wires, public size) is input-independent; the
witness re-solve seeds the fixture's recorded public inputs. -/
def compareWith {p : ℕ} [Fact p.Prime] (side : Kimchi.Fixture.PS.Side p)
    {a b avar bvar : Type} [A : CircuitType (ZMod p) a avar]
    [CheckedType (ZMod p) (KimchiConstraint (ZMod p)) a avar] [B : CircuitType (ZMod p) b bvar]
    (main : avar → CircuitM (ZMod p) (KimchiConstraint (ZMod p)) bvar) (raw : Raw (ZMod p)) :
    List (String × Bool) :=
  let (rows, gates, pubVars) := kimchiGateData (a := a) (b := b) main
  let pubSize := pubVars.length
  let csChecks :=
    [ ("publicInputSize", pubSize == raw.publicInputSize),
      ("gate count", gates.length == raw.typs.size),
      ("gate types", (gates.map (kindType ·.kind)).toArray == raw.typs),
      ("coefficients", (gates.map (·.coeffs.toArray)).toArray == raw.coeffs),
      ("wires",
        (gates.map fun g =>
          (g.wires.toList.map fun w => (w.col, w.row)).toArray).toArray
          == raw.wires),
      ("gate count matches wires", gates.length == raw.wires.size),
      ("variables (up to renaming)", varsAgreeUpToRenaming rows raw.vars) ]
  let input : a := A.fieldsToValue (Vector.ofFn fun i => raw.pub.getD i 0)
  -- A witness-less dump (the `exactMatchEff` registrations) has no witness side to
  -- compare; `main` reports which circuits were checked CS-side only.
  let witChecks := if raw.witness.isEmpty then [] else
    match kimchiSolve (a := a) (b := b) main input with
    | .error _ => [("solve", false)]
    | .ok (_, env) =>
      let (wit, pubs) := makeWitness env rows pubVars
      [ ("witness",
          (List.range 15).map (fun j => wit.map fun row => row.toList.getD j 0)
            == raw.witness.toList.map (·.toList)),
        ("public values", pubs == raw.pub.toList),
        ("index round-trip", indexRoundTrip side rows gates pubSize wit pubs) ]
  csChecks ++ witChecks

/-- A corpus entry: parse the dump at the target's field and compare. -/
def target {p : ℕ} [Fact p.Prime] (side : Kimchi.Fixture.PS.Side p)
    {a b avar bvar : Type} [CircuitType (ZMod p) a avar]
    [CheckedType (ZMod p) (KimchiConstraint (ZMod p)) a avar] [CircuitType (ZMod p) b bvar]
    (main : avar → CircuitM (ZMod p) (KimchiConstraint (ZMod p)) bvar) (j : Json) :
    Except String (Option (Bool × List (String × Bool))) := do
  match ← parseComparisonCs? (m := p) j with
  | none => return none
  | some raw => return some (raw.witness.isEmpty, compareWith side (a := a) (b := b) main raw)

/-- A step-side entry. -/
def stepTarget {a b avar bvar : Type} [CircuitType Fp a avar] [CheckedType Fp C a avar]
    [CircuitType Fp b bvar] (main : avar → CircuitM Fp C bvar) :=
  target Kimchi.Fixture.PS.fpSide (a := a) (b := b) main

/-- A wrap-side entry. -/
def wrapTarget {a b avar bvar : Type} [CircuitType Fq a avar] [CheckedType Fq Cq a avar]
    [CircuitType Fq b bvar] (main : avar → CircuitM Fq Cq bvar) :=
  target Kimchi.Fixture.PS.fqSide (a := a) (b := b) main

/-! ## The linearization circuit

Transcribes `Pickles.CircuitDiffs.PureScript.LinearizationCommon.linearizationCircuitM`.
The 90-input layout is OCaml's (`dump_circuit_impl.ml`), not what the constant term needs:
coefficients, `s` and the selectors arrive as `(ζ, ζω)` pairs though only the `ζ`
component of the first two is ever read, and `z`/`s` are not read at all. -/

open Pickles.Linearization in
/-- `α^0 … α^(n+1)`, by successive multiplication — 69 rows at the deployed length, and
the reason the interpreter's `alphaPow` is a lookup rather than an exponentiation. -/
def alphaGo {F : Type} [Field F] [DecidableEq F] (alpha : FVar F) :
    Nat → FVar F → Array (FVar F) → CircuitM F (KimchiConstraint F) (Array (FVar F))
  | 0, _, acc => pure acc
  | n + 1, prev, acc => do
    let next ← Snarky.mul alpha prev
    alphaGo alpha n next (acc.push next)

open Pickles.Linearization in
/-- The precomputed table: `[1, α, α², …, α^70]`. -/
def precomputeAlphaPowers {F : Type} [Field F] [DecidableEq F] (alpha : FVar F) :
    CircuitM F (KimchiConstraint F) (Array (FVar F)) :=
  alphaGo alpha 69 alpha #[.const 1, alpha]

open Pickles.Linearization Kimchi.Protocol.Linearization in
/-- The interpreter's inputs from the 90-entry layout: `get i` is input `i`, `pows` the
precomputed α-table. -/
def linearizationInputs {p : ℕ} [Fact p.Prime] (get : ℕ → FVar (ZMod p))
    (pows : Array (FVar (ZMod p))) : Inputs (ZMod p) :=
  { evals :=
      { w i := get (2 * i)
        wOmega i := get (2 * i + 1)
        coeffs i := get (30 + 2 * i)
        z := get 60
        zOmega := get 61
        s i := get (62 + 2 * i)
        genericSelector := get 74
        poseidonSelector := get 76
        completeAddSelector := get 78
        mulSelector := get 80
        emulSelector := get 82
        endoScalarSelector := get 84 }
    alphaPows n := pows[n]?.getD (.const 0)
    beta := get 87
    gamma := get 88
    jointCombiner := .const 1
    vanishes := .const 1 }

open Pickles.Linearization Kimchi.Protocol.Linearization in
/-- The circuit under comparison, at either side: the domain generator (PS
`domainGenerator`, matching production's recorded `omega`), the endomorphism coefficient
and the MDS matrix all come from `side`. The `zkPoly` and `zeta^n - 1` terms are computed
and DISCARDED: they emit rows the OCaml dump contains, so they are part of the constraint
system being compared even though nothing reads them. -/
def linearizationCircuit {p : ℕ} [Fact p.Prime] (side : Kimchi.Fixture.PS.Side p)
    (domLog2 : Nat) (toks : Array PolishToken) (inputs : Vector (FVar (ZMod p)) 90) :
    CircuitM (ZMod p) (KimchiConstraint (ZMod p)) (FVar (ZMod p)) := do
  let get (i : Nat) : FVar (ZMod p) := inputs[i]?.getD (.const 0)
  let gen := side.omega (2 ^ domLog2)
  let om1 := gen⁻¹
  let om2 := om1 * om1
  let om3 := om2 * om1
  let alpha := get 86
  let zeta := get 89
  let pows ← precomputeAlphaPowers alpha
  -- eager zk_polynomial, discarded
  let t1 ← Snarky.mul (CVar.sub_ zeta (.const om1)) (CVar.sub_ zeta (.const om2))
  let _ ← Snarky.mul t1 (CVar.sub_ zeta (.const om3))
  -- eager zeta^n - 1, discarded
  let _ ← Snarky.pow zeta (2 ^ domLog2)
  evaluate ((linearizationInputs get pows).toEnv side.endo side.mds lookupZero (fun _ => false)
    (fun _ _ => pure (.const 0))) toks

/-! ## The ft_eval0 circuit

Transcribes `Pickles.CircuitDiffs.PureScript.FtEval0Common.ftEval0CircuitM`: the 90-input
linearization layout plus `p_eval0` at index 90, the same `scalars_env` prelude with the
`zkPoly` and `zeta^n − 1` rows now READ, and `Pickles.ftEval0Circuit` — the gadget the
faithfulness theorem is about — fed those as its upstream inputs. The domain is constant
in the dump, so `ω^{n − zkRows}` is the constant `ω⁻³` and the coset shifts are constants. -/

/-- The step-side coset shifts, production's Blake2b-sampled `Shifts::new` values (PS reads
them through `domainShifts`; recorded in `kimchi/fixtures/linearization_vesta{,_emul}.json`,
identical at both domain sizes there). They enter the dump as Generic coefficients, so the
comparison checks them against production rather than trusting them. -/
def stepShifts : Fin permCols → Fp := fun i =>
  (#[1, 328286983623303317637963920346571898945724874896624808297627776768640590563,
     91433028157768305433241271390810941046493237899366836746431422160024463706,
     240213425742950025341713987028051046476975246675775993287051503548513551377,
     417757293700961807788464308236931191792053554682199437460107260306038610067,
     430348682428487492383428014506756320686619984007091686553051322507181255952,
     326625242707153437805405281465150497418605074624614708160829052937679007395]
    : Array ℕ)[(i : ℕ)]?.getD 0

open Pickles.Linearization Kimchi.Protocol.Linearization in
/-- The `ft_eval0` circuit under comparison, at either side. -/
def ftEval0CsCircuit {p : ℕ} [Fact p.Prime] (side : Kimchi.Fixture.PS.Side p)
    (domLog2 : Nat) (toks : Array PolishToken) (shifts : Fin permCols → ZMod p)
    (inputs : Vector (FVar (ZMod p)) 91) :
    CircuitM (ZMod p) (KimchiConstraint (ZMod p)) (FVar (ZMod p)) := do
  let get (i : Nat) : FVar (ZMod p) := inputs[i]?.getD (.const 0)
  let gen := side.omega (2 ^ domLog2)
  let om1 := gen⁻¹
  let om2 := om1 * om1
  let om3 := om2 * om1
  let alpha := get 86
  let zeta := get 89
  let pows ← precomputeAlphaPowers alpha
  -- eager zk_polynomial
  let t1 ← Snarky.mul (CVar.sub_ zeta (.const om1)) (CVar.sub_ zeta (.const om2))
  let zkPoly ← Snarky.mul t1 (CVar.sub_ zeta (.const om3))
  -- eager zeta^n - 1
  let zetaToN ← Snarky.pow zeta (2 ^ domLog2)
  let ext : Pickles.PermInputs (ZMod p) :=
    { zeta := zeta
      pubEval := get 90
      zkPoly := zkPoly
      zetaToNMinus1 := CVar.sub_ zetaToN (.const 1)
      omegaZk := .const om3
      shifts := shifts }
  Pickles.ftEval0Circuit side.endo side.mds toks (fun _ => false) (fun _ _ => pure (.const 0))
    (linearizationInputs get pows) ext

/-! ## The combined inner product circuits

Transcribe `Pickles.CircuitDiffs.PureScript.Cip`: both sides of the check over the dumps'
layouts — two 16-entry previous-challenge vectors, `ζ`, `ζω`, `ξ`, `r`, `ft_eval0`,
`ft_eval1`, the public evaluations, and the 43-entry evaluation block at each point — around
the proved gadgets `Pickles.challengePolyEvals` and `Pickles.combinedInnerProduct`. The step side
has two proofs-verified mask booleans first and a Type1 claim; the wrap side no mask and a
Type2 claim. An entry's bit is the mask bit on the step side and the constant `true_` elsewhere,
which `selectField` folds to no row. -/

open Pickles in
/-- The shared body from `base` on: the challenge polynomials of both previous proofs at
`ζ` then `ζω`, the two batches, the gadget, and the equality with the unshifted claim. `sg`
pairs an `sg` evaluation with its bit: the mask on the step side, `true_` on the wrap side. -/
def cipCore {p : ℕ} [Fact p.Prime] (get : ℕ → FVar (ZMod p)) (base : ℕ)
    (sg : Fin 2 → FVar (ZMod p) → BoolVar (ZMod p) × FVar (ZMod p)) (expected : FVar (ZMod p)) :
    CircuitM (ZMod p) (KimchiConstraint (ZMod p)) PUnit := do
  let at_ (i : ℕ) : FVar (ZMod p) := get (base + i)
  let chals (j : ℕ) : List (FVar (ZMod p)) := (List.range 16).map fun k => at_ (16 * j + k)
  let evals (b : ℕ) : List (FVar (ZMod p)) := (List.range 43).map fun j => at_ (b + j)
  let zeta := at_ 32
  let zetaw := at_ 33
  let tagged (l : List (FVar (ZMod p))) : List (BoolVar (ZMod p) × FVar (ZMod p)) :=
    List.zipWith (fun (j : Fin 2) x => sg j x) [0, 1] l
  let sgZeta ← challengePolyEvals zeta [chals 0, chals 1]
  let sgZetaw ← challengePolyEvals zetaw [chals 0, chals 1]
  let actual ← combinedInnerProduct (at_ 34) (at_ 35)
    (buildEvalList (tagged sgZeta) (at_ 38) (at_ 36) (evals 40))
    (buildEvalList (tagged sgZetaw) (at_ 39) (at_ 37) (evals 83))
  let _ ← equals expected actual
  pure PUnit.unit

/-- `cip_step_circuit`: mask bits at 0–1 (unchecked, OCaml `Boolean.Unsafe.of_cvar`), the
shared layout from 2, the Type1 claim at 128. -/
def cipStepCircuit (input : Vector (FVar Fp) 129) : CircuitM Fp C PUnit :=
  let get (i : ℕ) : FVar Fp := input[i]?.getD (.const 0)
  cipCore get 2 (fun j x => (.unchecked (get j), x)) (Type1.fromShiftedCircuit 255 ⟨get 128⟩)

/-- `cip_wrap_circuit`: the shared layout from 0, no mask, the Type2 claim at 126. -/
def cipWrapCircuit (input : Vector (FVar Fq) 127) : CircuitM Fq Cq PUnit :=
  let get (i : ℕ) : FVar Fq := input[i]?.getD (.const 0)
  cipCore get 0 (fun _ x => (true_, x)) (Type2.fromShiftedCircuit 255 ⟨get 126⟩)

/-! ## The permutation scalar circuits

Transcribe `Pickles.CircuitDiffs.PureScript.PlonkChecksPassed`: the 18-input layout — `α`,
`β`, `γ`, `zkPolynomial`, `z(ζω)`, `σ₀…σ₅`, `w₀…w₅`, the claimed perm — with `α²¹` by `pow`
as the dump computes it, `Pickles.permScalarCircuit`, and the shifted comparison: the claim
against the Type1 encode of the scalar on the step side, the Type2 decode of the claim
against the scalar on the wrap side. -/

open Pickles in
/-- The shared body: `α²¹`, the scalar, and `compare claimed actual`. -/
def permCheckCore {p : ℕ} [Fact p.Prime] (input : Vector (FVar (ZMod p)) 18)
    (compare : FVar (ZMod p) → FVar (ZMod p) →
      CircuitM (ZMod p) (KimchiConstraint (ZMod p)) (BoolVar (ZMod p))) :
    CircuitM (ZMod p) (KimchiConstraint (ZMod p)) PUnit := do
  let get (i : ℕ) : FVar (ZMod p) := input[i]?.getD (.const 0)
  let a21 ← Snarky.pow (get 0) 21
  let actual ← permScalarCircuit (fun i => get (11 + i)) (fun i => get (5 + i)) (get 4) (get 1)
    (get 2) (get 3) a21
  let _ ← compare (get 17) actual
  pure PUnit.unit

/-- `plonk_checks_passed_step_circuit`: the Type1 claim against the encoded scalar. -/
def plonkChecksPassedStepCircuit (input : Vector (FVar Fp) 18) : CircuitM Fp C PUnit :=
  permCheckCore input fun claimed actual => equals claimed (Type1.ofFieldCircuit 255 actual)

/-- `plonk_checks_passed_wrap_circuit`: the decoded Type2 claim against the scalar. -/
def plonkChecksPassedWrapCircuit (input : Vector (FVar Fq) 18) : CircuitM Fq Cq PUnit :=
  permCheckCore input fun claimed actual => equals (Type2.fromShiftedCircuit 255 ⟨claimed⟩) actual

/-! ## The wrap column

The library gadgets the wrap-side dumps exercise, at `Fq`: the group map at Vesta's
parameters, and the linearization over the wrap token stream. -/

/-- The Vesta BW19 `setup()` parameters at the wrap field (PS
`groupMapParams (Proxy @VestaG)`): `Poseidon.GroupMapVesta.spec` with the same non-residue. -/
def groupMapParamsFq : GroupMapParams Fq := .ofSpec Poseidon.GroupMapVesta.spec 5

/-- `group_map_wrap_circuit` (the group-map gadget at the wrap field and Vesta parameters;
the dump carries no witness, so the advice is inert here). -/
def groupMapCircuitFq (input : FVar Fq) : CircuitM Fq Cq PUnit := do
  let _ ← groupMapCircuit (fun _ => none) groupMapParamsFq input
  pure ⟨⟩

/-- The corpus under comparison: the step column, then the wrap column. -/
def targets : List (String × (Json → Except String (Option (Bool × List (String × Bool))))) :=
  [ ("mul_step_circuit", stepTarget (a := Fp) (b := Fp) mulCircuit),
    ("inv_step_circuit", stepTarget (a := Fp) (b := Fp) invCircuit),
    ("div_step_circuit", stepTarget (a := Fp) (b := Fp) divCircuit),
    ("if_step_circuit", stepTarget (a := Fp) (b := Fp) ifCircuit),
    ("equals_step_circuit", stepTarget (a := Fp) (b := Bool) equalsCircuit),
    ("pow7_step_circuit", stepTarget (a := Fp) (b := Fp) pow7Circuit),
    ("pow8_step_circuit", stepTarget (a := Fp) (b := Fp) pow8Circuit),
    ("assert_equal_step_circuit", stepTarget (a := Fp) (b := PUnit) assertEqualCircuit),
    ("app_circuit_two_phase_chain_make_zero",
      stepTarget (a := Fp) (b := PUnit) makeZeroAppCircuit),
    ("app_circuit_two_phase_chain_increment",
      stepTarget (a := Fp) (b := PUnit) incrementAppCircuit),
    ("assert_square_step_circuit", stepTarget (a := Fp) (b := PUnit) assertSquareCircuit),
    ("assert_non_zero_step_circuit",
      stepTarget (a := Fp) (b := PUnit) assertNonZeroCircuit),
    ("assert_not_equal_step_circuit",
      stepTarget (a := Fp) (b := PUnit) assertNotEqualCircuit),
    ("unpack_step_circuit", stepTarget (a := Fp) (b := PUnit) unpackCircuit),
    ("bool_and_step_circuit", stepTarget (a := Bool) (b := Bool) boolAndCircuit),
    ("bool_or_step_circuit", stepTarget (a := Bool) (b := Bool) boolOrCircuit),
    ("bool_xor_step_circuit", stepTarget (a := Bool) (b := Bool) boolXorCircuit),
    ("bool_all_step_circuit", stepTarget (a := Bool) (b := Bool) boolAllCircuit),
    ("bool_any_step_circuit", stepTarget (a := Bool) (b := Bool) boolAnyCircuit),
    ("bool_assert_step_circuit", stepTarget (a := Bool) (b := PUnit) boolAssertCircuit),
    ("add_complete_step_circuit",
      stepTarget (a := AffinePoint Fp × AffinePoint Fp) (b := AffinePoint Fp)
        addCompleteCircuit),
    ("poseidon_step_circuit",
      stepTarget (a := Vector Fp 3) (b := Vector Fp 3) poseidonCircuit),
    ("endo_scalar_step_circuit",
      stepTarget (a := Fp) (b := Fp) endoScalarCircuit),
    ("endo_mul_step_circuit",
      stepTarget (a := AffinePoint Fp × Fp) (b := AffinePoint Fp) endoMulCircuit),
    ("var_base_mul_step_circuit",
      stepTarget (a := AffinePoint Fp × Fp) (b := AffinePoint Fp) varBaseMulCircuit),
    ("scale_fast2_128_step_circuit",
      stepTarget (a := AffinePoint Fp × Fp) (b := AffinePoint Fp) scaleFast2_128Circuit),
    ("group_map_step_circuit",
      stepTarget (a := Fp) (b := PUnit) groupMapCircuitFp),
    ("pow2_pow_step_circuit", stepTarget (a := Vector Fp 1) (b := PUnit) pow2PowCircuit),
    ("b_correct_step_circuit",
      stepTarget (a := Vector Fp 20) (b := PUnit) bCorrectCircuit),
    ("bullet_reduce_one_step_circuit",
      stepTarget (a := Vector Fp 5) (b := PUnit) bulletReduceOneCircuit),
    ("linearization_step_circuit",
      stepTarget (a := Vector Fp 90) (b := Fp)
        (linearizationCircuit Kimchi.Fixture.PS.fpSide 16 Pickles.Linearization.fpTokens)),
    ("bullet_reduce_step_circuit",
      stepTarget (a := Vector Fp 75) (b := PUnit) bulletReduceCircuit),
    ("ft_eval0_step_circuit",
      stepTarget (a := Vector Fp 91) (b := Fp)
        (ftEval0CsCircuit Kimchi.Fixture.PS.fpSide 16 Pickles.Linearization.fpTokens
          stepShifts)),
    ("cip_step_circuit", stepTarget (a := Vector Fp 129) (b := PUnit) cipStepCircuit),
    ("plonk_checks_passed_step_circuit",
      stepTarget (a := Vector Fp 18) (b := PUnit) plonkChecksPassedStepCircuit),
    -- the wrap column
    ("group_map_wrap_circuit", wrapTarget (a := Fq) (b := PUnit) groupMapCircuitFq),
    ("linearization_wrap_circuit",
      wrapTarget (a := Vector Fq 90) (b := Fq)
        (linearizationCircuit Kimchi.Fixture.PS.fqSide 15 Pickles.Linearization.fqTokens)),
    ("cip_wrap_circuit", wrapTarget (a := Vector Fq 127) (b := PUnit) cipWrapCircuit),
    ("b_correct_wrap_circuit", wrapTarget (a := Vector Fq 20) (b := PUnit) bCorrectWrapCircuit),
    ("plonk_checks_passed_wrap_circuit",
      wrapTarget (a := Vector Fq 18) (b := PUnit) plonkChecksPassedWrapCircuit) ]

def main : IO Unit := do
  let dir ← resultsDir
  let mut failures := 0
  for (name, compare) in targets do
    let path := dir / s!"{name}.json"
    let raw ← IO.FS.readFile path
    match Json.parse raw >>= compare with
    | .error e =>
      failures := failures + 1
      IO.println s!"✗ {name}: parse error: {e}"
    | .ok none =>
      failures := failures + 1
      IO.println s!"✗ {name}: not a comparison dump"
    | .ok (some (witnessLess, checks)) =>
      let bad := checks.filter (!·.2)
      if bad.isEmpty then
        let note := if witnessLess then "  (CS-side only: witness-less dump)" else ""
        IO.println s!"✓ {name}{note}"
      else
        failures := failures + 1
        IO.println s!"✗ {name}: {String.intercalate ", " (bad.map (·.1))}"
  if failures > 0 then
    throw <| IO.userError s!"CS-equality FAILED ({failures} circuit(s))"
  IO.println s!"── CS equality OK ({targets.length} circuits) ──"
