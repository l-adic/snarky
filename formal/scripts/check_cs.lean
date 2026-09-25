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

Harness rule, the same as the PureScript side's (`Common.purs`): a target lays out the
dump's inputs and calls the LIBRARY circuits (`Pickles.*`, `Snarky.*`) on them, never a
re-implementation written here — the point is to prove the library circuits equivalent,
so a library change must surface as a mismatch rather than be absorbed by the harness.
Native constant folding (generators, their powers, endomorphism coefficients) is not
circuit logic.

The circuits transcribe `Test.Pickles.CircuitDiffs.Main`
(packages/pickles-circuit-diffs/test/): every witness-carrying circuit built from the
`Basic` gadget vocabulary, the landed gate gadgets (poseidon, endo_scalar,
endo_mul), the gadget-complete pickles sub-circuits (pow2_pow, b_correct,
bullet_reduce_one_step, bullet_reduce_step — composition fixtures, the bullet pair
composing endoInv + endoMul + addComplete; their dumps are witness-less, so the
checks are CS-side only), ft_eval0_step (the proved `Pickles.ftEval0Circuit` under
the linearization prelude, against the PS `FtEval0Common` harness), and cip_{step,wrap}
(the proved `Pickles.combinedInnerProduct` over `Pickles.bPolyCircuit`, against the PS
`Cip` harness — the wrap column's first pickles sub-circuit), and the scalar side's
remaining slices through to finalize_other_proof_{step,wrap} (the permutation scalar,
expand_plonk, the challenge digests, the fr-sponge schedule, and the whole assembled
`Pickles.finalizeOtherProofStep`/`Wrap` against the PS `FopStep`/`FopWrap` harnesses).
and xhat_{wrap,step} (the public-input-commitment MSM on either side —
`Pickles.publicInputCommitFull` against the PS `Xhat` harness, `Pickles.publicInputCommitKnown`
against `XhatStep` — with the Lagrange bases loaded from the circuit-diffs exports and the
shift corrections derived by `smulFast`), and ftcomm_{step,wrap} (the proved
`Pickles.ftComm` at either side's `IpaScalarOps`, against the PS `FtcommStep`/`Ftcomm`
harnesses), and ivp_step (the whole group half, `Pickles.incrementallyVerifyProof` on the
step side against the PS `IvpStep` harness, its Lagrange bases from the circuit-diffs
export). Deferred, with the blocker each waits on:
- verify, ivp_wrap, wrap/step mains — the pickles buildout;
- hash_messages_*, schnorr_verify — the sponge circuit layer
  (packages/random-oracle);
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
import BulletproofFixture
import Snarky
import Snarky.Kimchi.Backend.Compile
import Pickles.Linearization.Circuit
import Pickles.FtEval0
import Pickles.IPA
import Pickles.CombinedInnerProduct
import Pickles.PermScalar
import Pickles.FrSponge
import Pickles.FinalizeOtherProof
import Pickles.FqSpongeTranscript
import Pickles.CheckBulletproof
import Pickles.PublicInputCommit
import Pickles.FtComm
import Pickles.IncrementallyVerify
import Pickles.Verify
import Pickles.VerifyOne
import Pickles.StepMain
import CompElliptic.Curves.Pasta.Fast.Projective.Core
import Pickles.Linearization.Fp
import Pickles.Linearization.Fq
import Pickles.MessageHash
import Pickles.WrapVerify
import Pickles.WrapFinalize
import Pickles.WrapMain
import Snarky.Kimchi.Circuit.AddComplete
import Snarky.Kimchi.Circuit.GroupMap
import Snarky.Kimchi.Circuit.Poseidon
import Snarky.Kimchi.Circuit.EndoScalar
import Snarky.Kimchi.Circuit.EndoMul
import Snarky.Kimchi.Circuit.VarBaseMul
import Poseidon.Basic
import Pasta.Endo
import PicklesFixture

open Lean Snarky Snarky.Kimchi Kimchi Kimchi.Index Kimchi.Fixture.PS CompElliptic.Fields.Pasta
open PicklesFixture

/-- Where the circuit-diffs results live (workspace-relative default, env override). -/
def resultsDir : IO System.FilePath := do
  match (← IO.getEnv "KIMCHI_PS_RESULTS_DIR") with
  | some d => return d
  | none =>
    return ".." / "packages" / "pickles-circuit-diffs" / "circuits" / "results"

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

/-- `poseidon_step_circuit` (the PS gadget `Snarky.Circuit.Kimchi.Poseidon.poseidon`
at the step field's parameters; the PS `Vector 3` interface renders as the gadget's
`SpongeState` at the boundary). -/
def poseidonCircuit (s : Vector (FVar Fp) 3) : CircuitM Fp C (Vector (FVar Fp) 3) := do
  let r ← poseidon Poseidon.fpParams ⟨s[0], s[1], s[2]⟩
  pure #v[r.s0, r.s1, r.s2]

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

/-- `group_map_step_circuit` (the PS gadget
`Snarky.Circuit.Kimchi.GroupMap.groupMapCircuit` at the step field and Pallas
parameters; the dump carries no witness, so the advice is inert here). -/
def groupMapCircuitFp (input : FVar Fp) : CircuitM Fp C PUnit := do
  let _ ← groupMapCircuit (fun _ => none) Pickles.groupMapParamsPallas input
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
  let pows ← Pickles.Linearization.precomputeAlphaPowers alpha
  -- eager zk_polynomial at constant powers, discarded
  let _ ← Pickles.zkPolynomial zeta ⟨.const om1, .const om2, .const om3⟩
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
  let pows ← Pickles.Linearization.precomputeAlphaPowers alpha
  -- eager zk_polynomial at constant powers
  let zkPoly ← Pickles.zkPolynomial zeta ⟨.const om1, .const om2, .const om3⟩
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
  let chals := prevChallengesOf at_ 0
  let evals (b : ℕ) : List (FVar (ZMod p)) := (List.range 43).map fun j => at_ (b + j)
  let zeta := at_ 32
  let zetaw := at_ 33
  let tagged (l : List (FVar (ZMod p))) : List (BoolVar (ZMod p) × FVar (ZMod p)) :=
    List.zipWith (fun (j : Fin 2) x => sg j x) [0, 1] l
  let sgZeta ← challengePolyEvals zeta chals
  let sgZetaw ← challengePolyEvals zetaw chals
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

/-! ## The challenge expansion circuits

Transcribe `Pickles.CircuitDiffs.PureScript.ExpandPlonk`: `α` at 0 and `ζ` at 3 expanded
through `EndoScalar.toField` at the side's scalar endomorphism, `β`, `γ` untouched, then
`ζω = ω · ζ` at the side's constant generator, which folds to no row. -/

/-- The shared body at a side's endomorphism and generator. -/
def expandPlonkCore {p : ℕ} [Fact p.Prime] (endo gen : ZMod p) (input : Vector (FVar (ZMod p)) 4) :
    CircuitM (ZMod p) (KimchiConstraint (ZMod p)) PUnit := do
  let endoVar : FVar (ZMod p) := .const endo
  let _ ← EndoScalar.toField 8 input[0] endoVar
  let zeta ← EndoScalar.toField 8 input[3] endoVar
  let _ ← mul (.const gen) zeta
  pure PUnit.unit

/-- `expand_plonk_step_circuit`. -/
def expandPlonkStepCircuit (input : Vector (FVar Fp) 4) : CircuitM Fp C PUnit :=
  expandPlonkCore endoVestaLam (Kimchi.Fixture.PS.fpSide.omega (2 ^ 16)) input

/-- `expand_plonk_wrap_circuit`. -/
def expandPlonkWrapCircuit (input : Vector (FVar Fq) 4) : CircuitM Fq Cq PUnit :=
  expandPlonkCore endoPallasLam (Kimchi.Fixture.PS.fqSide.omega (2 ^ 15)) input

/-! ## The Pseudo selection circuits

Transcribe `Pickles.CircuitDiffs.PureScript.PseudoCircuits`: `Pickles.oneHotVector` of input 0,
`Pickles.Pseudo.mask` and `Pickles.Pseudo.choose` behind it, on either field, and
`Pickles.toDomain` over the three wrap domains with the selected vanishing polynomial at
input 1. -/

section PseudoCircuits

variable {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]

/-- `one_hot_n{n}`: the one-hot vector of input 0 over `n` entries. -/
def oneHotCircuit (n : ℕ) (input : Vector (FVar F) 1) : CircuitM F c PUnit := do
  let _ ← Pickles.oneHotVector n input[0]
  pure PUnit.unit

/-- `pseudo_mask_n{n}`: the one-hot of input 0 over `n` entries masking `xs input`. -/
def pseudoMaskCircuit {k : ℕ} (n : ℕ) (xs : Vector (FVar F) (k + 1) → List (FVar F))
    (input : Vector (FVar F) (k + 1)) : CircuitM F c PUnit := do
  let bits ← Pickles.oneHotVector n input[0]
  let _ ← Pickles.Pseudo.mask bits (xs input)
  pure PUnit.unit

/-- `pseudo_choose_n{n}`: the one-hot of input 0 over `n` entries choosing among the constants
`ks`. -/
def pseudoChooseCircuit (n : ℕ) (ks : List ℕ) (input : Vector (FVar F) 1) :
    CircuitM F c PUnit := do
  let bits ← Pickles.oneHotVector n input[0]
  let _ ← Pickles.Pseudo.choose bits ks fun k => .const (k : F)
  pure PUnit.unit

end PseudoCircuits

/-- `pseudo_to_domain_wrap_circuit`: the one-hot of input 0 over the wrap domains `2^13`,
`2^14`, `2^15`, and the selected domain's vanishing polynomial at input 1. -/
def pseudoToDomainWrapCircuit (input : Vector (FVar Fq) 2) : CircuitM Fq Cq PUnit := do
  let which ← Pickles.oneHotVector 3 input[0]
  let d ← Pickles.toDomain (fun l => Kimchi.Fixture.PS.fqSide.omega (2 ^ l)) which
    [13, 14, 15]
  let _ ← d.vanishingPolynomial input[1]
  pure PUnit.unit

/-! ## The wrap circuit's branch selection

Transcribe `Pickles.CircuitDiffs.PureScript.PseudoCircuits`' `utils_ones_vector_n16` (the slot
mask, `Pickles.onesVector`, on either field) and `choose_key_n1_wrap` (`Pickles.chooseKey` over
one branch whose key is Vesta's generator `(1, √6)` in every commitment). -/

/-- `utils_ones_vector_n16`: the mask over 16 slots, the first zero at input 0. -/
def onesVectorN16Circuit {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]
    (input : Vector (FVar F) 1) : CircuitM F c PUnit := do
  let _ ← Pickles.onesVector input[0] 16
  pure PUnit.unit

/-- `choose_key_n1_wrap_circuit`: the one-hot of input 0 over one branch choosing its key. -/
def chooseKeyN1WrapCircuit (input : Vector (FVar Fq) 1) : CircuitM Fq Cq PUnit := do
  let bits ← Pickles.oneHotVector 1 input[0]
  let g : AffinePoint (FVar Fq) :=
    ⟨.const 1,
      .const 11426906929455361843568202299992114520848200991084027513389447476559454104162⟩
  let ch : Vector (AffinePoint (FVar Fq)) 1 := #v[g]
  let key : Pickles.VkComms 1 (AffinePoint (FVar Fq)) :=
    ⟨Vector.replicate _ ch, Vector.replicate _ ch, ch, ch, ch, ch, ch, ch⟩
  let _ ← Pickles.chooseKey (Vector.ofFn fun i => bits.getD i.val true_) #v[key]
  pure PUnit.unit

/-! ## The evaluation layout

The evaluation record as the dumps lay it out, shared by the `finalize_other_proof` targets
below. The PS harnesses' fr-sponge slices (`SpongeChallenges`: the challenge digests and the
schedule with `ξ`, `r`) are strict sub-circuits of those targets, so their byte-equality is
checked there rather than as separate interpreter passes. -/

/-! ## The fq-sponge transcript circuit

Transcribes `Pickles.CircuitDiffs.PureScript.FqSpongeTranscript`: the group side's
Fiat–Shamir schedule of `incrementally_verify_proof`, `Pickles.fqSpongeTranscript` at the
step field's sponge and range-check endomorphism over the 53-input layout, `x_hat` handed in
as the input point. -/

/-- `fq_sponge_transcript_step_circuit`: the index digest at 0, two `sg_old` points at 1–4,
`x_hat` at 5–6, the 15 `w_comm` points at 7–36, `z_comm` at 37–38, the 7 `t_comm` points at
39–52. -/
def fqSpongeTranscriptStepCircuit (input : Vector (FVar Fp) 53) : CircuitM Fp C PUnit := do
  let get (i : ℕ) : FVar Fp := input[i]?.getD (.const 0)
  let pt (i : ℕ) : AffinePoint (FVar Fp) := ⟨get i, get (i + 1)⟩
  let _ ← Pickles.fqSpongeTranscript Bulletproof.IpaVesta.curve.frSponge.params
    (.const endoVestaLam)
    (get 0) [pt 1, pt 3] (pure [pt 5]) ((List.range 15).map fun j => [pt (7 + 2 * j)]) [pt 37]
    ((List.range 7).map fun j => pt (39 + 2 * j))
  pure PUnit.unit


/-- `fq_sponge_transcript_wrap_circuit`: the two mask bits at 0–1, the index digest at 2, two
`sg_old` points at 3–6, `x_hat` at 7–8, the 15 `w_comm` points at 9–38, `z_comm` at 39–40, the
7 `t_comm` points at 41–54. -/
def fqSpongeTranscriptWrapCircuit (input : Vector (FVar Fq) 55) : CircuitM Fq Cq PUnit := do
  let get (i : ℕ) : FVar Fq := input[i]?.getD (.const 0)
  let pt (i : ℕ) : AffinePoint (FVar Fq) := ⟨get i, get (i + 1)⟩
  let _ ← Pickles.fqSpongeTranscriptOpt Bulletproof.IpaPallas.curve.frSponge.params
    (.const endoPallasLam) (get 2) [(.unchecked (get 0), pt 3), (.unchecked (get 1), pt 5)] [pt 7]
    ((List.range 15).map fun j => [pt (9 + 2 * j)]) [pt 39]
    ((List.range 7).map fun j => pt (41 + 2 * j))
  pure PUnit.unit

/-! ## The `check_bulletproof` circuits

Transcribe `Pickles.CircuitDiffs.PureScript.CheckBulletproofStep` and `CheckBulletproofWrap`:
`Pickles.checkBulletproof` from a sponge at `sponge_before_evaluations` on either side,
the step side at `IpaScalarOps.step`/`IpaEndo.pallas` over the 170-input layout, the wrap
side at `IpaScalarOps.wrap`/`IpaEndo.vesta` over the 172-input layout with the two `sg_old`
bases under their mask bits. The SRS blinding base `h` is a constant on both sides, as in
production. -/

/-- The SRS blinding base `h` of a fixture (`srs_h`, the same production SRS the IPA
fixture checks read), as a constant point. -/
def blindingBase (C : Bulletproof.Ipa.KimchiCurve) (path : System.FilePath) :
    IO (AffinePoint (FVar (ZMod C.base))) := do
  let raw ← IO.FS.readFile path
  match Json.parse raw >>= fun j => j.getObjVal? "srs_h" >>= Bulletproof.Fixture.parsePt C with
  | .ok P => return ⟨.const P.x, .const P.y⟩
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- `check_bulletproof_step_circuit`: the sponge state at 0–2 (`Squeezed 1`), `ξ` at 3, the
47 bases at 4–97 (unmasked), the 15 `(L, R)` pairs at 98–157, `δ` at 158, `sg` at 160, then
`z₁`, `z₂`, `cip`, `b` as `(sDiv2, sOdd)` pairs at 162–169. -/
def checkBulletproofStepCircuit (blindingH : AffinePoint (FVar Fp)) (input : Vector (FVar Fp) 170) :
    CircuitM Fp C PUnit := do
  let get (i : ℕ) : FVar Fp := input[i]?.getD (.const 0)
  let pt (i : ℕ) : AffinePoint (FVar Fp) := ⟨get i, get (i + 1)⟩
  let shifted (i : ℕ) : Type2 (SplitField (FVar Fp) (BoolVar Fp)) :=
    ⟨⟨get i, .unchecked (get (i + 1))⟩⟩
  let sv : SpongeVar Fp := ⟨⟨get 0, get 1, get 2⟩, .squeezed 1⟩
  let _ ← Pickles.checkBulletproof Pickles.IpaScalarOps.step Pickles.IpaEndo.pallas
    Bulletproof.IpaVesta.curve.frSponge.params (.const endoVestaLam) Pickles.groupMapParamsPallas
    (fun _ => none) sv
    ((List.range 47).map fun j => (pt (4 + 2 * j), none))
    { xi := ⟨get 3⟩
      deferred := { combinedInnerProduct := shifted 166, b := shifted 168 }
      opening := { lr := Vector.ofFn (n := 15) fun j => (pt (98 + 4 * j), pt (100 + 4 * j))
                   z1 := shifted 162, z2 := shifted 164, delta := pt 158, sg := pt 160 }
      blindingGenerator := blindingH }
  pure PUnit.unit

/-! ## The `finalize_other_proof` circuits

Transcribe `Pickles.CircuitDiffs.PureScript.FopStep` and `FopWrap`: the whole scalar-side
check on either side, `Pickles.finalizeOtherProofStep` at the step field's parameters over the
151-input layout and `Pickles.finalizeOtherProofWrap` at the wrap field's over the 148-input
layout, the wrap side's vanishing polynomial by `pow2PowMul` as the PS harness passes it. -/

/-- `finalize_other_proof_step_circuit` as a comparison target: the harness, output
discarded. -/
def finalizeOtherProofStepCircuit (input : Vector (FVar Fp) 151) : CircuitM Fp C PUnit := do
  let _ ← fopStepHarness input
  pure PUnit.unit

open Pickles Kimchi.Verifier in
/-- The step side over the chunked flat layout at `nc` chunks: the 151-cell layout with each
evaluation widened to its chunks — from 29, 44 columns of `2 · nc` cells (the `ζ` chunks, then
the `ζω` chunks) in the order public, `w`, coefficients, `z`, `σ`, the six selectors — then
`ft(ζω)`, the two previous-challenge vectors and the digest before evaluations. `zk_rows`
follows the chunk count. At `nc = 1` this is the 151-cell layout. -/
def fopStepChunkedHarnessAt (nc : ℕ) (domains : List (Pickles.KnownDomain Fp)) {n : ℕ}
    (input : Vector (FVar Fp) n) : CircuitM Fp C (Pickles.FopOutput Fp) := do
  let get (i : ℕ) : FVar Fp := input[i]?.getD (.const 0)
  let column (k : ℕ) : PointEvaluations (Vector (FVar Fp) nc) :=
    ⟨Vector.ofFn fun c => get (29 + 2 * nc * k + c),
     Vector.ofFn fun c => get (29 + 2 * nc * k + nc + c)⟩
  let tail := 29 + 88 * nc
  let (u, _, _) := PicklesFixture.fopInputsOf Type1.mk get 29
  let u := { u with spongeDigestBeforeEvaluations := get (tail + 33) }
  let w : ChunkedEvals nc (FVar Fp) :=
    { ftEval1 := get tail
      pub := column 0
      evals :=
        { w := Vector.ofFn fun j => column (1 + j)
          coefficients := Vector.ofFn fun j => column (16 + j)
          z := column 31
          s := Vector.ofFn fun j => column (32 + j)
          genericSelector := column 38
          poseidonSelector := column 39
          completeAddSelector := column 40
          mulSelector := column 41
          emulSelector := column 42
          endomulScalarSelector := column 43 } }
  Pickles.finalizeOtherProofStep
    { PicklesFixture.fopStepParams with zkRows := (16 * nc + 5) / 7 }
    domains u w [.unchecked (get 26), .unchecked (get 27)]
    (PicklesFixture.prevChallengesOf get (tail + 1))
    (get 28)

/-- `finalize_other_proof_chunks2_step_circuit`: the dump's 239 cells at two chunks and one
known domain of `log2 = 16`. -/
def fopStepChunks2Harness (input : Vector (FVar Fp) 239) :
    CircuitM Fp C (Pickles.FopOutput Fp) :=
  fopStepChunkedHarnessAt 2 [⟨16, Kimchi.Fixture.PS.fpSide.omega (2 ^ 16)⟩] input

/-- `finalize_other_proof_chunks2_step_circuit` as a comparison target: the step side over
a two-chunk step proof, output discarded. -/
def finalizeOtherProofChunks2StepCircuit (input : Vector (FVar Fp) 239) :
    CircuitM Fp C PUnit := do
  let _ ← fopStepChunks2Harness input
  pure PUnit.unit

/-- `finalize_other_proof_wrap_circuit` as a comparison target: the harness, output
discarded. -/
def finalizeOtherProofWrapCircuit (input : Vector (FVar Fq) 148) : CircuitM Fq Cq PUnit := do
  let _ ← fopWrapHarness input
  pure PUnit.unit

/-- `wrap_finalize_n2_circuit`: `Pickles.wrapFinalizePrevProofs` at two branches and two
slots. Input 0 is the branch index; slot `i`'s 145-cell finalize input at the wrap circuit's
15 rounds starts at `1 + 147 i`, followed by its `shouldFinalize` and its wrap domain index.
Branch 0's slots are pinned to domain indices `[1, 1]`, branch 1's to `[0, 2]`. -/
def wrapFinalizeN2Circuit (input : Vector (FVar Fq) 295) : CircuitM Fq Cq PUnit := do
  let get (i : ℕ) : FVar Fq := input[i]?.getD (.const 0)
  let bits ← Pickles.oneHotVector 2 (get 0)
  let whichBranch : Vector (BoolVar Fq) 2 := Vector.ofFn fun i => bits.getD i.val true_
  let slot (i : ℕ) (pins : Vector (Option ℕ) 2) : Pickles.WrapFinalizeSlot 2 15 1 Fq :=
    let off := 1 + 147 * i
    let (u, w, _) := fopInputsOf Type2.mk (fun j => get (off + j)) 25 15
    { domainIndex := get (off + 146), pins
      unfinalized := { u with shouldFinalize := .unchecked (get (off + 145)) }
      evals := w
      prevChallenges := Vector.ofFn fun a => Vector.ofFn fun r => get (off + 114 + 15 * a + r) }
  let _ ← Pickles.wrapFinalizePrevProofs fopWrapParams
    (fun l => Kimchi.Fixture.PS.fqSide.omega (2 ^ l)) whichBranch
    #v[slot 0 #v[some 1, some 0], slot 1 #v[some 1, some 2]]
  pure PUnit.unit

/-! ## The wrap column

The library gadgets the wrap-side dumps exercise, at `Fq`: the group map at Vesta's
parameters, and the linearization over the wrap token stream. -/

/-- `group_map_wrap_circuit` (the group-map gadget at the wrap field and Vesta parameters;
the dump carries no witness, so the advice is inert here). -/
def groupMapCircuitFq (input : FVar Fq) : CircuitM Fq Cq PUnit := do
  let _ ← groupMapCircuit (fun _ => none) Pickles.groupMapParamsVesta input
  pure ⟨⟩

/-- `check_bulletproof_wrap_circuit`: the sponge state at 0–2 (`Squeezed 1`), `ξ` at 3, the
two mask bits at 4–5, the 47 bases at 6–99 (the two `sg_old` under the mask), the 16
`(L, R)` pairs at 100–163, `δ` at 164, `sg` at 166, then `z₁`, `z₂`, `cip`, `b` at 168–171. -/
def checkBulletproofWrapCircuit (blindingH : AffinePoint (FVar Fq)) (input : Vector (FVar Fq) 172) :
    CircuitM Fq Cq PUnit := do
  let get (i : ℕ) : FVar Fq := input[i]?.getD (.const 0)
  let pt (i : ℕ) : AffinePoint (FVar Fq) := ⟨get i, get (i + 1)⟩
  let sv : SpongeVar Fq := ⟨⟨get 0, get 1, get 2⟩, .squeezed 1⟩
  let bases : List (AffinePoint (FVar Fq) × Option (BoolVar Fq)) :=
    [(pt 6, some (.unchecked (get 4))), (pt 8, some (.unchecked (get 5)))]
      ++ (List.range 45).map fun j => (pt (10 + 2 * j), none)
  let _ ← Pickles.checkBulletproof Pickles.IpaScalarOps.wrap Pickles.IpaEndo.vesta
    Bulletproof.IpaPallas.curve.frSponge.params (.const endoPallasLam) Pickles.groupMapParamsVesta
    (fun _ => none) sv
    bases
    { xi := ⟨get 3⟩
      deferred := { combinedInnerProduct := ⟨get 170⟩, b := ⟨get 171⟩ }
      opening := { lr := Vector.ofFn (n := 16) fun j => (pt (100 + 4 * j), pt (102 + 4 * j))
                   z1 := ⟨get 168⟩, z2 := ⟨get 169⟩, delta := pt 164, sg := pt 166 }
      blindingGenerator := blindingH }
  pure PUnit.unit

/-! ## The public-input commitment (`x_hat`)

The wrap-side `x_hat` MSM (`Pickles.publicInputCommitFull`) against the PS `Xhat` harness's
`xhat_wrap_circuit`. The 34 Vesta Lagrange bases and blinding `h` are SRS constants Lean
cannot compute; they arrive in `xhat_wrap_lagrange.json` (the circuit-diffs export). The
per-leaf shift corrections `-(2^L)·base` are derived HERE via CompElliptic's `smulFast`, so
only the bases are dumped. Packing (`Pickles.PackedStepPublicInput 1 15` walked by the
`PublicInputCommit` typeclass, through nested tuples — no field reorder) fixes the leaf
order: for `i = 0..33`, input `i` is leaf `i`'s scalar/bit and Lagrange base `i` its base,
with `full` (255-bit) at {0,2,4,6,8,10,32,33}, `condAdd` (the five shifted-scalar parities and
`should_finalize`) at {1,3,5,7,9,31}, `b128` at {11..30}. The six `condAdd` bits carry the
packing's booleanity checks, emitted (in walk order) before the gadget. -/

/-- The Vesta curve of the `x_hat` Lagrange bases (Fq coordinates). -/
abbrev XhatCurve := Bulletproof.IpaVesta.curve

open CompElliptic.Curves.Pasta.Fast.Projective.Core.PPoint in
/-- The shift correction `-(2^L)·P` at a Lagrange base chunk `P`, as a constant point:
`smulFast` computes `[2^L]·P` (the ladder shift `L = 5·chunks`), negated coordinatewise
(`(x, -y)` on `y² = x³ + 5`). Matches PS `scalarMulLeaf`'s `-pow2pow(base, 5·nChunks)`. -/
def xhatCorr (L : ℕ) (P : XhatCurve.Point) : AffinePoint (FVar Fq) :=
  let Q := smulFast XhatCurve.E (by decide) (by decide) (2 ^ L) P
  ⟨.const Q.x, .const (-Q.y)⟩

/-- A Lagrange base chunk `P` as a constant point. -/
def xhatBase (P : XhatCurve.Point) : AffinePoint (FVar Fq) := ⟨.const P.x, .const P.y⟩

/-- `xhat_wrap_circuit` (one chunk) and `xhat_wrap_chunks2_circuit` (two):
`Pickles.publicInputCommitFull` over the 34-leaf list — the boolean leaves constrain their own
bits inside the gadget — `full` at {0,2,4,6,8,10,32,33} (`L = 255`), `b128` at {11..30}
(`L = 130`), `condAdd` at {1,3,5,7,9,31}; leaf `i` reads input `i` and Lagrange base `pts[i]`,
at `nc` chunks. -/
def xhatWrapCircuit {nc : ℕ} (pts : Array (Vector XhatCurve.Point nc))
    (h : AffinePoint (FVar Fq)) (input : Vector (FVar Fq) 34) : CircuitM Fq Cq PUnit := do
  let get (i : ℕ) : FVar Fq := input[i]?.getD (.const 0)
  let pt (i : ℕ) : Vector XhatCurve.Point nc :=
    pts[i]?.getD (Vector.replicate nc (CompElliptic.CurveForms.ShortWeierstrass.SWPoint.zero
      XhatCurve.E))
  let base (i : ℕ) := (pt i).map xhatBase
  let full (i : ℕ) : Pickles.Leaf Fq nc := .full (get i) (base i) ((pt i).map (xhatCorr 255))
  let b128 (i : ℕ) : Pickles.Leaf Fq nc := .b128 (get i) (base i) ((pt i).map (xhatCorr 130))
  let cond (i : ℕ) : Pickles.Leaf Fq nc := .condAdd (.unchecked (get i)) (base i)
  let leaves : List (Pickles.Leaf Fq nc) :=
    [ full 0, cond 1, full 2, cond 3, full 4, cond 5, full 6, cond 7, full 8, cond 9, full 10 ]
      ++ (List.range 20).map (fun j => b128 (11 + j))
      ++ [ cond 31, full 32, full 33 ]
  let _ ← Pickles.publicInputCommitFull h leaves
  pure PUnit.unit

/-- `xhat_wrap_branches_{same,diff}_circuit`: input 0 is the branch index over two branches,
inputs 1–34 are `xhat_wrap_circuit`'s, committed by `Pickles.publicInputCommitMasked` over the
branches' Lagrange bases `pts0`/`pts1`, `shared` when the branches share one step domain. -/
def xhatBranchesCircuit (shared : Bool) (pts0 pts1 : Array XhatCurve.Point)
    (h : AffinePoint (FVar Fq)) (input : Vector (FVar Fq) 35) : CircuitM Fq Cq PUnit := do
  let bits ← Pickles.oneHotVector 2 input[0]
  let get (i : ℕ) : FVar Fq := input[i + 1]?.getD (.const 0)
  let full (i : ℕ) : Pickles.PackedScalar Fq := .full (get i)
  let b128 (i : ℕ) : Pickles.PackedScalar Fq := .b128 (get i)
  let cond (i : ℕ) : Pickles.PackedScalar Fq := .bit (.unchecked (get i))
  let ks := [ full 0, cond 1, full 2, cond 3, full 4, cond 5, full 6, cond 7, full 8, cond 9,
      full 10 ] ++ (List.range 20).map (fun j => b128 (11 + j)) ++ [ cond 31, full 32, full 33 ]
  let _ ← Pickles.publicInputCommitMasked (C := XhatCurve) shared h bits ks
    [pts0.toList.map (#v[·]), pts1.toList.map (#v[·])]
  pure PUnit.unit

/-! ## The wrap circuits (`wrap_main_*`)

`Pickles.wrapMain` at each dump's branches, slots and chunks, its config from
`<name>_constants.json` (the circuit-diffs export): the branches' slot counts, step domains
and step keys, the Lagrange bases per public-input scalar and branch, the blinding `h`, the
wrap domain pins (`-1` for a side-loaded slot), the slot widths and the padding challenges. -/

/-- The constants a `wrap_main_*` circuit bakes in, at `nc` step chunks. -/
structure WrapMainConsts (nc : ℕ) where
  /-- Each branch's slot count. -/
  stepWidths : List ℕ
  /-- Each branch's step domain, `log2`. -/
  domainLog2s : List ℕ
  /-- Each branch's step key. -/
  keys : List (Pickles.VkComms nc (AffinePoint (FVar Fq)))
  /-- Per public-input scalar, each branch's Lagrange base. -/
  lagrange : Array (List (Vector XhatCurve.Point nc))
  /-- The blinding base. -/
  h : XhatCurve.Point
  /-- Per branch, each slot's wrap domain index, `-1` when side-loaded. -/
  pins : List (List Int)
  /-- Each slot's challenge-stack height. -/
  slotWidths : List ℕ
  /-- The padding challenge vector. -/
  dummy : List Fq

/-- `<name>_constants.json`, parsed at `nc` step chunks. -/
def wrapMainConsts (nc : ℕ) (path : System.FilePath) : IO (WrapMainConsts nc) := do
  let raw ← IO.FS.readFile path
  let parsed : Except String (WrapMainConsts nc) := do
    let j ← Json.parse raw
    let pt := Bulletproof.Fixture.parsePt XhatCurve
    let chunks (j : Json) : Except String (Vector XhatCurve.Point nc) := do
      let pts ← FixtureKit.parseArrOf pt j
      if h : pts.size = nc then pure ⟨pts, h⟩ else throw s!"{pts.size} chunks, expected {nc}"
    let comms (j : Json) (k : String) (n : ℕ) :
        Except String (Vector (Vector (AffinePoint (FVar Fq)) nc) n) := do
      let cs ← FixtureKit.parseArrOf chunks (← j.getObjVal? k)
      if h : cs.size = n then pure (Vector.map (·.map xhatBase) ⟨cs, h⟩)
      else throw s!"{k}: {cs.size} commitments"
    let key (j : Json) : Except String (Pickles.VkComms nc (AffinePoint (FVar Fq))) := do
      let sel ← comms j "selectors" 6
      pure { sigmaComm := ← comms j "sigma" 7, coefficientsComm := ← comms j "coefficients" 15
             genericComm := sel[0], poseidonComm := sel[1], completeAddComm := sel[2]
             mulComm := sel[3], emulComm := sel[4], endomulScalarComm := sel[5] }
    let nats (k : String) : Except String (List ℕ) := do
      pure (← FixtureKit.parseArrOf (fun j => j.getNat?) (← j.getObjVal? k)).toList
    pure
      { stepWidths := ← nats "stepWidths"
        domainLog2s := ← nats "domainLog2s"
        keys := (← FixtureKit.parseArrOf key (← j.getObjVal? "stepKeys")).toList
        lagrange := ← FixtureKit.parseArrOf
          (fun j => do pure (← FixtureKit.parseArrOf chunks j).toList) (← j.getObjVal? "lagrange")
        h := ← pt (← j.getObjVal? "h")
        pins := (← FixtureKit.parseArrOf
          (fun j => do pure (← FixtureKit.parseArrOf (fun j => j.getInt?) j).toList)
          (← j.getObjVal? "pins")).toList
        slotWidths := ← nats "slotWidths"
        dummy := (← FixtureKit.parseArrOf FixtureKit.parseZMod
          (← j.getObjVal? "dummyWrapExpanded")).toList }
  match parsed with
  | .ok r => return r
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- The exported slot counts as one per branch, each at most `mpv`, when they are. -/
def wrapMainWidths? (bp mpv : ℕ) (ws : List ℕ) : Option (Vector (Fin (mpv + 1)) (bp + 1)) :=
  if h : ws.length = bp + 1 ∧ ∀ x ∈ ws, x ≤ mpv then
    some (Vector.ofFn fun b =>
      ⟨ws[b.val]'(by omega), Nat.lt_succ_of_le (h.2 _ (List.getElem_mem _))⟩)
  else none

/-- The exported step domains as one per branch, when they are. -/
def wrapMainLog2s? (bp : ℕ) (ls : List ℕ) : Option (Vector ℕ (bp + 1)) :=
  if h : ls.length = bp + 1 then some ⟨ls.toArray, by simpa using h⟩ else none

/-- A `wrap_main_*` circuit: `Pickles.wrapMain` at `bp + 1` branches, `mpv` slots and `nc`
step chunks from its constants, slot counts and step domains; a branch's Lagrange table is the
one exported for its step domain. -/
def wrapMainDumpCircuit (bp mpv nc : ℕ) (k : WrapMainConsts nc)
    (widths : Vector (Fin (mpv + 1)) (bp + 1)) (log2s : Vector ℕ (bp + 1))
    (stmt : Vector (FVar Fq) 40) :
    CircuitM Fq Cq PUnit :=
  let zeroKey : Pickles.VkComms nc (AffinePoint (FVar Fq)) :=
    VkComms.replicate (Vector.replicate nc ⟨.const 0, .const 0⟩)
  let pin (v : Int) : Option ℕ := if v < 0 then none else some v.toNat
  let zeroPts : Vector XhatCurve.Point nc :=
    Vector.replicate nc (CompElliptic.CurveForms.ShortWeierstrass.SWPoint.zero XhatCurve.E)
  Pickles.wrapMain (branches := bp + 1) (mpv := mpv) (ncStep := nc) (k := 15) (ks := 16)
    fopWrapParams
    (fun l => Kimchi.Fixture.PS.fqSide.omega (2 ^ l)) widths log2s
    (Vector.ofFn fun b => k.keys.getD b.val zeroKey)
    (Vector.ofFn fun s => Vector.ofFn fun b => pin ((k.pins.getD b.val []).getD s.val (-1)))
    (fun l => k.lagrange.toList.map fun perBranch =>
      perBranch.getD (k.domainLog2s.idxOf l) zeroPts)
    k.h k.dummy (Vector.ofFn fun s => k.slotWidths.getD s.val 0)
    ⟨AsProver.throw "advice", AsProver.throw "advice", AsProver.throw "advice",
      AsProver.throw "advice", AsProver.throw "advice", AsProver.throw "advice",
      AsProver.throw "advice", AsProver.throw "advice"⟩ stmt *> pure PUnit.unit

/-- The `wrap_main_*` dumps with their branch, slot and chunk counts. -/
def wrapMainDumps : List (String × ℕ × ℕ × ℕ) :=
  [ ("wrap_main_circuit", 0, 1, 1),
    ("wrap_main_side_loaded_main_circuit", 0, 1, 1),
    ("wrap_main_n2_circuit", 0, 2, 1),
    ("wrap_main_add_one_return_circuit", 0, 0, 1),
    ("chunks2_wrap_main_circuit", 0, 0, 2),
    ("wrap_main_tree_proof_return_circuit", 0, 2, 1),
    ("wrap_main_two_phase_chain_circuit", 1, 1, 1) ]

/-- The Lagrange bases and blinding `h` of an `x_hat` circuit, from its circuit-diffs export
(`{lagrange : [[x,y]×n], h : [x,y]}`, decimal pairs), parsed as points of `C` — `IpaVesta` for
`xhat_wrap_lagrange.json`, `IpaPallas` for `xhat_step_lagrange.json`. The corrections are
derived in-circuit. -/
def xhatPoints (C : Bulletproof.Ipa.KimchiCurve) (path : System.FilePath) :
    IO (Array C.Point × C.Point) := do
  let raw ← IO.FS.readFile path
  let parsed : Except String (Array C.Point × C.Point) := do
    let j ← Json.parse raw
    let lagr ← FixtureKit.parseArrOf (Bulletproof.Fixture.parsePt C) (← j.getObjVal? "lagrange")
    let h ← Bulletproof.Fixture.parsePt C (← j.getObjVal? "h")
    pure (lagr, h)
  match parsed with
  | .ok r => return r
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- `xhatPoints` for a chunked export (`{lagrange : [[[x,y]×nc]×n], h : [x,y]}`): each base as
its `nc` chunks. -/
def xhatPointsChunks (C : Bulletproof.Ipa.KimchiCurve) (nc : ℕ) (path : System.FilePath) :
    IO (Array (Vector C.Point nc) × C.Point) := do
  let raw ← IO.FS.readFile path
  let chunks (j : Json) : Except String (Vector C.Point nc) := do
    let pts ← FixtureKit.parseArrOf (Bulletproof.Fixture.parsePt C) j
    if h : pts.size = nc then pure ⟨pts, h⟩ else throw s!"{pts.size} chunks, expected {nc}"
  let parsed : Except String (Array (Vector C.Point nc) × C.Point) := do
    let j ← Json.parse raw
    let lagr ← FixtureKit.parseArrOf chunks (← j.getObjVal? "lagrange")
    let h ← Bulletproof.Fixture.parsePt C (← j.getObjVal? "h")
    pure (lagr, h)
  match parsed with
  | .ok (lagr, h) => return (lagr, h)
  | .error e => throw (IO.userError s!"{path}: {e}")

/-! ### The step side (`xhat_step_circuit`)

The step-side `x_hat` MSM (`Pickles.publicInputCommitKnown`, OCaml `multiscale_known`) against
the PS `XhatStep` harness's `xhat_step_circuit`: 30 Pallas Lagrange bases (Fp coordinates) and
the blinding `h` from `xhat_step_lagrange.json`. The leaf widths follow
`XhatStep.parseXhatStepInput`: `full` (255-bit) at {0..4, 10..12}, `b128` at {5..9, 13..28},
`b10` at {29}; no `condAdd`. In `PureCorrections` mode the corrections are constants: the
gadget takes the first leaf's correction (`corrHead`, the seed PS uses only when the first
result is a `condAdd`) and their sum (`corrSum`), both computed natively here. -/

/-- The 30 step leaves: leaf `i` reads `get i` at Lagrange base `pts[i]` with its constant
correction, at the width `xhatStepWidth i`. -/
def xhatStepLeaves (pts : Array XhatStepCurve.Point) (get : ℕ → FVar Fp) :
    List (Pickles.Leaf Fp 1) :=
  (List.range 30).map fun i =>
    let base := xhatStepConst (pts[i]?.getD 0)
    let corr := xhatStepConst (xhatStepCorr pts i)
    match xhatStepWidth i with
    | 255 => .full (get i) base corr
    | 10 => .b10 (get i) base corr
    | _ => .b128 (get i) base corr

/-- The known-domain `x_hat` over the step leaves, with the constant correction seed and sum:
the one chunk, as the list the group half consumes. -/
def xhatStepCommit (pts : Array XhatStepCurve.Point) (h : AffinePoint (FVar Fp))
    (get : ℕ → FVar Fp) : CircuitM Fp C (List (AffinePoint (FVar Fp))) := do
  let corrSum : XhatStepCurve.Point := ((List.range 30).map (xhatStepCorr pts)).sum
  let r ← Pickles.publicInputCommitKnown (0 : Fin 1) h (xhatStepCell (xhatStepCorr pts 0))
    (xhatStepCell corrSum) (xhatStepLeaves pts get)
  pure [r]

/-- `xhat_step_circuit`: `Pickles.publicInputCommitKnown` over the 30-leaf list, leaf `i`
reading input `i` and Lagrange base `pts[i]`, with the constant correction seed and sum. -/
def xhatStepCircuit (pts : Array XhatStepCurve.Point) (h : AffinePoint (FVar Fp))
    (input : Vector (FVar Fp) 30) : CircuitM Fp C PUnit := do
  let _ ← xhatStepCommit pts h fun i => input[i]?.getD (.const 0)
  pure PUnit.unit

/-! ## The `ft_comm` circuits

Transcribe `Pickles.CircuitDiffs.PureScript.FtcommStep` and `Ftcomm`: `Pickles.ftComm` at
either side's `IpaScalarOps` over the dumps' layouts — the 7 `t_comm` points at 0–13, then
`perm`, `ζ^{2^k}`, `ζⁿ`: `(sDiv2, sOdd)` Type2 pairs at 14–19 on the step side, one Type1 cell
each at 14–16 on the wrap side. `σ₆` is the one-chunk constant group generator (OCaml
`Inner_curve.Params.one`, the IVP dump's `dummy_comm`). -/

/-- The Pallas group generator (proof-systems `pallas.rs` `G_GENERATOR_{X,Y}`), as a constant
point at the step field. -/
def pallasGenerator : AffinePoint (FVar Fp) :=
  ⟨.const 1, .const 12418654782883325593414442427049395787963493412651469444558597405572177144507⟩

/-- The Vesta group generator (proof-systems `vesta.rs` `G_GENERATOR_{X,Y}`), as a constant
point at the wrap field. -/
def vestaGenerator : AffinePoint (FVar Fq) :=
  ⟨.const 1, .const 11426906929455361843568202299992114520848200991084027513389447476559454104162⟩

/-- `ftcomm_step_circuit`. -/
def ftcommStepCircuit (input : Vector (FVar Fp) 20) : CircuitM Fp C PUnit := do
  let get (i : ℕ) : FVar Fp := input[i]?.getD (.const 0)
  let pt (i : ℕ) : AffinePoint (FVar Fp) := ⟨get i, get (i + 1)⟩
  let shifted (i : ℕ) : Type2 (SplitField (FVar Fp) (BoolVar Fp)) :=
    ⟨⟨get i, .unchecked (get (i + 1))⟩⟩
  let _ ← Pickles.ftComm Pickles.IpaScalarOps.step [pallasGenerator]
    ((List.range 7).map fun j => pt (2 * j)) (shifted 14) (shifted 16) (shifted 18)
  pure PUnit.unit

/-- `ftcomm_wrap_circuit`. -/
def ftcommWrapCircuit (input : Vector (FVar Fq) 17) : CircuitM Fq Cq PUnit := do
  let get (i : ℕ) : FVar Fq := input[i]?.getD (.const 0)
  let pt (i : ℕ) : AffinePoint (FVar Fq) := ⟨get i, get (i + 1)⟩
  let _ ← Pickles.ftComm Pickles.IpaScalarOps.wrap [vestaGenerator]
    ((List.range 7).map fun j => pt (2 * j)) ⟨get 14⟩ ⟨get 15⟩ ⟨get 16⟩
  pure PUnit.unit

/-! ## The `incrementally_verify_proof` circuit

Transcribes `Pickles.CircuitDiffs.PureScript.IvpStep`: the 175-input layout is the packed
public input at 0–29 (the `x_hat` leaves, at the widths of `xhat_step_circuit`), the deferred
values at 30–59 (`α, β, γ, ζ` at 30–33, `perm`, `ζ^{2^k}`, `ζⁿ`, `cip`, `b` as `(sDiv2, sOdd)`
pairs at 34–43, `ξ` at 44, the 15 round challenges at 45–59), the 15 `w_comm` points at
60–89, `z_comm` at 90, the 7 `t_comm` points at 92–105, `δ` at 106, `sg` at 108, the 15
`(L, R)` pairs at 110–169, `z₁`, `z₂` at 170–173 and the claimed digest at 174. The key's
commitments are the dummy generator and the two `sg_old` the dummy wrap `sg` (PS `Common`).
The standalone PS harness derives the index digest by absorbing the key's commitments into a
fresh sponge (`IncrementallyVerifyProof.purs`, the `Nothing` branch), so this harness replays
that absorb before handing the sponge to the gadget. The 30 Lagrange bases and `h` are the
`pallasCrs15` SRS's at domain 15 (`ivp_step_lagrange.json`), not `xhat_step_circuit`'s. -/

/-- The dummy `sg_old` (PS `dummyWrapSg`), as a constant point at the step field. -/
def dummyWrapSg : AffinePoint (FVar Fp) :=
  ⟨.const 8063668238751197448664615329057427953229339439010717262869116690340613895496,
   .const 2694491010813221541025626495812026140144933943906714931997499229912601205355⟩

/-- The dummy key's commitments (PS `Common`): `σ₀…σ₆`, the 15 coefficient commitments and
the six index commitments, each one chunk at the generator. -/
def dummyKeyComms : Pickles.VkComms 1 (AffinePoint (FVar Fp)) :=
  VkComms.replicate #v[pallasGenerator]

/-- The sponge after the dummy key's index digest. -/
def dummyIndexSponge : CircuitM Fp C (SpongeVar Fp) :=
  indexSponge Bulletproof.IpaVesta.curve.frSponge.params dummyKeyComms

/-- The group half's cells from the 175-input layout at `get`: the claims and the opening
from the inputs, the key's commitments and `sg_old` dummy constants. -/
def ivpStepInput (get : ℕ → FVar Fp) :
    Pickles.IvpInput Pickles.WrapIPARounds 1 (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))) :=
  let pt (i : ℕ) : AffinePoint (FVar Fp) := ⟨get i, get (i + 1)⟩
  let shifted (i : ℕ) : Type2 (SplitField (FVar Fp) (BoolVar Fp)) :=
    ⟨⟨get i, .unchecked (get (i + 1))⟩⟩
  let dv : Pickles.DeferredValues Pickles.WrapIPARounds (FVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))) :=
    { plonk := { alpha := ⟨get 30⟩, beta := ⟨get 31⟩, gamma := ⟨get 32⟩, zeta := ⟨get 33⟩,
                 perm := shifted 34, zetaToSrsLength := shifted 36, zetaToDomainSize := shifted 38 }
      combinedInnerProduct := shifted 40, b := shifted 42, xi := ⟨get 44⟩
      bulletproofChallenges := Vector.ofFn fun j => ⟨get (45 + j)⟩ }
  Pickles.ivpInputOf dv [(none, dummyWrapSg), (none, dummyWrapSg)] dummyKeyComms
    { wComm := Vector.ofFn fun j => #v[pt (60 + 2 * j)]
      zComm := #v[pt 90]
      tComm := Vector.ofFn fun j => pt (92 + 2 * j)
      opening := { lr := Vector.ofFn fun j => (pt (110 + 4 * j), pt (112 + 4 * j))
                   z1 := shifted 170, z2 := shifted 172, delta := pt 106, sg := pt 108 } }

/-- `ivp_step_circuit`: the index-digest sponge, `Pickles.incrementallyVerifyProof` on the
step side with `x_hat` the known-domain commitment of inputs 0–29, then the harness's
assertions — the digest against input 174 and each returned round challenge against its
claim. -/
def ivpStepCircuit (pts : Array XhatStepCurve.Point) (h : AffinePoint (FVar Fp))
    (input : Vector (FVar Fp) 175) : CircuitM Fp C PUnit := do
  let get (i : ℕ) : FVar Fp := input[i]?.getD (.const 0)
  let sv ← dummyIndexSponge
  let o ← Pickles.incrementallyVerifyProof Pickles.IpaScalarOps.step Pickles.IpaEndo.pallas
    Bulletproof.IpaVesta.curve.frSponge.params (.const endoVestaLam) Pickles.groupMapParamsPallas
    (fun _ => none) false h sv (xhatStepCommit pts h get) (ivpStepInput get)
  assertEqual o.spongeDigest (get 174)
  for c in ((List.range 15).map fun j => get (45 + j)).zip o.bulletproofChallenges do
    assertEqual c.1 c.2.val
  pure PUnit.unit

/-! ## The `verify` circuit (`Step_verifier.verify`)

Transcribes `Pickles.CircuitDiffs.PureScript.StepVerify`: the 268-input layout is the wrap
proof at 0–113 (15 `w_comm` points at 0–29, `z_comm` at 30, 7 `t_comm` points at 32–45, the
15 `(L, R)` pairs at 46–105, `z₁`, `z₂` at 106–109, `δ` at 110, `sg` at 112), the wrap
statement's proof state at 114–143 (`α, β, γ, ζ` at 114–117, `ζ^{2^k}`, `ζⁿ`, `perm` at
118–120, `cip`, `b` at 121–122, `ξ` at 123, the 16 round challenges at 124–139, the two mask
bits at 140–141, `domain_log2` at 142, the digest at 143), dead evaluation inputs at 144–232,
the unfinalized proof at 233–264 (`cip`, `b`, `ζ^{2^k}`, `ζⁿ`, `perm` as `(sDiv2, sOdd)` pairs at
233–242, the digest at 243, `β, γ, α, ζ` at 244–247, `ξ` at 248, the 15 round challenges at
249–263), `is_base_case` at 265 and the two message digests at 266–267. The key and `sg_old`
are the dummies of `ivp_step_circuit`, the index digest the same replayed absorb, the
Lagrange bases the same `pallasCrs15` export. -/

/-- The unfinalized proof the verified wrap proof is checked against, from the 268-input
layout. -/
def stepVerifyUnfinalized (get : ℕ → FVar Fp) :
    Pickles.UnfinalizedProof Pickles.WrapIPARounds (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))) :=
  let shifted (i : ℕ) : Type2 (SplitField (FVar Fp) (BoolVar Fp)) :=
    ⟨⟨get i, .unchecked (get (i + 1))⟩⟩
  { deferredValues :=
      { plonk := { alpha := ⟨get 246⟩, beta := ⟨get 244⟩, gamma := ⟨get 245⟩, zeta := ⟨get 247⟩,
                   perm := shifted 241, zetaToSrsLength := shifted 237,
                   zetaToDomainSize := shifted 239 }
        combinedInnerProduct := shifted 233, b := shifted 235, xi := ⟨get 248⟩
        bulletproofChallenges := Vector.ofFn fun j => ⟨get (249 + j)⟩ }
    shouldFinalize := true_
    spongeDigestBeforeEvaluations := get 243 }

/-- The wrap statement from the 268-input layout: the proof state's claims as `Type1` cells,
the branch data, the three digests. -/
def stepVerifyStatement (get : ℕ → FVar Fp) :
    Pickles.WrapStatement Pickles.StepIPARounds (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)) :=
  { proofState :=
      { deferredValues :=
          { plonk := { alpha := ⟨get 114⟩, beta := ⟨get 115⟩, gamma := ⟨get 116⟩,
                       zeta := ⟨get 117⟩, perm := ⟨get 120⟩, zetaToSrsLength := ⟨get 118⟩,
                       zetaToDomainSize := ⟨get 119⟩ }
            combinedInnerProduct := ⟨get 121⟩, b := ⟨get 122⟩, xi := ⟨get 123⟩
            bulletproofChallenges := Vector.ofFn fun j => ⟨get (124 + j)⟩
            branchData := { domainLog2 := get 142,
                            proofsVerifiedMask := #v[.unchecked (get 140), .unchecked (get 141)] } }
        spongeDigestBeforeEvaluations := get 143
        messagesForNextWrapProof := get 266 }
    messagesForNextStepProof := get 267 }

/-- The group half's cells from the 268-input layout: the wrap proof block at 0, the key and
`sg_old` dummies; the claim cells are `verify`'s to substitute. -/
def stepVerifyCells (get : ℕ → FVar Fp) :
    Pickles.IvpInput Pickles.WrapIPARounds 1 (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))) :=
  let pt (i : ℕ) : AffinePoint (FVar Fp) := ⟨get i, get (i + 1)⟩
  let shifted (i : ℕ) : Type2 (SplitField (FVar Fp) (BoolVar Fp)) :=
    ⟨⟨get i, .unchecked (get (i + 1))⟩⟩
  Pickles.ivpInputOf (stepVerifyUnfinalized get).deferredValues
    [(none, dummyWrapSg), (none, dummyWrapSg)] dummyKeyComms
    { wComm := Vector.ofFn fun j => #v[pt (2 * j)]
      zComm := #v[pt 30]
      tComm := Vector.ofFn fun j => pt (32 + 2 * j)
      opening := { lr := Vector.ofFn fun j => (pt (46 + 4 * j), pt (48 + 4 * j))
                   z1 := shifted 106, z2 := shifted 108, delta := pt 110, sg := pt 112 } }

/-- `step_verify_circuit`: the index-digest sponge, then `Pickles.verifyProofWith` — the gadget
`verifyProofAt` is at an environment's data — at the dump's points, over the parsed statement,
unfinalized proof and cells. -/
def stepVerifyCircuit (pts : Array XhatStepCurve.Point) (h : XhatStepCurve.Point)
    (input : Vector (FVar Fp) 268) : CircuitM Fp C PUnit := do
  let get (i : ℕ) : FVar Fp := input[i]?.getD (.const 0)
  let sv ← dummyIndexSponge
  let _ ← Pickles.verifyProofWith h (oneChunk pts) sv (.unchecked (get 265))
    (stepVerifyStatement get) (stepVerifyUnfinalized get) (stepVerifyCells get)
  pure PUnit.unit

/-! ## One slot of the step circuit

Transcribes `Pickles.CircuitDiffs.PureScript.FullStepVerifyOne`: `Pickles.verifyOneBy` over one
previous proof of width 1, the check against `verifyProofWith` at `pallasCrs15`'s Lagrange bases
at domain 14 (`full_step_lagrange.json`), the finalize at the dump's one known domain of
`log2 = 16`, the key's commitments the dummy generator and the padded `sg_old` the dummy wrap
`sg`.

The 286-cell layout: the application state at 0; the wrap proof from 1 (the 15 `w_comm` points,
`z_comm` at 31, the 7 `t_comm` points at 33, the 15 `(L, R)` pairs at 47, `z₁`, `z₂` at 107-110,
`δ` at 111, `sg` at 113); the proof state from 115 (`α, β, γ, ζ`, `ζ^{2^k}`, `ζⁿ`, `perm`,
`cip`, `b`, `ξ`, the 16 round challenges, the two mask bits, the domain's `log2` at 143, the
digest at 144); the evaluations from 145 (44 columns of two cells, `ft(ζω)` at 233); the
previous challenges at 234; the previous `sg` at 250; the unfinalized proof from 252; the
wrap-side message at 284 and `mustVerify` at 285. -/

open Pickles Kimchi.Verifier in
/-- `full_step_verify_one_circuit`. -/
def fullStepVerifyOneCircuit (pts : Array XhatStepCurve.Point) (h : XhatStepCurve.Point)
    (input : Vector (FVar Fp) 286) : CircuitM Fp C PUnit := do
  let get (i : ℕ) : FVar Fp := input[i]?.getD (.const 0)
  let pt (i : ℕ) : AffinePoint (FVar Fp) := ⟨get i, get (i + 1)⟩
  let split (i : ℕ) : Type2 (SplitField (FVar Fp) (BoolVar Fp)) :=
    ⟨⟨get i, .unchecked (get (i + 1))⟩⟩
  let col (b k : ℕ) : PointEvaluations (Vector (FVar Fp) 1) :=
    ⟨#v[get (b + 2 * k)], #v[get (b + 2 * k + 1)]⟩
  let psb := 115
  let eb := 145
  let inp : VerifyOneInput 16 15 1 1 1 :=
    { appState := [get 0]
      deferred := ⟨⟨⟨get psb⟩, ⟨get (psb + 1)⟩, ⟨get (psb + 2)⟩, ⟨get (psb + 3)⟩,
          ⟨get (psb + 6)⟩, ⟨get (psb + 4)⟩, ⟨get (psb + 5)⟩⟩, ⟨get (psb + 7)⟩, ⟨get (psb + 9)⟩,
        Vector.ofFn fun j => ⟨get (psb + 10 + j)⟩, ⟨get (psb + 8)⟩⟩
      spongeDigest := get (psb + 29)
      branchData := ⟨get (psb + 28), #v[.unchecked (get (psb + 26)), .unchecked (get (psb + 27))]⟩
      messagesForNextWrapProof := get 284
      evals := ⟨get (eb + 88), col eb 0,
        ⟨Vector.ofFn fun j => col (eb + 2) j, col (eb + 62) 0, Vector.ofFn fun j => col (eb + 64) j,
          Vector.ofFn fun j => col (eb + 32) j, col (eb + 76) 0, col (eb + 76) 1, col (eb + 76) 2,
          col (eb + 76) 3, col (eb + 76) 4, col (eb + 76) 5⟩⟩
      proofMask := #v[.unchecked (get (psb + 27))]
      prevChallenges := #v[Vector.ofFn fun j => get (234 + j)]
      prevSgs := #v[pt 250]
      sgOld := #v[dummyWrapSg, pt 250]
      unfinalized := ⟨⟨⟨⟨get 265⟩, ⟨get 263⟩, ⟨get 264⟩, ⟨get 266⟩, split 260, split 256,
          split 258⟩, split 252, ⟨get 267⟩, Vector.ofFn fun j => ⟨get (268 + j)⟩, split 254⟩,
        .unchecked (get 283), get 262⟩
      proof := ⟨Vector.ofFn fun j => #v[pt (1 + 2 * j)], #v[pt 31],
        Vector.ofFn fun j => pt (33 + 2 * j),
        ⟨Vector.ofFn fun j => (pt (47 + 4 * j), pt (49 + 4 * j)), split 107, split 109, pt 111,
          pt 113⟩⟩
      mustVerify := .unchecked (get 285) }
  let _ ← verifyOneBy (fun sv b st u cells => verifyProofWith h (oneChunk pts) sv b st u cells)
    PicklesFixture.fopStepParams [⟨16, Kimchi.Fixture.PS.fpSide.omega (2 ^ 16)⟩] dummyKeyComms inp
  pure PUnit.unit

/-! ## The step circuit

Transcribes `Pickles.CircuitDiffs.PureScript.StepMainSimpleChainN2`: `Pickles.stepMain` for the
rule `self = 1 + prev₁ + prev₂` over two self slots of width 2, at the Lagrange bases of
`full_step_lagrange.json`, the finalize at the rule's own step domain (`log2 = 15`, the dump's
22957 rows rounded up), and the wrap-side messages unpadded. The output is the 67 cells of the
step statement. `Pickles.CircuitDiffs.PureScript.StepMainTwoPhaseChainMakeZero` is the padded
case: no slot in a tag of width 1, so one dummy unfinalized entry and one padding message. The
advice is inert: the comparison is on the constraint system. -/

/-- The unfinalized entry padding the statement of a rule verifying no proofs (PS
`Dummy.baseCaseDummies { maxProofsVerified: 0 }`), at the wrap circuit's 15 rounds. -/
def dummyUnfN0 : Pickles.UnfVal 15 :=
  let sf (x : Fp) : Type2 (SplitField Fp Bool) := ⟨⟨x, true⟩⟩
  { cip := sf 10733637291412775405099085909742784243308064411873129175045178535313137524648
    b := sf 12005690365207186104828106725404484059974178413747419366262848828074459318671
    zetaToSrsLength :=
      sf 7826322391957027530016555805456769916486940393993472644155614648591765317494
    zetaToDomainSize :=
      sf 7826322391957027530016555805456769916486940393993472644155614648591765317494
    perm := sf 11720302720943076563339347688798825215517484960467558296985186859509025408993
    spongeDigest := 6277101735386680764176071790128604879584176795969512275969
    beta := 152341587173296550850923210387509020609
    gamma := 239197809892340837260422696781281951881
    alpha := 236185100527557585826515066705725312805
    zeta := 260445934505999659442479615932459762956
    xi := 18446744073709551617
    bulletproofChallenges := #v[161621990286339861369413299182831583087,
      294397517322790754025793051151124957079, 10455894452509500744048069718178570187,
      224814704134265519234947971901913897491, 330128161163701260858569889180053145483,
      102493828312258879830323023652412497031, 215326567078568560823705023668614618897,
      120359744259981153545389569741970563149, 221360828059242236386510005024107555656,
      257571901803291014519404945390244881518, 209025140278641004900167089918138330057,
      201591733645229477386800950847198767694, 318881875946480425567146057353930829431,
      198219236102229943192453714701868046676, 122049445183499159876948789073679959987]
    shouldFinalize := false }

/-- The rule of `simple_chain_n2`: two previous states, `self` their sum plus one unless `self`
is zero, the base case in which neither previous proof must verify. -/
def simpleChainN2Rule (appState : FVar Fp) :
    CircuitM Fp C (Vector Pickles.PrevStatement 2 × List (FVar Fp)) := do
  let prev1 ← witness (val := Fp) (AsProver.throw "advice")
  let prev2 ← witness (val := Fp) (AsProver.throw "advice")
  let isBaseCase ← equals (.const 0) appState
  let mustVerify := Snarky.not isBaseCase
  let selfCorrect ← equals (CVar.add_ (CVar.add_ (.const 1) prev1) prev2) appState
  assertAny [selfCorrect, isBaseCase]
  pure (#v[⟨[prev1], mustVerify⟩, ⟨[prev2], mustVerify⟩], [])

open Pickles in
/-- `step_main_simple_chain_n2_circuit`. -/
def stepMainSimpleChainN2Circuit (pts : Array XhatStepCurve.Point) (h : XhatStepCurve.Point)
    (_ : Vector (FVar Fp) 0) : CircuitM Fp C (Vector (FVar Fp) 67) := do
  let out ← stepMain (n := 2) (w := 2) (ncw := 1) (ncs := 1) (k := 15) (ks := 16) (inVal := Fp)
    (by decide)
    (fun sv b st u cells => verifyProofWith h (oneChunk pts) sv b st u cells)
    PicklesFixture.fopStepParams [⟨15, Kimchi.Fixture.PS.fpSide.omega (2 ^ 15)⟩] dummyWrapSg
    dummyUnfN0 simpleChainN2Rule
    ⟨AsProver.throw "advice", AsProver.throw "advice", AsProver.throw "advice",
      AsProver.throw "advice", AsProver.throw "advice", AsProver.throw "advice"⟩
  pure (Vector.ofFn fun i => out.out[i.val]?.getD (.const 0))

open Pickles in
/-- `step_main_two_phase_chain_make_zero_circuit`: the rule `self = 0` with no slot, so the
verifier and the finalize's domains are never used. -/
def stepMainTwoPhaseChainMakeZeroCircuit (_ : Vector (FVar Fp) 0) :
    CircuitM Fp C (Vector (FVar Fp) 34) := do
  let out ← stepMain (n := 0) (w := 1) (ncw := 1) (ncs := 1) (k := 15) (ks := 16) (inVal := Fp)
    (by decide)
    (fun _ _ _ _ _ => pure true_) PicklesFixture.fopStepParams [] dummyWrapSg dummyUnfN0
    (fun x => do makeZeroAppCircuit x; pure (#v[], []))
    ⟨AsProver.throw "advice", AsProver.throw "advice", AsProver.throw "advice",
      AsProver.throw "advice", AsProver.throw "advice", AsProver.throw "advice"⟩
  pure (Vector.ofFn fun i => out.out[i.val]?.getD (.const 0))

/-! ## The wrap side's `incrementally_verify_proof`

Transcribes `Pickles.CircuitDiffs.PureScript.IvpWrap`: the wrap circuit's group half over a
step proof, at the conditional sponge with no `sg_old`, the key's commitments the dummy Vesta
generator, and `x_hat` the in-circuit-correction commitment of the packed step statement
(`PackedStepPublicInput 1 15`, one slot at the wrap SRS's 15 rounds). The Lagrange bases are
`xhat_wrap_lagrange.json`'s, which the PS harness builds from the same `vestaCrs16` data it
gives `xhat_wrap_circuit`.

The 177-cell layout: the statement slot at 0-31 (the five split claims as `(half, parity)`
pairs at 0-9, the digest at 10, `β, γ` at 11-12, `α, ζ, ξ` at 13-15, the 15 round challenges
from 16, `should_finalize` at 31), `messages_for_next_step_proof` at 32 and the slot's
`messages_for_next_wrap_proof` at 33; then the step proof's deferred values at 34-43 with its
16 round challenges from 44, the 15 `w_comm` points at 60, `z_comm` at 90, the 7 `t_comm`
points at 92, `δ` at 106, `sg` at 108, the 16 `(L, R)` pairs at 110, `z₁`, `z₂` at 174-175,
and the claimed digest at 176. -/

/-- The dummy key's commitments on the wrap side (PS `dummyVestaPt`, the Vesta generator):
`σ₀…σ₆`, the 15 coefficient commitments and the six index commitments, one chunk each. -/
def dummyWrapKeyComms : Pickles.VkComms 1 (AffinePoint (FVar Fq)) :=
  VkComms.replicate #v[vestaGenerator]

/-- The step statement of the wrap-side harnesses, one slot at 15 rounds, from `get`. -/
def wrapStepStatement (get : ℕ → FVar Fq) :
    Pickles.StepStatement 15 1 (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq))) :=
  let split (i : ℕ) : Type2 (SplitField (FVar Fq) (BoolVar Fq)) :=
    ⟨⟨get i, .unchecked (get (i + 1))⟩⟩
  { proofState :=
      { unfinalizedProofs := #v[
          { deferredValues :=
              { plonk := { alpha := ⟨get 13⟩, beta := ⟨get 11⟩, gamma := ⟨get 12⟩,
                           zeta := ⟨get 14⟩, perm := split 8, zetaToSrsLength := split 4,
                           zetaToDomainSize := split 6 }
                combinedInnerProduct := split 0, b := split 2, xi := ⟨get 15⟩
                bulletproofChallenges := Vector.ofFn fun j => ⟨get (16 + j)⟩ }
            shouldFinalize := .unchecked (get 31)
            spongeDigestBeforeEvaluations := get 10 }]
        messagesForNextStepProof := get 32 }
    messagesForNextWrapProof := #v[get 33] }

/-- The step proof's deferred values from the wrap-side layout: the plonk claims at 34-40,
`cip`, `b`, `ξ` at 41-43, the 16 round challenges from 44. -/
def wrapIvpDv (get : ℕ → FVar Fq) : Pickles.DeferredValues 16 (FVar Fq) (Type1 (FVar Fq)) :=
  { plonk := { alpha := ⟨get 34⟩, beta := ⟨get 35⟩, gamma := ⟨get 36⟩, zeta := ⟨get 37⟩,
               perm := ⟨get 38⟩, zetaToSrsLength := ⟨get 39⟩, zetaToDomainSize := ⟨get 40⟩ }
    combinedInnerProduct := ⟨get 41⟩, b := ⟨get 42⟩, xi := ⟨get 43⟩
    bulletproofChallenges := Vector.ofFn fun j => ⟨get (44 + j)⟩ }

/-- The step proof's commitments and opening from the wrap-side layout: the 15 `w_comm` points
at 60, `z_comm` at 90, the 7 `t_comm` points at 92, `δ` at 106, `sg` at 108, the 16 `(L, R)`
pairs at 110, `z₁`, `z₂` at 174-175. -/
def wrapIvpProof (pt : ℕ → AffinePoint (FVar Fq)) (get : ℕ → FVar Fq) :
    Pickles.IvpProof 16 1 (FVar Fq) (Type1 (FVar Fq)) :=
  { wComm := Vector.ofFn fun j => #v[pt (60 + 2 * j)]
    zComm := #v[pt 90]
    tComm := Vector.ofFn fun j => pt (92 + 2 * j)
    opening := { lr := Vector.ofFn fun j => (pt (110 + 4 * j), pt (112 + 4 * j))
                 z1 := ⟨get 174⟩, z2 := ⟨get 175⟩, delta := pt 106, sg := pt 108 } }

/-- `ivp_wrap_circuit`: the dummy key's index sponge, `Pickles.incrementallyVerifyProof` on the
conditional sponge with `x_hat` the packed step statement's commitment, then the harness's two
assertions — the digest against input 176 and each claimed round challenge against the
returned one. -/
def ivpWrapCircuit (pts : Array XhatCurve.Point) (h : AffinePoint (FVar Fq))
    (input : Vector (FVar Fq) 177) : CircuitM Fq Cq PUnit := do
  let get (i : ℕ) : FVar Fq := input[i]?.getD (.const 0)
  let pt (i : ℕ) : AffinePoint (FVar Fq) := ⟨get i, get (i + 1)⟩
  let dv := wrapIvpDv get
  let sv ← indexSponge Bulletproof.IpaVesta.curve.sponge.params dummyWrapKeyComms
  let computeXHat : CircuitM Fq Cq (List (AffinePoint (FVar Fq))) :=
    Vector.toList <$> Pickles.publicInputCommitFull h
      (Pickles.packLeavesOf (wrapStepStatement get).packed
        (Pickles.XhatTable.ofKey (wrapStepStatement get).packed (oneChunk pts)))
  let o ← Pickles.incrementallyVerifyProof Pickles.IpaScalarOps.wrap Pickles.IpaEndo.vesta
    Bulletproof.IpaVesta.curve.sponge.params (.const endoPallasLam) Pickles.groupMapParamsVesta
    vestaBase.sqrt? true h sv computeXHat
    (Pickles.ivpInputOf dv [] dummyWrapKeyComms (wrapIvpProof pt get))
  assertEqual o.spongeDigest (get 176)
  for c in dv.bulletproofChallenges.toList.zip o.bulletproofChallenges do
    assertEqual c.1.val c.2.val
  pure PUnit.unit

/-! ## The wrap circuit's verify block

Transcribes `Pickles.CircuitDiffs.PureScript.WrapVerify`: `Pickles.wrapVerifyWith` — the gadget
`wrapVerifyAt` is at an environment's data — at the dump's points, over the same
177-cell IVP layout as `ivp_wrap_circuit`, now with one real accumulator — `sg_old` at 194
under a constant keep bit — followed by the claimed `messages_for_next_wrap_proof` digest at
177 and the new round challenges at 178-192 (193 is unused: the OCaml dump computes the
offset at 16 rounds where the wrap side has 15). -/

/-- The message-hash sponge `wrap_verify_circuit` starts from: the state after absorbing the
one dummy challenge vector that pads its single real slot to `MaxProofsVerified` (PS
`dummyPaddingSpongeStates` at `n = 1`), so the padding costs no gates. -/
def wrapMsgSponge : SpongeVar Fq :=
  Pickles.wrapPaddingSponge Bulletproof.IpaVesta.curve.sponge.params dummyWrapChallenges 1

/-- `wrap_verify_circuit`. -/
def wrapVerifyCircuit (pts : Array XhatCurve.Point) (h : XhatCurve.Point)
    (input : Vector (FVar Fq) 196) : CircuitM Fq Cq PUnit := do
  let get (i : ℕ) : FVar Fq := input[i]?.getD (.const 0)
  let pt (i : ℕ) : AffinePoint (FVar Fq) := ⟨get i, get (i + 1)⟩
  let dv := wrapIvpDv get
  let sv ← indexSponge Bulletproof.IpaVesta.curve.sponge.params dummyWrapKeyComms
  Pickles.wrapVerifyWith h (oneChunk pts) (wrapStepStatement get) sv wrapMsgSponge
    [(List.range 15).map fun j => get (178 + j)] (get 177)
    { deferredValues := dv, shouldFinalize := .unchecked (.const 1)
      spongeDigestBeforeEvaluations := get 176 }
    (Pickles.ivpInputOf dv [(some (.unchecked (.const 1)), pt 194)] dummyWrapKeyComms
      (wrapIvpProof pt get))

/-! ## The `messages_for_next_wrap_proof` hash

Transcribes `Pickles.CircuitDiffs.PureScript.HashMessagesWrap`: the digest the wrap circuit
commits its accumulator advice to (`Pickles.hashMessagesForNextWrapProof`, OCaml
`wrap_hack.ml:119-142`), from the fresh sponge, asserted against the claimed digest. The
layout is 33 cells: the two `MaxProofsVerified` challenge vectors of `WrapIPARounds` at 0-29,
`sg` at 30-31, the claim at 32. -/

/-- `hash_messages_for_next_wrap_proof_circuit`. -/
def hashMessagesWrapCircuit (input : Vector (FVar Fq) 33) : CircuitM Fq Cq PUnit := do
  let get (i : ℕ) : FVar Fq := input[i]?.getD (.const 0)
  let digest ← Pickles.hashMessagesForNextWrapProof Bulletproof.IpaVesta.curve.sponge.params
    SpongeVar.init
    [(List.range 15).map fun j => get j, (List.range 15).map fun j => get (15 + j)]
    ⟨get 30, get 31⟩
  assertEqual digest (get 32)

/-! ## The step proof's accumulator digest

Transcribes `Pickles.CircuitDiffs.PureScript.HashMessagesStep`: the digest the step circuit
commits its predecessors' accumulator advice to, on the plain sponge
(`Pickles.hashMessagesForNextStepProof`, OCaml `step_verifier.ml:1167-1188`), with no
application state, asserted against the claimed digest. The layout is 91 cells: the key's 28
one-chunk commitments at 0-55 (`σ₀…σ₆`, the 15 coefficients, the six selectors, each `x, y`),
then two proofs of 17 cells from 56 (`sg`, then 15 challenges), the claim at 90. -/

/-- `hash_messages_for_next_step_proof_circuit`. -/
def hashMessagesStepCircuit (input : Vector (FVar Fp) 91) : CircuitM Fp C PUnit := do
  let get (i : ℕ) : FVar Fp := input[i]?.getD (.const 0)
  let pt (i : ℕ) : Vector (AffinePoint (FVar Fp)) 1 := #v[⟨get (2 * i), get (2 * i + 1)⟩]
  let vk : Pickles.VkComms 1 (AffinePoint (FVar Fp)) :=
    ⟨Vector.ofFn fun j => pt j, Vector.ofFn fun j => pt (7 + j), pt 22, pt 23, pt 24, pt 25,
      pt 26, pt 27⟩
  let proof (i : ℕ) : AffinePoint (FVar Fp) × List (FVar Fp) :=
    (⟨get (56 + 17 * i), get (57 + 17 * i)⟩, (List.range 15).map fun j => get (58 + 17 * i + j))
  let digest ← Pickles.hashMessagesForNextStepProof Bulletproof.IpaPallas.curve.sponge.params
    vk [] [proof 0, proof 1]
  assertEqual digest (get 90)

/-- The corpus under comparison: the step column, then the wrap column, at the two SRS
blinding bases. -/
def targets (hStep : AffinePoint (FVar Fp)) (hWrap : AffinePoint (FVar Fq)) :
    List (String × (Json → Except String (Option (Bool × List (String × Bool))))) :=
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
    ("expand_plonk_step_circuit",
      stepTarget (a := Vector Fp 4) (b := PUnit) expandPlonkStepCircuit),
    ("fq_sponge_transcript_step_circuit",
      stepTarget (a := Vector Fp 53) (b := PUnit) fqSpongeTranscriptStepCircuit),
    ("check_bulletproof_step_circuit",
      stepTarget (a := Vector Fp 170) (b := PUnit) (checkBulletproofStepCircuit hStep)),
    ("finalize_other_proof_step_circuit",
      stepTarget (a := Vector Fp 151) (b := PUnit) finalizeOtherProofStepCircuit),
    ("finalize_other_proof_chunks2_step_circuit",
      stepTarget (a := Vector Fp 239) (b := PUnit) finalizeOtherProofChunks2StepCircuit),
    ("ftcomm_step_circuit", stepTarget (a := Vector Fp 20) (b := PUnit) ftcommStepCircuit),
    -- the wrap column
    ("group_map_wrap_circuit", wrapTarget (a := Fq) (b := PUnit) groupMapCircuitFq),
    ("linearization_wrap_circuit",
      wrapTarget (a := Vector Fq 90) (b := Fq)
        (linearizationCircuit Kimchi.Fixture.PS.fqSide 15 Pickles.Linearization.fqTokens)),
    ("cip_wrap_circuit", wrapTarget (a := Vector Fq 127) (b := PUnit) cipWrapCircuit),
    ("b_correct_wrap_circuit", wrapTarget (a := Vector Fq 20) (b := PUnit) bCorrectWrapCircuit),
    ("plonk_checks_passed_wrap_circuit",
      wrapTarget (a := Vector Fq 18) (b := PUnit) plonkChecksPassedWrapCircuit),
    ("expand_plonk_wrap_circuit",
      wrapTarget (a := Vector Fq 4) (b := PUnit) expandPlonkWrapCircuit),
    ("fq_sponge_transcript_wrap_circuit",
      wrapTarget (a := Vector Fq 55) (b := PUnit) fqSpongeTranscriptWrapCircuit),
    ("check_bulletproof_wrap_circuit",
      wrapTarget (a := Vector Fq 172) (b := PUnit) (checkBulletproofWrapCircuit hWrap)),
    ("finalize_other_proof_wrap_circuit",
      wrapTarget (a := Vector Fq 148) (b := PUnit) finalizeOtherProofWrapCircuit),
    ("wrap_finalize_n2_circuit",
      wrapTarget (a := Vector Fq 295) (b := PUnit) wrapFinalizeN2Circuit),
    ("ftcomm_wrap_circuit", wrapTarget (a := Vector Fq 17) (b := PUnit) ftcommWrapCircuit),
    -- the Pseudo selection circuits, on both fields
    ("one_hot_n1_step_circuit", stepTarget (a := Vector Fp 1) (b := PUnit) (oneHotCircuit 1)),
    ("one_hot_n3_step_circuit", stepTarget (a := Vector Fp 1) (b := PUnit) (oneHotCircuit 3)),
    ("one_hot_n17_step_circuit", stepTarget (a := Vector Fp 1) (b := PUnit) (oneHotCircuit 17)),
    ("one_hot_n1_wrap_circuit", wrapTarget (a := Vector Fq 1) (b := PUnit) (oneHotCircuit 1)),
    ("one_hot_n3_wrap_circuit", wrapTarget (a := Vector Fq 1) (b := PUnit) (oneHotCircuit 3)),
    ("one_hot_n17_wrap_circuit", wrapTarget (a := Vector Fq 1) (b := PUnit) (oneHotCircuit 17)),
    ("pseudo_mask_n1_step_circuit", stepTarget (a := Vector Fp 2) (b := PUnit)
      (pseudoMaskCircuit 1 fun i => [i[1]])),
    ("pseudo_mask_n3_step_circuit", stepTarget (a := Vector Fp 4) (b := PUnit)
      (pseudoMaskCircuit 3 fun i => [i[1], i[2], i[3]])),
    ("pseudo_mask_n17_step_circuit", stepTarget (a := Vector Fp 1) (b := PUnit)
      (pseudoMaskCircuit 17 fun _ => (List.range 17).map fun j => .const (j : Fp))),
    ("pseudo_mask_n1_wrap_circuit", wrapTarget (a := Vector Fq 2) (b := PUnit)
      (pseudoMaskCircuit 1 fun i => [i[1]])),
    ("pseudo_mask_n3_wrap_circuit", wrapTarget (a := Vector Fq 4) (b := PUnit)
      (pseudoMaskCircuit 3 fun i => [i[1], i[2], i[3]])),
    ("pseudo_mask_n17_wrap_circuit", wrapTarget (a := Vector Fq 1) (b := PUnit)
      (pseudoMaskCircuit 17 fun _ => (List.range 17).map fun j => .const (j : Fq))),
    ("pseudo_choose_n1_step_circuit", stepTarget (a := Vector Fp 1) (b := PUnit)
      (pseudoChooseCircuit 1 [42])),
    ("pseudo_choose_n3_step_circuit", stepTarget (a := Vector Fp 1) (b := PUnit)
      (pseudoChooseCircuit 3 [13, 14, 15])),
    ("pseudo_choose_n1_wrap_circuit", wrapTarget (a := Vector Fq 1) (b := PUnit)
      (pseudoChooseCircuit 1 [42])),
    ("pseudo_choose_n3_wrap_circuit", wrapTarget (a := Vector Fq 1) (b := PUnit)
      (pseudoChooseCircuit 3 [13, 14, 15])),
    ("utils_ones_vector_n16_step_circuit",
      stepTarget (a := Vector Fp 1) (b := PUnit) onesVectorN16Circuit),
    ("utils_ones_vector_n16_wrap_circuit",
      wrapTarget (a := Vector Fq 1) (b := PUnit) onesVectorN16Circuit),
    ("choose_key_n1_wrap_circuit",
      wrapTarget (a := Vector Fq 1) (b := PUnit) chooseKeyN1WrapCircuit),
    ("pseudo_to_domain_wrap_circuit",
      wrapTarget (a := Vector Fq 2) (b := PUnit) pseudoToDomainWrapCircuit),
    ("hash_messages_for_next_step_proof_circuit",
      stepTarget (a := Vector Fp 91) (b := PUnit) hashMessagesStepCircuit),
    ("step_main_two_phase_chain_make_zero_circuit",
      stepTarget (a := Vector Fp 0) (b := Vector Fp 34) stepMainTwoPhaseChainMakeZeroCircuit),
    ("hash_messages_for_next_wrap_proof_circuit",
      wrapTarget (a := Vector Fq 33) (b := PUnit) hashMessagesWrapCircuit) ]

/-- The two step domains' Lagrange bases and blinding `h` from
`xhat_wrap_branches_lagrange.json` (`{lagrange15, lagrange16 : [[x,y]×34], h : [x,y]}`). -/
def xhatBranchesPoints (path : System.FilePath) :
    IO (Array XhatCurve.Point × Array XhatCurve.Point × XhatCurve.Point) := do
  let raw ← IO.FS.readFile path
  let parsed : Except String (Array XhatCurve.Point × Array XhatCurve.Point × XhatCurve.Point) :=
    do
    let j ← Json.parse raw
    let at_ (k : String) := do
      FixtureKit.parseArrOf (Bulletproof.Fixture.parsePt XhatCurve) (← j.getObjVal? k)
    let h ← Bulletproof.Fixture.parsePt XhatCurve (← j.getObjVal? "h")
    pure (← at_ "lagrange15", ← at_ "lagrange16", h)
  match parsed with
  | .ok r => return r
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- The targets baked over a Lagrange export, each present only when its export is (a
narrowed local PS run regenerates one column's exports; the unfiltered run has all). -/
def xhatTargets (wrap : Option (Array XhatCurve.Point × XhatCurve.Point))
    (wrap2 : Option (Array (Vector XhatCurve.Point 2) × XhatCurve.Point))
    (step : Option (Array XhatStepCurve.Point × XhatStepCurve.Point))
    (ivpStep : Option (Array XhatStepCurve.Point × XhatStepCurve.Point))
    (branches : Option (Array XhatCurve.Point × Array XhatCurve.Point × XhatCurve.Point))
    (wrapMains : List (String × (Json → Except String (Option (Bool × List (String × Bool))))))
    (fullStep : Option (Array XhatStepCurve.Point × XhatStepCurve.Point)) :
    List (String × (Json → Except String (Option (Bool × List (String × Bool))))) :=
  (fullStep.toList.map fun (pts, h) =>
    ("full_step_verify_one_circuit",
      stepTarget (a := Vector Fp 286) (b := PUnit) (fullStepVerifyOneCircuit pts h)))
  ++ (fullStep.toList.map fun (pts, h) =>
    ("step_main_simple_chain_n2_circuit",
      stepTarget (a := Vector Fp 0) (b := Vector Fp 67) (stepMainSimpleChainN2Circuit pts h)))
  ++ (step.toList.map fun (pts, h) =>
    ("xhat_step_circuit",
      stepTarget (a := Vector Fp 30) (b := PUnit) (xhatStepCircuit pts (xhatStepCell h))))
  ++ (ivpStep.toList.map fun (pts, h) =>
    ("ivp_step_circuit",
      stepTarget (a := Vector Fp 175) (b := PUnit) (ivpStepCircuit pts (xhatStepCell h))))
  ++ (ivpStep.toList.map fun (pts, h) =>
    ("step_verify_circuit",
      stepTarget (a := Vector Fp 268) (b := PUnit) (stepVerifyCircuit pts h)))
  ++ (wrap.toList.map fun (pts, h) =>
    ("xhat_wrap_circuit",
      wrapTarget (a := Vector Fq 34) (b := PUnit)
        (xhatWrapCircuit (pts.map (#v[·])) (xhatWrapCell h))))
  ++ (wrap2.toList.map fun (pts, h) =>
    ("xhat_wrap_chunks2_circuit",
      wrapTarget (a := Vector Fq 34) (b := PUnit) (xhatWrapCircuit pts (xhatWrapCell h))))
  ++ (wrap.toList.map fun (pts, h) =>
    ("ivp_wrap_circuit",
      wrapTarget (a := Vector Fq 177) (b := PUnit) (ivpWrapCircuit pts (xhatWrapCell h))))
  ++ wrapMains
  ++ (branches.toList.map fun (_, l16, h) =>
    ("xhat_wrap_branches_same_circuit",
      wrapTarget (a := Vector Fq 35) (b := PUnit)
        (xhatBranchesCircuit true l16 l16 (xhatWrapCell h))))
  ++ (branches.toList.map fun (l15, l16, h) =>
    ("xhat_wrap_branches_diff_circuit",
      wrapTarget (a := Vector Fq 35) (b := PUnit)
        (xhatBranchesCircuit false l15 l16 (xhatWrapCell h))))
  ++ (wrap.toList.map fun (pts, h) =>
    ("wrap_verify_circuit", wrapTarget (a := Vector Fq 196) (b := PUnit) (wrapVerifyCircuit pts h)))

/-- Load an `x_hat` Lagrange export when present. Under `KIMCHI_CS_FILTER` a missing export
skips its target (a narrowed PS run regenerates only the selected circuits' exports); in the
unfiltered run — CI — it is an error. -/
def optionalExport {α : Type} (filter : String) (path : System.FilePath)
    (load : System.FilePath → IO α) : IO (Option α) := do
  if ← path.pathExists then
    some <$> load path
  else if filter.isEmpty then
    throw (IO.userError s!"missing export: {path}")
  else
    IO.println s!"· {path.fileName.getD path.toString} not exported: its target is skipped"
    pure none

def main : IO Unit := do
  let dir ← resultsDir
  let fdir := (← IO.getEnv "BULLETPROOF_FIXTURES_DIR").getD "bulletproof-pcs/fixtures"
  let hStep ← blindingBase Bulletproof.IpaPallas.curve s!"{fdir}/ipa_batch_pallas.json"
  let hWrap ← blindingBase Bulletproof.IpaVesta.curve s!"{fdir}/ipa_batch_vesta.json"
  -- `KIMCHI_CS_FILTER` narrows the corpus to targets whose name contains it — for local
  -- validation of one circuit against a partial results dir. Unset (CI) runs the whole corpus.
  let filter := (← IO.getEnv "KIMCHI_CS_FILTER").getD ""
  -- The `x_hat` Lagrange dumps sit in the results dir beside the comparison dumps (they
  -- carry no `purescript` field and no manifest entry, so the other consumers skip them).
  let xhatWrap ← optionalExport filter (dir / "xhat_wrap_lagrange.json") (xhatPoints XhatCurve)
  let xhatWrap2 ← optionalExport filter (dir / "xhat_wrap_chunks2_lagrange.json")
    (xhatPointsChunks XhatCurve 2)
  let xhatStep ← optionalExport filter (dir / "xhat_step_lagrange.json") (xhatPoints XhatStepCurve)
  let ivpStep ← optionalExport filter (dir / "ivp_step_lagrange.json") (xhatPoints XhatStepCurve)
  let xhatBranches ← optionalExport filter (dir / "xhat_wrap_branches_lagrange.json")
    xhatBranchesPoints
  let wrapMains ← wrapMainDumps.filterMapM fun (name, bp, mpv, nc) => do
    let k ← optionalExport filter (dir / s!"{name}_constants.json") (wrapMainConsts nc)
    k.mapM fun k => do
      let some widths := wrapMainWidths? bp mpv k.stepWidths
        | throw (IO.userError s!"{name}: slot counts {k.stepWidths} are not {bp + 1} ≤ {mpv}")
      let some log2s := wrapMainLog2s? bp k.domainLog2s
        | throw (IO.userError s!"{name}: step domains {k.domainLog2s} are not {bp + 1}")
      pure (name, wrapTarget (a := Vector Fq 40) (b := PUnit)
        (wrapMainDumpCircuit bp mpv nc k widths log2s))
  let fullStep ← optionalExport filter (dir / "full_step_lagrange.json")
    (xhatPoints XhatStepCurve)
  let selected := (targets hStep hWrap
    ++ xhatTargets xhatWrap xhatWrap2 xhatStep ivpStep xhatBranches wrapMains fullStep).filter
    fun (n, _) =>
    filter.isEmpty || (n.splitOn filter).length > 1
  let mut failures := 0
  for (name, compare) in selected do
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
  IO.println s!"── CS equality OK ({selected.length} circuits) ──"
