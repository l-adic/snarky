/-
The CS-equality seam: compile the gadget circuits with the Lean kimchi backend and
compare the assembled constraint system — gate types, coefficients, wiring, per-cell
variable ids and public size — against the recorded PureScript dumps (`KimchiFixture.PS`
decodes the JSON schema). The dumps carry no witness: the comparison is on the constraint
system alone.

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
(packages/pickles-circuit-diffs/test/): every circuit built from the
`Basic` gadget vocabulary, the landed gate gadgets (poseidon, endo_scalar,
endo_mul), the gadget-complete pickles sub-circuits (pow2_pow, b_correct,
bullet_reduce_one_step, bullet_reduce_step — composition fixtures, the bullet pair
composing endoInv + endoMul + addComplete), ft_eval0_step (the proved `Pickles.ftEval0Circuit` under
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
`npx spago test -p pickles-circuit-diffs`. CI runs
this check against the exports its own commit just produced.

Run from `formal/`:  lake env lean --run scripts/check_cs.lean

This is a WORKSPACE script rather than a package one: the corpus spans packages — the
`Basic` and gate gadgets come from `snarky`, the linearization circuit from `pickles`,
which requires snarky — so no single package can import every circuit under comparison.
(`KIMCHI_PS_RESULTS_DIR` overrides the default export location).
-/
import Std.Data.HashMap
import KimchiFixture.Cache
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
at the step field's parameters), over the sponge state itself: `SpongeStateVal`'s three cells
are the PS `Vector 3`. -/
def poseidonCircuit (s : SpongeState Fp) : CircuitM Fp C (SpongeState Fp) :=
  poseidon Poseidon.fpParams s

/-- `endo_scalar_step_circuit` (the PS gadget `Snarky.Circuit.Kimchi.EndoScalar.toField`
at 8 rows and the constant Vesta eigenvalue). -/
def endoScalarCircuit (scalar : FVar Fp) : CircuitM Fp C (FVar Fp) :=
  EndoScalar.toField 8 scalar (.const Bulletproof.IpaVesta.curve.lam)

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
circuits are — these are the first fixtures exercising the gadgets IN COMPOSITION. -/

/-- `pow2_pow_step_circuit` (`Pickles.Util.Pow2.pow2PowSquare` at 16 squarings —
sixteen `square` rows chained). -/
def pow2PowCircuit (x : FVar Fp) : CircuitM Fp C PUnit := do
  let _ ← (List.range 16).foldlM (fun acc _ => square acc) x
  pure PUnit.unit

/-- `b_correct_{step,wrap}_circuit`'s input: the claimed `b` is a shifted value `s`, Type1 on
the step side, Type2 on the wrap side. -/
structure BCorrectInput (f s : Type) where
  /-- The 16 raw 128-bit bulletproof challenges. -/
  challenges : Vector (SizedF 128 f) 16
  /-- The evaluation point `ζ`. -/
  zeta : f
  /-- `ζω`. -/
  zetaOmega : f
  /-- The evaluation scale. -/
  evalscale : f
  /-- The claimed `b`. -/
  b : s

/-- The input is its fields, in order. -/
def BCorrectInput.equivProd (f s : Type) :
    BCorrectInput f s ≃ Vector (SizedF 128 f) 16 × f × f × f × s :=
  ⟨fun i => (i.challenges, i.zeta, i.zetaOmega, i.evalscale, i.b),
   fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F s vs : Type} [CircuitType F s vs] :
    CircuitType F (BCorrectInput F s) (BCorrectInput (FVar F) vs) :=
  CircuitType.ofEquiv (BCorrectInput.equivProd F s) (BCorrectInput.equivProd (FVar F) vs)

/-- `b_correct_step_circuit` (PS `bCorrectStepCircuit`): the 16 raw 128-bit challenges
expanded by `Pickles.computeChallenges`, then `Pickles.bCorrectCircuit` against the
Type1-unshifted claim. -/
def bCorrectCircuit (input : UnChecked (BCorrectInput (FVar Fp) (Type1 (FVar Fp)))) :
    CircuitM Fp C PUnit := do
  let i := input.val
  let expanded ← Pickles.computeChallenges (.const Bulletproof.IpaVesta.curve.lam) i.challenges
  let _ ← Pickles.bCorrectCircuit expanded i.zeta i.zetaOmega i.evalscale
    (Type1.fromShiftedCircuit 255 i.b)
  pure PUnit.unit

/-- `b_correct_wrap_circuit` (PS `bCorrectWrapCircuit`): the step layout at the wrap field,
the challenges expanded through `IpaPallas.curve.lam`, the claim Type2-unshifted. -/
def bCorrectWrapCircuit (input : UnChecked (BCorrectInput (FVar Fq) (Type2 (FVar Fq)))) :
    CircuitM Fq Cq PUnit := do
  let i := input.val
  let expanded ← Pickles.computeChallenges (.const Bulletproof.IpaPallas.curve.lam) i.challenges
  let _ ← Pickles.bCorrectCircuit expanded i.zeta i.zetaOmega i.evalscale
    (Type2.fromShiftedCircuit 255 i.b)
  pure PUnit.unit

/-- The step-side `endoInv` scalar-field data: the Pallas group order is prime
(`pallas_card` carries the `Fact` over to the numeral). -/
def pallasOrderPrime : Nat.Prime PALLAS_SCALAR_CARD :=
  Pasta.pallas_card ▸
    (Fact.out : Nat.Prime CompElliptic.Curves.Pasta.Pallas.curve.toAffine.order)

/-- `bullet_reduce_one_step_circuit`'s input. -/
structure BulletReduceOneInput (f : Type) where
  /-- The round's `L`. -/
  l : AffinePoint f
  /-- The round's `R`. -/
  r : AffinePoint f
  /-- The round's raw prechallenge. -/
  u : SizedF 128 f

/-- The input is its fields, in order. -/
def BulletReduceOneInput.equivProd (f : Type) :
    BulletReduceOneInput f ≃ AffinePoint f × AffinePoint f × SizedF 128 f :=
  ⟨fun i => (i.l, i.r, i.u), fun p => ⟨p.1, p.2.1, p.2.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F : Type} : CircuitType F (BulletReduceOneInput F) (BulletReduceOneInput (FVar F)) :=
  CircuitType.ofEquiv (BulletReduceOneInput.equivProd F) (BulletReduceOneInput.equivProd (FVar F))

/-- One IPA fold step (`bullet_reduce_one_step_circuit`, the PS wrapper's inline body):
`endoInv(L, u) + endo(R, u)` — the first fixture composing endoInv, endoMul, and
addComplete. -/
def bulletReduceOneCircuit (input : UnChecked (BulletReduceOneInput (FVar Fp))) :
    CircuitM Fp C PUnit := do
  let i := input.val
  let lScaled ← endoInv Pasta.pallasEndo CompElliptic.Curves.Pasta.Pallas.curve.toAffine
    PALLAS_SCALAR_CARD pallasOrderPrime ((Pasta.pallasLam : ℤ) : ZMod PALLAS_SCALAR_CARD) i.l i.u
  let rScaled ← endoMul Pasta.pallasEndo 32 i.r i.u
  let _ ← addFast .checkFinite lScaled rScaled
  pure PUnit.unit

/-- `bullet_reduce_step_circuit`'s input. -/
structure BulletReduceInput (f : Type) where
  /-- The 15 `(L, R)` pairs. -/
  pairs : Vector (AffinePoint f × AffinePoint f) 15
  /-- The 15 raw round prechallenges. -/
  challenges : Vector (SizedF 128 f) 15

/-- The input is its fields, in order. -/
def BulletReduceInput.equivProd (f : Type) :
    BulletReduceInput f ≃ Vector (AffinePoint f × AffinePoint f) 15 × Vector (SizedF 128 f) 15 :=
  ⟨fun i => (i.pairs, i.challenges), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F : Type} : CircuitType F (BulletReduceInput F) (BulletReduceInput (FVar F)) :=
  CircuitType.ofEquiv (BulletReduceInput.equivProd F) (BulletReduceInput.equivProd (FVar F))

/-- The IPA `lr_prod` fold (`bullet_reduce_step_circuit`, PS `IPA.bulletReduceCircuit`
at 15 pairs): per pair `endoInv(Lᵢ, uᵢ) + endo(Rᵢ, uᵢ)`, then the running
`addComplete` sum. -/
def bulletReduceCircuit (input : UnChecked (BulletReduceInput (FVar Fp))) :
    CircuitM Fp C PUnit := do
  let i := input.val
  let terms ← (i.pairs.zip i.challenges).toList.mapM (fun ((l, r), u) => do
    let lScaled ← endoInv Pasta.pallasEndo CompElliptic.Curves.Pasta.Pallas.curve.toAffine
      PALLAS_SCALAR_CARD pallasOrderPrime ((Pasta.pallasLam : ℤ) : ZMod PALLAS_SCALAR_CARD) l u
    let rScaled ← endoMul Pasta.pallasEndo 32 r u
    addFast .checkFinite lScaled rScaled)
  match terms with
  | [] => pure PUnit.unit
  | head :: tail => do
    let _ ← tail.foldlM (fun acc q => (·.p) <$> addFast .checkFinite acc q.p) head.p
    pure PUnit.unit

/-- A corpus entry's comparison: parse a dump and compare it, `none` when the JSON is not a
comparison dump. -/
abbrev Comparison := Json → Except String (Option (List (String × Bool)))

/-- A corpus entry: parse the dump at the target's field and compare. -/
def target {p : ℕ} [Fact p.Prime]
    {a b avar bvar : Type} [CircuitType (ZMod p) a avar]
    [CheckedType (ZMod p) (KimchiConstraint (ZMod p)) a avar] [CircuitType (ZMod p) b bvar]
    (main : avar → CircuitM (ZMod p) (KimchiConstraint (ZMod p)) bvar) : Comparison := fun j => do
  return (← parseComparisonCs? (m := p) j).map (compareWith (a := a) (b := b) main)

/-- A step-side entry. -/
def stepTarget {a b avar bvar : Type} [CircuitType Fp a avar] [CheckedType Fp C a avar]
    [CircuitType Fp b bvar] (main : avar → CircuitM Fp C bvar) : Comparison :=
  target (a := a) (b := b) main

/-- A wrap-side entry. -/
def wrapTarget {a b avar bvar : Type} [CircuitType Fq a avar] [CheckedType Fq Cq a avar]
    [CircuitType Fq b bvar] (main : avar → CircuitM Fq Cq bvar) : Comparison :=
  target (a := a) (b := b) main

/-! ## The linearization circuit

Transcribes `Pickles.CircuitDiffs.PureScript.LinearizationCommon.linearizationCircuitM`.
The input is OCaml's (`dump_circuit_impl.ml`), not what the constant term needs:
coefficients, `s` and the selectors arrive as `(ζ, ζω)` pairs though only the `ζ`
component of the first two is ever read, and `z`/`s` are not read at all. -/

open Kimchi.Verifier in
/-- The input the linearization and `ft_eval0` dumps share. -/
structure LinearizationInput (f : Type) where
  /-- The 15 witness evaluation pairs. -/
  witnessEvals : Vector (PointEvaluations f) 15
  /-- The 15 coefficient evaluation pairs. -/
  coeffEvals : Vector (PointEvaluations f) 15
  /-- The permutation accumulator's evaluation pair. -/
  zEvals : PointEvaluations f
  /-- The 6 `σ` evaluation pairs. -/
  sigmaEvals : Vector (PointEvaluations f) 6
  /-- The 6 selector evaluation pairs: generic, poseidon, complete-add, var-base-mul, endo-mul,
  endo-mul-scalar. -/
  indexEvals : Vector (PointEvaluations f) 6
  /-- `α`. -/
  alpha : f
  /-- `β`. -/
  beta : f
  /-- `γ`. -/
  gamma : f
  /-- `ζ`. -/
  zeta : f

open Kimchi.Verifier in
/-- The input is its fields, in order. -/
def LinearizationInput.equivProd (f : Type) :
    LinearizationInput f ≃
      Vector (PointEvaluations f) 15 × Vector (PointEvaluations f) 15 × PointEvaluations f ×
        Vector (PointEvaluations f) 6 × Vector (PointEvaluations f) 6 × f × f × f × f :=
  ⟨fun i => (i.witnessEvals, i.coeffEvals, i.zEvals, i.sigmaEvals, i.indexEvals, i.alpha, i.beta,
      i.gamma, i.zeta),
   fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
     p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F : Type} : CircuitType F (LinearizationInput F) (LinearizationInput (FVar F)) :=
  CircuitType.ofEquiv (LinearizationInput.equivProd F) (LinearizationInput.equivProd (FVar F))

open Pickles.Linearization Kimchi.Protocol.Linearization in
/-- The interpreter's inputs from the shared input, `pows` the precomputed α-table. -/
def linearizationInputs {p : ℕ} [Fact p.Prime] (i : LinearizationInput (FVar (ZMod p)))
    (pows : Array (FVar (ZMod p))) : Inputs (ZMod p) :=
  { evals :=
      { w j := (i.witnessEvals.get j).zeta
        wOmega j := (i.witnessEvals.get j).zetaOmega
        coeffs j := (i.coeffEvals.get j).zeta
        z := i.zEvals.zeta
        zOmega := i.zEvals.zetaOmega
        s j := (i.sigmaEvals.get j).zeta
        genericSelector := i.indexEvals[0].zeta
        poseidonSelector := i.indexEvals[1].zeta
        completeAddSelector := i.indexEvals[2].zeta
        mulSelector := i.indexEvals[3].zeta
        emulSelector := i.indexEvals[4].zeta
        endoScalarSelector := i.indexEvals[5].zeta }
    alphaPows n := pows[n]?.getD (.const 0)
    beta := i.beta
    gamma := i.gamma
    jointCombiner := .const 1
    vanishes := .const 1 }

open Pickles.Linearization Kimchi.Protocol.Linearization in
/-- The circuit under comparison, at either side: the domain generator (PS
`domainGenerator`, matching production's recorded `omega`), the endomorphism coefficient
and the MDS matrix all come from `side`. The `zkPoly` and `zeta^n - 1` terms are computed
and DISCARDED: they emit rows the OCaml dump contains, so they are part of the constraint
system being compared even though nothing reads them. -/
def linearizationCircuit {p : ℕ} [Fact p.Prime] (side : Kimchi.Fixture.PS.Side p)
    (domLog2 : Nat) (toks : Array PolishToken)
    (input : UnChecked (LinearizationInput (FVar (ZMod p)))) :
    CircuitM (ZMod p) (KimchiConstraint (ZMod p)) (FVar (ZMod p)) := do
  let i := input.val
  let gen := side.omega (2 ^ domLog2)
  let om1 := gen⁻¹
  let om2 := om1 * om1
  let om3 := om2 * om1
  let pows ← Pickles.Linearization.precomputeAlphaPowers i.alpha
  -- eager zk_polynomial at constant powers, discarded
  let _ ← Pickles.zkPolynomial i.zeta ⟨.const om1, .const om2, .const om3⟩
  -- eager zeta^n - 1, discarded
  let _ ← Snarky.pow i.zeta (2 ^ domLog2)
  evaluate ((linearizationInputs i pows).toEnv side.endo side.mds lookupZero (fun _ => false)
    (fun _ _ => pure (.const 0))) toks

/-! ## The ft_eval0 circuit

Transcribes `Pickles.CircuitDiffs.PureScript.FtEval0Common.ftEval0CircuitM`: the
linearization input plus `p_eval0`, the same `scalars_env` prelude with the `zkPoly` and
`zeta^n − 1` rows now READ, and `Pickles.ftEval0Circuit` — the gadget the faithfulness
theorem is about — fed those as its upstream inputs. The domain is constant in the dump, so
`ω^{n − zkRows}` is the constant `ω⁻³` and the coset shifts are constants. -/

/-- `ft_eval0_step_circuit`'s input: the linearization input and the public-input polynomial
at `ζ`. -/
structure FtEval0Input (f : Type) extends LinearizationInput f where
  /-- `p(ζ)`. -/
  pEval0 : f

/-- The input is its fields, in order. -/
def FtEval0Input.equivProd (f : Type) : FtEval0Input f ≃ LinearizationInput f × f :=
  ⟨fun i => (i.toLinearizationInput, i.pEval0), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F : Type} : CircuitType F (FtEval0Input F) (FtEval0Input (FVar F)) :=
  CircuitType.ofEquiv (FtEval0Input.equivProd F) (FtEval0Input.equivProd (FVar F))

open Pickles.Linearization Kimchi.Protocol.Linearization in
/-- The `ft_eval0` circuit under comparison, at either side. -/
def ftEval0CsCircuit {p : ℕ} [Fact p.Prime] (side : Kimchi.Fixture.PS.Side p)
    (domLog2 : Nat) (toks : Array PolishToken) (shifts : Fin permCols → ZMod p)
    (input : UnChecked (FtEval0Input (FVar (ZMod p)))) :
    CircuitM (ZMod p) (KimchiConstraint (ZMod p)) (FVar (ZMod p)) := do
  let i := input.val
  let gen := side.omega (2 ^ domLog2)
  let om1 := gen⁻¹
  let om2 := om1 * om1
  let om3 := om2 * om1
  let pows ← Pickles.Linearization.precomputeAlphaPowers i.alpha
  -- eager zk_polynomial at constant powers
  let zkPoly ← Pickles.zkPolynomial i.zeta ⟨.const om1, .const om2, .const om3⟩
  -- eager zeta^n - 1
  let zetaToN ← Snarky.pow i.zeta (2 ^ domLog2)
  let ext : Pickles.PermInputs (ZMod p) :=
    { zeta := i.zeta
      pubEval := i.pEval0
      zkPoly := zkPoly
      zetaToNMinus1 := CVar.sub_ zetaToN (.const 1)
      omegaZk := .const om3
      shifts := shifts }
  Pickles.ftEval0Circuit side.endo side.mds toks (fun _ => false) (fun _ _ => pure (.const 0))
    (linearizationInputs i.toLinearizationInput pows) ext

/-! ## The combined inner product circuits

Transcribe `Pickles.CircuitDiffs.PureScript.Cip`: both sides of the check around the proved
gadgets `Pickles.challengePolyEvals` and `Pickles.combinedInnerProduct`. The step side has two
proofs-verified mask booleans first and a Type1 claim; the wrap side no mask and a Type2 claim.
An entry's bit is the mask bit on the step side and the constant `true_` elsewhere, which
`selectField` folds to no row. -/

open Kimchi.Verifier in
/-- The inputs both `cip` sides share. The challenges are already expanded; each 43-entry
evaluation block is in `Evals.In_circuit.to_list` order (`z`, the 6 selectors, the 15 `w`, the
15 coefficients, the 6 `s`). -/
structure CipInput (f : Type) where
  /-- The two previous proofs' challenge vectors. -/
  prevChallenges : Vector (Vector f 16) 2
  /-- `ζ`. -/
  zeta : f
  /-- `ζω`. -/
  zetaw : f
  /-- The polynomial combiner `ξ`. -/
  xi : f
  /-- The evaluation combiner `r`. -/
  r : f
  /-- `ft(ζ)`. -/
  ftEval0 : f
  /-- `ft(ζω)`. -/
  ftEval1 : f
  /-- The public-input polynomial's evaluation pair. -/
  publicEvals : PointEvaluations f
  /-- The evaluation block at `ζ`. -/
  evalsZeta : Vector f 43
  /-- The evaluation block at `ζω`. -/
  evalsZetaw : Vector f 43

open Kimchi.Verifier in
/-- The input is its fields, in order. -/
def CipInput.equivProd (f : Type) :
    CipInput f ≃
      Vector (Vector f 16) 2 × f × f × f × f × f × f × PointEvaluations f × Vector f 43 ×
        Vector f 43 :=
  ⟨fun i => (i.prevChallenges, i.zeta, i.zetaw, i.xi, i.r, i.ftEval0, i.ftEval1, i.publicEvals,
      i.evalsZeta, i.evalsZetaw),
   fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
     p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F : Type} : CircuitType F (CipInput F) (CipInput (FVar F)) :=
  CircuitType.ofEquiv (CipInput.equivProd F) (CipInput.equivProd (FVar F))

open Pickles in
/-- The shared body: the challenge polynomials of both previous proofs at `ζ` then `ζω`, the
two batches, the gadget, and the equality with the unshifted claim. `sg` pairs an `sg`
evaluation with its bit: the mask on the step side, `true_` on the wrap side. -/
def cipCore {p : ℕ} [Fact p.Prime] (c : CipInput (FVar (ZMod p)))
    (sg : Fin 2 → FVar (ZMod p) → BoolVar (ZMod p) × FVar (ZMod p)) (expected : FVar (ZMod p)) :
    CircuitM (ZMod p) (KimchiConstraint (ZMod p)) PUnit := do
  let tagged (l : List (FVar (ZMod p))) : List (BoolVar (ZMod p) × FVar (ZMod p)) :=
    List.zipWith (fun (j : Fin 2) x => sg j x) [0, 1] l
  let sgZeta ← challengePolyEvals c.zeta c.prevChallenges
  let sgZetaw ← challengePolyEvals c.zetaw c.prevChallenges
  let actual ← combinedInnerProduct c.xi c.r
    (buildEvalList (tagged sgZeta.toList) c.publicEvals.zeta c.ftEval0 c.evalsZeta.toList)
    (buildEvalList (tagged sgZetaw.toList) c.publicEvals.zetaOmega c.ftEval1 c.evalsZetaw.toList)
  let _ ← equals expected actual
  pure PUnit.unit

/-- `cip_step_circuit`'s input. -/
structure CipStepInput (f b : Type) where
  /-- The two mask bits (unchecked, OCaml `Boolean.Unsafe.of_cvar`). -/
  mask : Vector b 2
  /-- The inputs both sides share. -/
  shared : CipInput f
  /-- The claim, a Type1 shifted value. -/
  claimed : Type1 f

/-- The input is its fields, in order. -/
def CipStepInput.equivProd (f b : Type) : CipStepInput f b ≃ Vector b 2 × CipInput f × Type1 f :=
  ⟨fun i => (i.mask, i.shared, i.claimed), fun p => ⟨p.1, p.2.1, p.2.2⟩, fun _ => rfl,
   fun _ => rfl⟩

instance {F : Type} [Zero F] [One F] [DecidableEq F] [NeZero (1 : F)] :
    CircuitType F (CipStepInput F Bool) (CipStepInput (FVar F) (BoolVar F)) :=
  CircuitType.ofEquiv (CipStepInput.equivProd F Bool) (CipStepInput.equivProd (FVar F) (BoolVar F))

/-- `cip_step_circuit`. -/
def cipStepCircuit (input : UnChecked (CipStepInput (FVar Fp) (BoolVar Fp))) :
    CircuitM Fp C PUnit :=
  let i := input.val
  cipCore i.shared (fun j x => (i.mask[j], x)) (Type1.fromShiftedCircuit 255 i.claimed)

/-- `cip_wrap_circuit`'s input. -/
structure CipWrapInput (f : Type) where
  /-- The inputs both sides share. -/
  shared : CipInput f
  /-- The claim, a Type2 shifted value. -/
  claimed : Type2 f

/-- The input is its fields, in order. -/
def CipWrapInput.equivProd (f : Type) : CipWrapInput f ≃ CipInput f × Type2 f :=
  ⟨fun i => (i.shared, i.claimed), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F : Type} : CircuitType F (CipWrapInput F) (CipWrapInput (FVar F)) :=
  CircuitType.ofEquiv (CipWrapInput.equivProd F) (CipWrapInput.equivProd (FVar F))

/-- `cip_wrap_circuit`. -/
def cipWrapCircuit (input : UnChecked (CipWrapInput (FVar Fq))) : CircuitM Fq Cq PUnit :=
  let i := input.val
  cipCore i.shared (fun _ x => (true_, x)) (Type2.fromShiftedCircuit 255 i.claimed)

/-! ## The permutation scalar circuits

Transcribe `Pickles.CircuitDiffs.PureScript.PlonkChecksPassed`: `α²¹` by `pow` as the dump
computes it, `Pickles.permScalarCircuit`, and the shifted comparison: the claim against the
Type1 encode of the scalar on the step side, the Type2 decode of the claim against the scalar
on the wrap side. -/

/-- `plonk_checks_passed_{step,wrap}_circuit`'s input: the claimed perm is a shifted value `s`,
Type1 on the step side, Type2 on the wrap side. -/
structure PlonkChecksPassedInput (f s : Type) where
  /-- `α`. -/
  alpha : f
  /-- `β`. -/
  beta : f
  /-- `γ`. -/
  gamma : f
  /-- The permutation vanishing polynomial at `ζ`. -/
  zkPolynomial : f
  /-- `z(ζω)`. -/
  zOmega : f
  /-- `σ₀(ζ)…σ₅(ζ)`. -/
  sigma : Vector f 6
  /-- `w₀(ζ)…w₅(ζ)`. -/
  w : Vector f 6
  /-- The claimed perm. -/
  claimedPerm : s

/-- The input is its fields, in order. -/
def PlonkChecksPassedInput.equivProd (f s : Type) :
    PlonkChecksPassedInput f s ≃ f × f × f × f × f × Vector f 6 × Vector f 6 × s :=
  ⟨fun i => (i.alpha, i.beta, i.gamma, i.zkPolynomial, i.zOmega, i.sigma, i.w, i.claimedPerm),
   fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
     p.2.2.2.2.2.2.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F s vs : Type} [CircuitType F s vs] :
    CircuitType F (PlonkChecksPassedInput F s) (PlonkChecksPassedInput (FVar F) vs) :=
  CircuitType.ofEquiv (PlonkChecksPassedInput.equivProd F s)
    (PlonkChecksPassedInput.equivProd (FVar F) vs)

open Pickles in
/-- The shared body: `α²¹` and the scalar. -/
def permCheckCore {p : ℕ} [Fact p.Prime] {s : Type} (i : PlonkChecksPassedInput (FVar (ZMod p)) s) :
    CircuitM (ZMod p) (KimchiConstraint (ZMod p)) (FVar (ZMod p)) := do
  let a21 ← Snarky.pow i.alpha 21
  permScalarCircuit i.w.get i.sigma.get i.zOmega i.beta i.gamma i.zkPolynomial a21

/-- `plonk_checks_passed_step_circuit`: the Type1 claim against the encoded scalar. -/
def plonkChecksPassedStepCircuit
    (input : UnChecked (PlonkChecksPassedInput (FVar Fp) (Type1 (FVar Fp)))) :
    CircuitM Fp C PUnit := do
  let actual ← permCheckCore input.val
  let _ ← equals input.val.claimedPerm.val (Type1.ofFieldCircuit 255 actual)
  pure PUnit.unit

/-- `plonk_checks_passed_wrap_circuit`: the decoded Type2 claim against the scalar. -/
def plonkChecksPassedWrapCircuit
    (input : UnChecked (PlonkChecksPassedInput (FVar Fq) (Type2 (FVar Fq)))) :
    CircuitM Fq Cq PUnit := do
  let actual ← permCheckCore input.val
  let _ ← equals (Type2.fromShiftedCircuit 255 input.val.claimedPerm) actual
  pure PUnit.unit

/-! ## The challenge expansion circuits

Transcribe `Pickles.CircuitDiffs.PureScript.ExpandPlonk`: `α` and `ζ` expanded through
`EndoScalar.toField` at the side's scalar endomorphism, `β`, `γ` untouched, then `ζω = ω · ζ` at
the side's constant generator, which folds to no row. -/

/-- `expand_plonk_{step,wrap}_circuit`'s input: the four plonk challenges, 128-bit. -/
structure ExpandPlonkInput (f : Type) where
  /-- `α`. -/
  alpha : SizedF 128 f
  /-- `β`. -/
  beta : SizedF 128 f
  /-- `γ`. -/
  gamma : SizedF 128 f
  /-- `ζ`. -/
  zeta : SizedF 128 f

/-- The input is its fields, in order. -/
def ExpandPlonkInput.equivProd (f : Type) :
    ExpandPlonkInput f ≃ SizedF 128 f × SizedF 128 f × SizedF 128 f × SizedF 128 f :=
  ⟨fun i => (i.alpha, i.beta, i.gamma, i.zeta), fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩,
   fun _ => rfl, fun _ => rfl⟩

instance {F : Type} : CircuitType F (ExpandPlonkInput F) (ExpandPlonkInput (FVar F)) :=
  CircuitType.ofEquiv (ExpandPlonkInput.equivProd F) (ExpandPlonkInput.equivProd (FVar F))

/-- The shared body at a side's endomorphism and generator. -/
def expandPlonkCore {p : ℕ} [Fact p.Prime] (endo gen : ZMod p)
    (input : UnChecked (ExpandPlonkInput (FVar (ZMod p)))) :
    CircuitM (ZMod p) (KimchiConstraint (ZMod p)) PUnit := do
  let endoVar : FVar (ZMod p) := .const endo
  let _ ← EndoScalar.toField 8 input.val.alpha.val endoVar
  let zeta ← EndoScalar.toField 8 input.val.zeta.val endoVar
  let _ ← mul (.const gen) zeta
  pure PUnit.unit

/-- `expand_plonk_step_circuit`. -/
def expandPlonkStepCircuit (input : UnChecked (ExpandPlonkInput (FVar Fp))) :
    CircuitM Fp C PUnit :=
  expandPlonkCore Bulletproof.IpaVesta.curve.lam
    (Kimchi.Verifier.domainGenerator Bulletproof.IpaVesta.curve 16) input

/-- `expand_plonk_wrap_circuit`. -/
def expandPlonkWrapCircuit (input : UnChecked (ExpandPlonkInput (FVar Fq))) :
    CircuitM Fq Cq PUnit :=
  expandPlonkCore Bulletproof.IpaPallas.curve.lam
    (Kimchi.Verifier.domainGenerator Bulletproof.IpaPallas.curve 15) input

/-! ## The Pseudo selection circuits

Transcribe `Pickles.CircuitDiffs.PureScript.PseudoCircuits`: `Pickles.oneHotVector` of the
index, `Pickles.Pseudo.mask` and `Pickles.Pseudo.choose` behind it, on either field, and
`Pickles.toDomain` over the three wrap domains with the selected vanishing polynomial at `ζ`. -/

/-- `pseudo_mask_n{1,3}`'s input: the index to select, then the `n` values to mask. -/
structure PseudoMaskInput (n : ℕ) (f : Type) where
  /-- The index to select. -/
  index : f
  /-- The values to mask. -/
  values : Vector f n

/-- The input is its fields, in order. -/
def PseudoMaskInput.equivProd (n : ℕ) (f : Type) : PseudoMaskInput n f ≃ f × Vector f n :=
  ⟨fun i => (i.index, i.values), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F : Type} {n : ℕ} : CircuitType F (PseudoMaskInput n F) (PseudoMaskInput n (FVar F)) :=
  CircuitType.ofEquiv (PseudoMaskInput.equivProd n F) (PseudoMaskInput.equivProd n (FVar F))

section PseudoCircuits

variable {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]

/-- `one_hot_n{n}`: the one-hot vector of the index over `n` entries. -/
def oneHotCircuit [ConstraintHolds F c] (n : ℕ) (index : FVar F) : CircuitM F c PUnit := do
  let _ ← Pickles.oneHotVector n index
  pure PUnit.unit

/-- The one-hot of `index` over `n` entries masking `xs`. -/
def pseudoMask [ConstraintHolds F c] (n : ℕ) (index : FVar F) (xs : List (FVar F)) :
    CircuitM F c PUnit := do
  let bits ← Pickles.oneHotVector n index
  let _ ← Pickles.Pseudo.mask bits.toList xs
  pure PUnit.unit

/-- `pseudo_mask_n{n}`, `n` ∈ {1, 3}: the input's values masked. -/
def pseudoMaskCircuit [ConstraintHolds F c] (n : ℕ)
    (input : UnChecked (PseudoMaskInput n (FVar F))) : CircuitM F c PUnit :=
  pseudoMask n input.val.index input.val.values.toList

/-- `pseudo_mask_n17`: the constants `0 … 16` masked. -/
def pseudoMaskConstCircuit [ConstraintHolds F c] (index : FVar F) : CircuitM F c PUnit :=
  pseudoMask 17 index ((List.range 17).map fun j => .const (j : F))

/-- `pseudo_choose_n{n}`: the one-hot of the index over `n` entries choosing among the constants
`ks`. -/
def pseudoChooseCircuit [ConstraintHolds F c] (n : ℕ) (ks : List ℕ) (index : FVar F) :
    CircuitM F c PUnit := do
  let bits ← Pickles.oneHotVector n index
  let _ ← Pickles.Pseudo.choose bits.toList ks fun k => .const (k : F)
  pure PUnit.unit

end PseudoCircuits

/-- `pseudo_to_domain_wrap_circuit`'s input: the domain index and `ζ`. -/
structure PseudoToDomainInput (f : Type) where
  /-- The domain index. -/
  index : f
  /-- `ζ`. -/
  zeta : f

/-- The input is its fields, in order. -/
def PseudoToDomainInput.equivProd (f : Type) : PseudoToDomainInput f ≃ f × f :=
  ⟨fun i => (i.index, i.zeta), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F : Type} : CircuitType F (PseudoToDomainInput F) (PseudoToDomainInput (FVar F)) :=
  CircuitType.ofEquiv (PseudoToDomainInput.equivProd F) (PseudoToDomainInput.equivProd (FVar F))

/-- `pseudo_to_domain_wrap_circuit`: the one-hot of the index over the wrap domains `2^13`,
`2^14`, `2^15`, and the selected domain's vanishing polynomial at `ζ`. -/
def pseudoToDomainWrapCircuit (input : UnChecked (PseudoToDomainInput (FVar Fq))) :
    CircuitM Fq Cq PUnit := do
  let which ← Pickles.oneHotVector 3 input.val.index
  let d ← Pickles.toDomain (Kimchi.Verifier.domainGenerator Bulletproof.IpaPallas.curve)
    which.toList [13, 14, 15]
  let _ ← d.vanishingPolynomial input.val.zeta
  pure PUnit.unit

/-! ## The wrap circuit's branch selection

Transcribe `Pickles.CircuitDiffs.PureScript.PseudoCircuits`' `utils_ones_vector_n16` (the slot
mask, `Pickles.onesVector`, on either field) and `choose_key_n1_wrap` (`Pickles.chooseKey` over
one branch whose key is Vesta's generator `(1, √6)` in every commitment). -/

/-- `utils_ones_vector_n16`: the mask over 16 slots, the first zero at `firstZero`. -/
def onesVectorN16Circuit {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (firstZero : FVar F) : CircuitM F c PUnit := do
  let _ ← Pickles.onesVector firstZero 16
  pure PUnit.unit

/-- `choose_key_n1_wrap_circuit`: the one-hot of the branch over one branch choosing its key. -/
def chooseKeyN1WrapCircuit (branch : FVar Fq) : CircuitM Fq Cq PUnit := do
  let bits ← Pickles.oneHotVector 1 branch
  let g : AffinePoint (FVar Fq) :=
    ⟨.const 1,
      .const 11426906929455361843568202299992114520848200991084027513389447476559454104162⟩
  let ch : Vector (AffinePoint (FVar Fq)) 1 := #v[g]
  let key : Pickles.VkComms 1 (AffinePoint (FVar Fq)) :=
    ⟨Vector.replicate _ ch, Vector.replicate _ ch, ch, ch, ch, ch, ch, ch⟩
  let _ ← Pickles.chooseKey bits #v[key]
  pure PUnit.unit

/-! ## The fr-sponge slices

The PS harnesses' fr-sponge slices (`SpongeChallenges`: the challenge digests and the schedule
with `ξ`, `r`) are strict sub-circuits of the `finalize_other_proof` targets, so their
byte-equality is checked there rather than as separate interpreter passes. -/

/-! ## The fq-sponge transcript circuit

Transcribes `Pickles.CircuitDiffs.PureScript.FqSpongeTranscript`: the group side's
Fiat–Shamir schedule of `incrementally_verify_proof`, `Pickles.fqSpongeTranscript` at the
step field's sponge and range-check endomorphism, `x_hat` handed in as the input point. -/

/-- `fq_sponge_transcript_step_circuit`'s input, at one chunk. -/
structure FqSpongeStepInput (f : Type) where
  /-- The index digest. -/
  indexDigest : f
  /-- The two `sg_old` points. -/
  sgOld : Vector (AffinePoint f) 2
  /-- The public-input commitment. -/
  xHat : AffinePoint f
  /-- The 15 witness commitments. -/
  wComm : Vector (Vector (AffinePoint f) 1) 15
  /-- The permutation commitment. -/
  zComm : Vector (AffinePoint f) 1
  /-- The 7 quotient chunks. -/
  tComm : Vector (AffinePoint f) 7

/-- The input is its fields, in order. -/
def FqSpongeStepInput.equivProd (f : Type) :
    FqSpongeStepInput f ≃
      f × Vector (AffinePoint f) 2 × AffinePoint f × Vector (Vector (AffinePoint f) 1) 15 ×
        Vector (AffinePoint f) 1 × Vector (AffinePoint f) 7 :=
  ⟨fun i => (i.indexDigest, i.sgOld, i.xHat, i.wComm, i.zComm, i.tComm),
   fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F : Type} : CircuitType F (FqSpongeStepInput F) (FqSpongeStepInput (FVar F)) :=
  CircuitType.ofEquiv (FqSpongeStepInput.equivProd F) (FqSpongeStepInput.equivProd (FVar F))

/-- `fq_sponge_transcript_step_circuit`. -/
def fqSpongeTranscriptStepCircuit (input : UnChecked (FqSpongeStepInput (FVar Fp))) :
    CircuitM Fp C PUnit := do
  let i := input.val
  let _ ← Pickles.fqSpongeTranscript Bulletproof.IpaVesta.curve.frSponge.params
    (.const Bulletproof.IpaVesta.curve.lam) i.indexDigest i.sgOld (pure #v[i.xHat]) i.wComm
    i.zComm i.tComm
  pure PUnit.unit


/-- `fq_sponge_transcript_wrap_circuit`'s input, at one chunk. The mask bits are cells, read
unchecked (OCaml `Boolean.Unsafe.of_cvar`). -/
structure FqSpongeWrapInput (f : Type) where
  /-- The two `sg_old` mask bits. -/
  sgOldMask : Vector f 2
  /-- The index digest. -/
  indexDigest : f
  /-- The two `sg_old` points. -/
  sgOld : Vector (AffinePoint f) 2
  /-- The public-input commitment. -/
  xHat : AffinePoint f
  /-- The 15 witness commitments. -/
  wComm : Vector (Vector (AffinePoint f) 1) 15
  /-- The permutation commitment. -/
  zComm : Vector (AffinePoint f) 1
  /-- The 7 quotient chunks. -/
  tComm : Vector (AffinePoint f) 7

/-- The input is its fields, in order. -/
def FqSpongeWrapInput.equivProd (f : Type) :
    FqSpongeWrapInput f ≃
      Vector f 2 × f × Vector (AffinePoint f) 2 × AffinePoint f ×
        Vector (Vector (AffinePoint f) 1) 15 × Vector (AffinePoint f) 1 ×
        Vector (AffinePoint f) 7 :=
  ⟨fun i => (i.sgOldMask, i.indexDigest, i.sgOld, i.xHat, i.wComm, i.zComm, i.tComm),
   fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩,
   fun _ => rfl, fun _ => rfl⟩

instance {F : Type} : CircuitType F (FqSpongeWrapInput F) (FqSpongeWrapInput (FVar F)) :=
  CircuitType.ofEquiv (FqSpongeWrapInput.equivProd F) (FqSpongeWrapInput.equivProd (FVar F))

/-- `fq_sponge_transcript_wrap_circuit`: each `sg_old` point under its mask bit. -/
def fqSpongeTranscriptWrapCircuit (input : UnChecked (FqSpongeWrapInput (FVar Fq))) :
    CircuitM Fq Cq PUnit := do
  let i := input.val
  let _ ← Pickles.fqSpongeTranscriptOpt Bulletproof.IpaPallas.curve.frSponge.params
    (.const Bulletproof.IpaPallas.curve.lam) i.indexDigest
    (Vector.zipWith (fun b p => (BoolVar.unchecked b, p)) i.sgOldMask i.sgOld) #v[i.xHat] i.wComm
    i.zComm i.tComm
  pure PUnit.unit

/-! ## The `check_bulletproof` circuits

Transcribe `Pickles.CircuitDiffs.PureScript.CheckBulletproofStep` and `CheckBulletproofWrap`:
`Pickles.checkBulletproof` from a sponge at `sponge_before_evaluations` (mode `Squeezed 1`) on
either side, the step side at `IpaScalarOps.step`/`IpaEndo.pallas`, the wrap side at
`IpaScalarOps.wrap`/`IpaEndo.vesta` with the two `sg_old` bases under their mask bits. The 47
bases are the two `sg_old`, `x_hat`, `ft_comm`, `z_comm`, the six index commitments, the 15
`w_comm`, the 15 coefficient commitments and the six `σ` commitments. The SRS blinding base `h`
is a constant on both sides, as in production. -/

/-- `check_bulletproof_step_circuit`'s input, at 15 rounds: the opening and the deferred `cip`,
`b`, Type2-shifted and split. -/
structure CheckBulletproofStepInput (f s : Type) where
  /-- The sponge state at `sponge_before_evaluations`. -/
  sponge : Vector f 3
  /-- The opening's `ξ` prechallenge. -/
  xi : SizedF 128 f
  /-- The 47 MSM bases. -/
  bases : Vector (AffinePoint f) 47
  /-- The `(L, R)` pairs. -/
  lr : Vector (AffinePoint f × AffinePoint f) 15
  /-- `δ`. -/
  delta : AffinePoint f
  /-- The challenge polynomial commitment. -/
  sg : AffinePoint f
  /-- `z₁`. -/
  z1 : s
  /-- `z₂`. -/
  z2 : s
  /-- The deferred combined inner product. -/
  combinedInnerProduct : s
  /-- The deferred `b`. -/
  b : s

/-- The input is its fields, in order. -/
def CheckBulletproofStepInput.equivProd (f s : Type) :
    CheckBulletproofStepInput f s ≃
      Vector f 3 × SizedF 128 f × Vector (AffinePoint f) 47 ×
        Vector (AffinePoint f × AffinePoint f) 15 × AffinePoint f × AffinePoint f × s × s × s × s :=
  ⟨fun i => (i.sponge, i.xi, i.bases, i.lr, i.delta, i.sg, i.z1, i.z2, i.combinedInnerProduct,
      i.b),
   fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
     p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F s vs : Type} [CircuitType F s vs] :
    CircuitType F (CheckBulletproofStepInput F s) (CheckBulletproofStepInput (FVar F) vs) :=
  CircuitType.ofEquiv (CheckBulletproofStepInput.equivProd F s)
    (CheckBulletproofStepInput.equivProd (FVar F) vs)

/-- `check_bulletproof_step_circuit`: the bases unmasked. -/
def checkBulletproofStepCircuit (blindingH : AffinePoint (FVar Fp))
    (input : UnChecked
      (CheckBulletproofStepInput (FVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))) :
    CircuitM Fp C PUnit := do
  let i := input.val
  let sv : SpongeVar Fp := ⟨⟨i.sponge[0], i.sponge[1], i.sponge[2]⟩, .squeezed 1⟩
  let _ ← Pickles.checkBulletproof Pickles.IpaScalarOps.step Pickles.IpaEndo.pallas
    Bulletproof.IpaVesta.curve.frSponge.params (.const Bulletproof.IpaVesta.curve.lam)
    Pickles.groupMapParamsPallas (fun _ => none) sv (i.bases.toList.map (·, none))
    { xi := i.xi
      deferred := { combinedInnerProduct := i.combinedInnerProduct, b := i.b }
      opening := { lr := i.lr, z1 := i.z1, z2 := i.z2, delta := i.delta, sg := i.sg }
      blindingGenerator := blindingH }
  pure PUnit.unit

/-! ## OCaml's hlist order

The deferred values as OCaml's `to_hlist` lays them out, shared by the per-proof witness and the
finalize inputs. -/

/-- Deferred values at `k` rounds in OCaml's hlist order: `α`, `β`, `γ`, `ζ`, `ζ^{2^k}`, `ζⁿ`,
`perm`, `cip`, `b`, `ξ`, the round challenges. -/
abbrev DeferredHlist (k : ℕ) (f s : Type) : Type :=
  SizedF 128 f × SizedF 128 f × SizedF 128 f × SizedF 128 f × s × s × s × s × s × SizedF 128 f ×
    Vector (SizedF 128 f) k

/-- The deferred values as their hlist. -/
def DeferredHlist.of {k : ℕ} {f s : Type} (dv : Pickles.DeferredValues k f s) :
    DeferredHlist k f s :=
  (dv.plonk.alpha, dv.plonk.beta, dv.plonk.gamma, dv.plonk.zeta, dv.plonk.zetaToSrsLength,
    dv.plonk.zetaToDomainSize, dv.plonk.perm, dv.combinedInnerProduct, dv.b, dv.xi,
    dv.bulletproofChallenges)

/-- The deferred values from their hlist. -/
def DeferredHlist.to {k : ℕ} {f s : Type} (d : DeferredHlist k f s) :
    Pickles.DeferredValues k f s :=
  { plonk := { alpha := d.1, beta := d.2.1, gamma := d.2.2.1, zeta := d.2.2.2.1,
               zetaToSrsLength := d.2.2.2.2.1, zetaToDomainSize := d.2.2.2.2.2.1,
               perm := d.2.2.2.2.2.2.1 }
    combinedInnerProduct := d.2.2.2.2.2.2.2.1, b := d.2.2.2.2.2.2.2.2.1
    xi := d.2.2.2.2.2.2.2.2.2.1, bulletproofChallenges := d.2.2.2.2.2.2.2.2.2.2 }

/-- A wrap statement's deferred values at 16 rounds in OCaml's hlist order: the deferred values,
the mask, the domain's `log2`. -/
abbrev WrapDeferredHlist (f b : Type) : Type := DeferredHlist 16 f (Type1 f) × Vector b 2 × f

/-- The wrap deferred values as their hlist. -/
def WrapDeferredHlist.of {f b : Type} (dv : Pickles.WrapDeferredValues 16 f b (Type1 f)) :
    WrapDeferredHlist f b :=
  (.of dv.toDeferredValues, dv.branchData.proofsVerifiedMask, dv.branchData.domainLog2)

/-- The wrap deferred values from their hlist. -/
def WrapDeferredHlist.to {f b : Type} (d : WrapDeferredHlist f b) :
    Pickles.WrapDeferredValues 16 f b (Type1 f) :=
  { toDeferredValues := d.1.to, branchData := ⟨d.2.2, d.2.1⟩ }

/-! ## The `finalize_other_proof` circuits

Transcribe `Pickles.CircuitDiffs.PureScript.FopStep` and `FopWrap`: the whole scalar-side
check on either side, `Pickles.finalizeOtherProofStep` at the step field's parameters and
`Pickles.finalizeOtherProofWrap` at the wrap field's, the wrap side's vanishing polynomial by
`pow2PowMul` as the PS harness passes it. -/

/-- `finalize_other_proof{,_chunks2}_step_circuit`'s input at `nc` chunks: the wrap statement's
deferred values in OCaml's hlist order, the evaluations (each column its `ζ` chunks then its
`ζω` chunks), the two previous challenge vectors and the sponge digest. -/
structure FopStepInput (nc : ℕ) (f b : Type) where
  /-- The wrap statement's deferred values. -/
  deferredValues : Pickles.WrapDeferredValues 16 f b (Type1 f)
  /-- The evaluations. -/
  evals : Pickles.AllocEvals nc f
  /-- The previous challenge vectors. -/
  prevChallenges : Vector (Vector f 16) 2
  /-- The sponge digest before evaluations. -/
  spongeDigest : f

/-- The input is its fields in the dumps' order. -/
def FopStepInput.equivProd (nc : ℕ) (f b : Type) :
    FopStepInput nc f b ≃
      WrapDeferredHlist f b × Pickles.AllocEvals nc f × Vector (Vector f 16) 2 × f :=
  ⟨fun i => (.of i.deferredValues, i.evals, i.prevChallenges, i.spongeDigest),
   fun p => ⟨p.1.to, p.2.1, p.2.2.1, p.2.2.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F : Type} {nc : ℕ} [Zero F] [One F] [DecidableEq F] [NeZero (1 : F)] :
    CircuitType F (FopStepInput nc F Bool) (FopStepInput nc (FVar F) (BoolVar F)) :=
  CircuitType.ofEquiv (FopStepInput.equivProd nc F Bool)
    (FopStepInput.equivProd nc (FVar F) (BoolVar F))

/-- The step side at `nc` chunks and the dump's one known domain of `log2 = 16`: the deferred
values always finalized, the mask and the domain's `log2` the statement's. `zk_rows` follows the
chunk count. -/
def fopStepCircuit {nc : ℕ} (input : UnChecked (FopStepInput nc (FVar Fp) (BoolVar Fp))) :
    CircuitM Fp C PUnit := do
  let i := input.val
  let dv := i.deferredValues
  let _ ← Pickles.finalizeOtherProofStep (PicklesFixture.fopStepParams nc)
    [⟨16, Kimchi.Verifier.domainGenerator Bulletproof.IpaVesta.curve 16⟩]
    { deferredValues := dv.toDeferredValues, shouldFinalize := true_
      spongeDigestBeforeEvaluations := i.spongeDigest }
    i.evals.toChunked dv.branchData.proofsVerifiedMask i.prevChallenges dv.branchData.domainLog2
  pure PUnit.unit

/-- A wrap-side finalize input at `k` rounds: the step proof's deferred values in OCaml's hlist
order, shifted values `s`, the evaluations, the two previous challenge vectors and the sponge
digest. -/
structure FopWrapInput (k : ℕ) (f s : Type) where
  /-- The step proof's deferred values. -/
  deferredValues : Pickles.DeferredValues k f s
  /-- The evaluations. -/
  evals : Pickles.AllocEvals 1 f
  /-- The previous challenge vectors. -/
  prevChallenges : Vector (Vector f k) 2
  /-- The sponge digest before evaluations. -/
  spongeDigest : f

/-- The input is its fields in the dumps' order. -/
def FopWrapInput.equivProd (k : ℕ) (f s : Type) :
    FopWrapInput k f s ≃
      DeferredHlist k f s × Pickles.AllocEvals 1 f × Vector (Vector f k) 2 × f :=
  ⟨fun i => (.of i.deferredValues, i.evals, i.prevChallenges, i.spongeDigest),
   fun p => ⟨p.1.to, p.2.1, p.2.2.1, p.2.2.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F s vs : Type} {k : ℕ} [CircuitType F s vs] :
    CircuitType F (FopWrapInput k F s) (FopWrapInput k (FVar F) vs) :=
  CircuitType.ofEquiv (FopWrapInput.equivProd k F s) (FopWrapInput.equivProd k (FVar F) vs)

/-- `finalize_other_proof_wrap_circuit`: the wrap side at the dump's constant domain of
`log2 = 15` and 16 challenges, the deferred values always finalized, `ζⁿ − 1` by
`pow2PowMul`. -/
def finalizeOtherProofWrapCircuit
    (input : UnChecked (FopWrapInput 16 (FVar Fq) (Type2 (FVar Fq)))) : CircuitM Fq Cq PUnit := do
  let i := input.val
  let _ ← Pickles.finalizeOtherProofWrap fopWrapParams
    (.const (Kimchi.Verifier.domainGenerator Bulletproof.IpaPallas.curve 15))
    (fun z => do let t ← Pickles.pow2PowMul z 15; pure (CVar.sub_ t (.const 1)))
    { deferredValues := i.deferredValues, shouldFinalize := true_
      spongeDigestBeforeEvaluations := i.spongeDigest }
    i.evals.toChunked i.prevChallenges
  pure PUnit.unit

/-- One slot of `wrap_finalize_n2_circuit`'s input: `finalize_other_proof_wrap_circuit`'s input
at the wrap circuit's 15 rounds, then `shouldFinalize` and the slot's wrap domain index. -/
structure WrapFinalizeSlotInput (f b : Type) where
  /-- The slot's finalize input. -/
  fop : FopWrapInput 15 f (Type2 f)
  /-- Whether the slot's proof is finalized. -/
  shouldFinalize : b
  /-- The slot's wrap domain index. -/
  domainIndex : f

/-- The slot is its fields, in order. -/
def WrapFinalizeSlotInput.equivProd (f b : Type) :
    WrapFinalizeSlotInput f b ≃ FopWrapInput 15 f (Type2 f) × b × f :=
  ⟨fun i => (i.fop, i.shouldFinalize, i.domainIndex), fun p => ⟨p.1, p.2.1, p.2.2⟩,
   fun _ => rfl, fun _ => rfl⟩

instance {F : Type} [Zero F] [One F] [DecidableEq F] [NeZero (1 : F)] :
    CircuitType F (WrapFinalizeSlotInput F Bool) (WrapFinalizeSlotInput (FVar F) (BoolVar F)) :=
  CircuitType.ofEquiv (WrapFinalizeSlotInput.equivProd F Bool)
    (WrapFinalizeSlotInput.equivProd (FVar F) (BoolVar F))

/-- `wrap_finalize_n2_circuit`'s input: the branch index, then the two slots. -/
structure WrapFinalizeInput (f b : Type) where
  /-- The branch index. -/
  branchIndex : f
  /-- The two slots. -/
  slots : Vector (WrapFinalizeSlotInput f b) 2

/-- The input is its fields, in order. -/
def WrapFinalizeInput.equivProd (f b : Type) :
    WrapFinalizeInput f b ≃ f × Vector (WrapFinalizeSlotInput f b) 2 :=
  ⟨fun i => (i.branchIndex, i.slots), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F : Type} [Zero F] [One F] [DecidableEq F] [NeZero (1 : F)] :
    CircuitType F (WrapFinalizeInput F Bool) (WrapFinalizeInput (FVar F) (BoolVar F)) :=
  CircuitType.ofEquiv (WrapFinalizeInput.equivProd F Bool)
    (WrapFinalizeInput.equivProd (FVar F) (BoolVar F))

/-- `wrap_finalize_n2_circuit`: `Pickles.wrapFinalizePrevProofs` at two branches and two slots.
Branch 0's slots are pinned to domain indices `[1, 1]`, branch 1's to `[0, 2]`. -/
def wrapFinalizeN2Circuit (input : UnChecked (WrapFinalizeInput (FVar Fq) (BoolVar Fq))) :
    CircuitM Fq Cq PUnit := do
  let i := input.val
  let whichBranch ← Pickles.oneHotVector 2 i.branchIndex
  let slot (s : WrapFinalizeSlotInput (FVar Fq) (BoolVar Fq)) (pins : Vector (Option ℕ) 2) :
      Pickles.WrapFinalizeSlot 2 15 1 Fq :=
    { domainIndex := s.domainIndex, pins
      unfinalized := { deferredValues := s.fop.deferredValues, shouldFinalize := s.shouldFinalize
                       spongeDigestBeforeEvaluations := s.fop.spongeDigest }
      evals := s.fop.evals.toChunked
      prevChallenges := s.fop.prevChallenges }
  let _ ← Pickles.wrapFinalizePrevProofs fopWrapParams whichBranch
    #v[slot i.slots[0] #v[some 1, some 0], slot i.slots[1] #v[some 1, some 2]]
  pure PUnit.unit

/-! ## The wrap column

The library gadgets the wrap-side dumps exercise, at `Fq`: the group map at Vesta's
parameters, and the linearization over the wrap token stream. -/

/-- `group_map_wrap_circuit` (the group-map gadget at the wrap field and Vesta parameters;
the dump carries no witness, so the advice is inert here). -/
def groupMapCircuitFq (input : FVar Fq) : CircuitM Fq Cq PUnit := do
  let _ ← groupMapCircuit (fun _ => none) Pickles.groupMapParamsVesta input
  pure ⟨⟩

/-- `check_bulletproof_wrap_circuit`'s input, at 16 rounds: the two `sg_old` mask bits after
`ξ`, the opening and the deferred `cip`, `b` Type1-shifted. -/
structure CheckBulletproofWrapInput (f b s : Type) where
  /-- The sponge state at `sponge_before_evaluations`. -/
  sponge : Vector f 3
  /-- The opening's `ξ` prechallenge. -/
  xi : SizedF 128 f
  /-- The two `sg_old` mask bits. -/
  sgOldMask : Vector b 2
  /-- The 47 MSM bases. -/
  bases : Vector (AffinePoint f) 47
  /-- The `(L, R)` pairs. -/
  lr : Vector (AffinePoint f × AffinePoint f) 16
  /-- `δ`. -/
  delta : AffinePoint f
  /-- The challenge polynomial commitment. -/
  sg : AffinePoint f
  /-- `z₁`. -/
  z1 : s
  /-- `z₂`. -/
  z2 : s
  /-- The deferred combined inner product. -/
  combinedInnerProduct : s
  /-- The deferred `b`. -/
  b : s

/-- The input is its fields, in order. -/
def CheckBulletproofWrapInput.equivProd (f b s : Type) :
    CheckBulletproofWrapInput f b s ≃
      Vector f 3 × SizedF 128 f × Vector b 2 × Vector (AffinePoint f) 47 ×
        Vector (AffinePoint f × AffinePoint f) 16 × AffinePoint f × AffinePoint f × s × s × s × s :=
  ⟨fun i => (i.sponge, i.xi, i.sgOldMask, i.bases, i.lr, i.delta, i.sg, i.z1, i.z2,
      i.combinedInnerProduct, i.b),
   fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
     p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2⟩,
   fun _ => rfl, fun _ => rfl⟩

instance {F s vs : Type} [Zero F] [One F] [DecidableEq F] [NeZero (1 : F)] [CircuitType F s vs] :
    CircuitType F (CheckBulletproofWrapInput F Bool s)
      (CheckBulletproofWrapInput (FVar F) (BoolVar F) vs) :=
  CircuitType.ofEquiv (CheckBulletproofWrapInput.equivProd F Bool s)
    (CheckBulletproofWrapInput.equivProd (FVar F) (BoolVar F) vs)

/-- `check_bulletproof_wrap_circuit`: the two `sg_old` bases under their mask bits. -/
def checkBulletproofWrapCircuit (blindingH : AffinePoint (FVar Fq))
    (input : UnChecked (CheckBulletproofWrapInput (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))) :
    CircuitM Fq Cq PUnit := do
  let i := input.val
  let sv : SpongeVar Fq := ⟨⟨i.sponge[0], i.sponge[1], i.sponge[2]⟩, .squeezed 1⟩
  let masks : Vector (Option (BoolVar Fq)) 47 :=
    i.sgOldMask.map some ++ Vector.replicate 45 (none : Option (BoolVar Fq))
  let _ ← Pickles.checkBulletproof Pickles.IpaScalarOps.wrap Pickles.IpaEndo.vesta
    Bulletproof.IpaPallas.curve.frSponge.params (.const Bulletproof.IpaPallas.curve.lam)
    Pickles.groupMapParamsVesta (fun _ => none) sv (i.bases.zip masks).toList
    { xi := i.xi
      deferred := { combinedInnerProduct := i.combinedInnerProduct, b := i.b }
      opening := { lr := i.lr, z1 := i.z1, z2 := i.z2, delta := i.delta, sg := i.sg }
      blindingGenerator := blindingH }
  pure PUnit.unit

/-! ## The public-input commitment (`x_hat`)

The wrap-side `x_hat` MSM (`Pickles.publicInputCommitFull`) against the PS `Xhat` harness's
`xhat_wrap_circuit`. The 34 Vesta Lagrange bases and blinding `h` are SRS constants Lean
cannot compute; they arrive in the dump's `xhat` constants (`xhatOf`). The input is the step
statement in allocation order, its leaves `Pickles.StepStatement.packed` and its table
`Pickles.XhatTable.ofKey`, which derives the shift corrections from the bases. -/

/-- The step statement the wrap-side harnesses take, one slot at 15 rounds: each slot in
allocation order (`Pickles.AllocUnfinalized`), its shifted claims split. -/
abbrev WrapStepStatement (f b : Type) : Type :=
  Pickles.StepStatement (Pickles.AllocUnfinalized 15 f b (Type2 (SplitField f b))) f 1

/-- The statement with its slots as unfinalized proofs. -/
def WrapStepStatement.unfinalized (st : WrapStepStatement (FVar Fq) (BoolVar Fq)) :
    Pickles.StepStatement
      (Pickles.UnfinalizedProof 15 (FVar Fq) (BoolVar Fq)
        (Type2 (SplitField (FVar Fq) (BoolVar Fq))))
      (FVar Fq) 1 :=
  ⟨⟨st.proofState.unfinalizedProofs.map (·.toUnfinalized), st.proofState.messagesForNextStepProof⟩,
    st.messagesForNextWrapProof⟩

/-- `xhat_wrap_circuit` (one chunk) and `xhat_wrap_chunks2_circuit` (two):
`Pickles.publicInputCommitFull` over the packed statement's leaves at `nc` chunks — the boolean
leaves constrain their own bits inside the gadget. -/
def xhatWrapCircuit {nc : ℕ}
    (pts : Vector (Vector XhatWrapCurve.Point nc)
      (CircuitType.size Fp (Pickles.StepStatement (Pickles.UnfVal 15) Fp 1)))
    (h : AffinePoint (FVar Fq)) (input : UnChecked (WrapStepStatement (FVar Fq) (BoolVar Fq))) :
    CircuitM Fq Cq PUnit := do
  let ks := input.val.unfinalized.packed
  let _ ← Pickles.publicInputCommitFull h
    (Pickles.packLeavesOf ks (Pickles.XhatTable.ofKey (C := XhatWrapCurve) ks pts))
  pure PUnit.unit

/-- `xhat_wrap_branches_{same,diff}_circuit`'s input: the branch index over two branches, then
`xhat_wrap_circuit`'s statement. -/
structure XhatBranchesInput (f b : Type) where
  /-- The branch index. -/
  branchIndex : f
  /-- The statement. -/
  statement : WrapStepStatement f b

/-- The input is its fields, in order. -/
def XhatBranchesInput.equivProd (f b : Type) :
    XhatBranchesInput f b ≃ f × WrapStepStatement f b :=
  ⟨fun i => (i.branchIndex, i.statement), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F : Type} [Zero F] [One F] [DecidableEq F] [NeZero (1 : F)] :
    CircuitType F (XhatBranchesInput F Bool) (XhatBranchesInput (FVar F) (BoolVar F)) :=
  CircuitType.ofEquiv (XhatBranchesInput.equivProd F Bool)
    (XhatBranchesInput.equivProd (FVar F) (BoolVar F))

/-- `xhat_wrap_branches_{same,diff}_circuit`: the statement committed by
`Pickles.publicInputCommitMasked` over the branches' Lagrange bases `pts0`/`pts1`, `shared` when
the branches share one step domain. -/
def xhatBranchesCircuit (shared : Bool) (pts0 pts1 : Array XhatWrapCurve.Point)
    (h : AffinePoint (FVar Fq)) (input : UnChecked (XhatBranchesInput (FVar Fq) (BoolVar Fq))) :
    CircuitM Fq Cq PUnit := do
  let bits ← Pickles.oneHotVector 2 input.val.branchIndex
  let _ ← Pickles.publicInputCommitMasked (C := XhatWrapCurve) shared h bits
    input.val.statement.unfinalized.packed #v[oneChunk pts0, oneChunk pts1]
  pure PUnit.unit

/-! ## The wrap circuits (`wrap_main_*`)

`Pickles.wrapMain` at each dump's branches, slots and chunks, its config from the dump's
`wrapMain` constants (`wrapMainOf`): the branches' slot counts, step domains and step keys, the
Lagrange bases per public-input scalar and branch, the blinding `h`, the wrap domain pins (none
for a side-loaded slot), the slot widths and the padding challenges. Each target compiles
`wrapMainDumpCircuit`'s output alone, the capstones' system (`Snarky.compileWith_constraints`). -/

/-- An `x_hat` circuit's constants (`xhat`): its Lagrange bases at `nc` chunks, as points of
`C` — `IpaVesta` on the wrap side, `IpaPallas` on the step side — and its blinding `h`. The
corrections are derived in-circuit. -/
def xhatOf (C : Bulletproof.Ipa.KimchiCurve) (nc : ℕ) (j : Json) :
    Except String (Array (Vector C.Point nc) × C.Point) := do
  let c ← constantsOf "xhat" j
  return (← FixtureKit.parseArrOf (chunksOf C nc) (← c.getObjVal? "lagrange"),
    ← Bulletproof.Fixture.parsePt C (← c.getObjVal? "h"))

/-- `xhatOf` at one chunk, each base as its one point. -/
def xhat1Of (C : Bulletproof.Ipa.KimchiCurve) (j : Json) :
    Except String (Array C.Point × C.Point) :=
  return (← xhatOf C 1 j).map (·.map fun (v : Vector C.Point 1) => v[0]) id

/-- A wrap-side `x_hat` circuit's constants at `nc` chunks, its bases the packed step
statement's table (`PicklesFixture.firstBases?`). -/
def xhatBasesOf (nc : ℕ) (j : Json) :
    Except String
      (Vector (Vector XhatWrapCurve.Point nc)
        (CircuitType.size Fp (Pickles.StepStatement (Pickles.UnfVal 15) Fp 1)) ×
        XhatWrapCurve.Point) := do
  let (pts, h) ← xhatOf XhatWrapCurve nc j
  return (← firstBases? pts, h)

/-- The branches `x_hat` circuit's constants (`xhatBranches`): its two branches' one-chunk
Lagrange bases on the wrap side, and the blinding `h`. -/
def xhatBranchesOf (j : Json) :
    Except String (Vector (Array XhatWrapCurve.Point) 2 × XhatWrapCurve.Point) := do
  let c ← constantsOf "xhatBranches" j
  let branch (b : Json) : Except String (Array XhatWrapCurve.Point) := do
    return (← FixtureKit.parseArrOf (chunksOf XhatWrapCurve 1) b).map
      fun (v : Vector XhatWrapCurve.Point 1) => v[0]
  let ls ← FixtureKit.parseArrOf branch (← c.getObjVal? "lagrange")
  let some ls := (if h : ls.size = 2 then some (⟨ls, h⟩ : Vector _ 2) else none)
    | throw s!"{ls.size} branches, expected 2"
  return (ls, ← Bulletproof.Fixture.parsePt XhatWrapCurve (← c.getObjVal? "h"))

/-- A target whose circuit is built from its own dump's constants, read by `read`. -/
def withConstants {α : Type} (read : Json → Except String α) (mk : α → Comparison) : Comparison :=
  fun j => do mk (← read j) j

/-! ### The step side (`xhat_step_circuit`)

The step-side `x_hat` MSM (`Pickles.publicInputCommitKnown`, OCaml `multiscale_known`) against
the PS `XhatStep` harness's `xhat_step_circuit`: 30 Pallas Lagrange bases (Fp coordinates) and
the blinding `h` from the dump's `xhat` constants. In `PureCorrections` mode the corrections are
constants: the known-domain table `Pickles.XhatTable.ofKeyKnown` carries the first leaf's
correction (`corrHead`, the seed PS uses only when the first result is a `condAdd`) and their
sum (`corrSum`), both computed natively. -/

/-- `xhat_step_circuit`'s input: the packed wrap statement without its feature cells
(`Pickles.StatementPacked`'s first six fields), at 16 rounds. -/
structure XhatStepInput (f : Type) where
  /-- The shifted scalars `cip`, `b`, `ζ^(2^k)`, `ζⁿ`, the permutation scalar. -/
  fpFields : Vector f 5
  /-- `β`, `γ`. -/
  challenges : Vector f 2
  /-- `α`, `ζ`, `ξ`. -/
  scalarChallenges : Vector f 3
  /-- The fq-sponge digest before evaluations, the wrap-side and the step-side message
  digests. -/
  digests : Vector f 3
  /-- The round challenges. -/
  bulletproofChallenges : Vector f 16
  /-- The branch data, packed as `4·domainLog2 + mask₀ + 2·mask₁`. -/
  branchData : f

/-- The input is its fields, in order. -/
def XhatStepInput.equivProd (f : Type) :
    XhatStepInput f ≃ Vector f 5 × Vector f 2 × Vector f 3 × Vector f 3 × Vector f 16 × f :=
  ⟨fun i => (i.fpFields, i.challenges, i.scalarChallenges, i.digests, i.bulletproofChallenges,
      i.branchData),
   fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩, fun _ => rfl,
   fun _ => rfl⟩

instance {F : Type} : CircuitType F (XhatStepInput F) (XhatStepInput (FVar F)) :=
  CircuitType.ofEquiv (XhatStepInput.equivProd F) (XhatStepInput.equivProd (FVar F))

/-- The input as packed scalars, in order: the shifted scalars full, the challenges 128-bit, the
digests full, the round challenges 128-bit, the branch data 10-bit. -/
def XhatStepInput.packed (i : XhatStepInput (FVar Fp)) : Vector (Pickles.PackedScalar Fp) 30 :=
  open Pickles.PackedScalar in
  ⟨(i.fpFields.toList.map full ++ (i.challenges.toList ++ i.scalarChallenges.toList).map b128
      ++ i.digests.toList.map full ++ i.bulletproofChallenges.toList.map b128
      ++ [b10 i.branchData]).toArray, by simp⟩

/-- The known-domain `x_hat` of the input, with the constant correction seed and sum: the one
chunk the group half consumes. -/
def XhatStepInput.commit (pts : Array XhatStepCurve.Point) (h : AffinePoint (FVar Fp))
    (i : XhatStepInput (FVar Fp)) : CircuitM Fp C (Vector (AffinePoint (FVar Fp)) 1) := do
  let ks := i.packed
  let tab := Pickles.XhatTable.ofKeyKnown (C := XhatStepCurve) ks (oneChunk pts)
  let r ← Pickles.publicInputCommitKnown (0 : Fin 1) h tab.corrHead[0] tab.corrSum[0]
    (Pickles.packLeavesOf ks tab)
  pure #v[r]

/-- `xhat_step_circuit`. -/
def xhatStepCircuit (pts : Array XhatStepCurve.Point) (h : AffinePoint (FVar Fp))
    (input : UnChecked (XhatStepInput (FVar Fp))) : CircuitM Fp C PUnit := do
  let _ ← input.val.commit pts h
  pure PUnit.unit

/-! ## The `ft_comm` circuits

Transcribe `Pickles.CircuitDiffs.PureScript.FtcommStep` and `Ftcomm`: `Pickles.ftComm` at
either side's `IpaScalarOps`. `σ₆` is the one-chunk constant group generator (OCaml
`Inner_curve.Params.one`, the IVP dump's `dummy_comm`). -/

/-- `ftcomm_{step,wrap}_circuit`'s input: the shifted scalars `s` are split Type2 values on the
step side, Type1 on the wrap side. -/
structure FtcommInput (f s : Type) where
  /-- The 7 quotient chunks. -/
  tComm : Vector (AffinePoint f) 7
  /-- The permutation scalar. -/
  perm : s
  /-- `ζ^{2^k}`. -/
  zetaToSrsLength : s
  /-- `ζⁿ`. -/
  zetaToDomainSize : s

/-- The input is its fields, in order. -/
def FtcommInput.equivProd (f s : Type) : FtcommInput f s ≃ Vector (AffinePoint f) 7 × s × s × s :=
  ⟨fun i => (i.tComm, i.perm, i.zetaToSrsLength, i.zetaToDomainSize),
   fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F s vs : Type} [CircuitType F s vs] :
    CircuitType F (FtcommInput F s) (FtcommInput (FVar F) vs) :=
  CircuitType.ofEquiv (FtcommInput.equivProd F s) (FtcommInput.equivProd (FVar F) vs)

/-- The Pallas group generator (proof-systems `pallas.rs` `G_GENERATOR_{X,Y}`), as a constant
point at the step field. -/
def pallasGenerator : AffinePoint (FVar Fp) :=
  ⟨.const 1, .const 12418654782883325593414442427049395787963493412651469444558597405572177144507⟩

/-- The Vesta group generator (proof-systems `vesta.rs` `G_GENERATOR_{X,Y}`), as a constant
point at the wrap field. -/
def vestaGenerator : AffinePoint (FVar Fq) :=
  ⟨.const 1, .const 11426906929455361843568202299992114520848200991084027513389447476559454104162⟩

/-- `ftcomm_step_circuit`. -/
def ftcommStepCircuit
    (input : UnChecked (FtcommInput (FVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))) :
    CircuitM Fp C PUnit := do
  let i := input.val
  let _ ← Pickles.ftComm Pickles.IpaScalarOps.step #v[pallasGenerator] i.tComm i.perm
    i.zetaToSrsLength i.zetaToDomainSize
  pure PUnit.unit

/-- `ftcomm_wrap_circuit`. -/
def ftcommWrapCircuit (input : UnChecked (FtcommInput (FVar Fq) (Type1 (FVar Fq)))) :
    CircuitM Fq Cq PUnit := do
  let i := input.val
  let _ ← Pickles.ftComm Pickles.IpaScalarOps.wrap #v[vestaGenerator] i.tComm i.perm
    i.zetaToSrsLength i.zetaToDomainSize
  pure PUnit.unit

/-! ## The `incrementally_verify_proof` circuit

Transcribes `Pickles.CircuitDiffs.PureScript.IvpStep`: the public input is
`xhat_step_circuit`'s, committed at the known domain. The key's commitments are the dummy
generator and the two `sg_old` the dummy wrap `sg` (PS `Common`). The standalone PS harness
derives the index digest by absorbing the key's commitments into a fresh sponge
(`IncrementallyVerifyProof.purs`, the `Nothing` branch), so this harness replays that absorb
before handing the sponge to the gadget. The 30 Lagrange bases and `h` are the `pallasCrs15`
SRS's at domain 15 (the dump's `xhat` constants), not `xhat_step_circuit`'s. -/

/-- `dummyWrapSgPt` as a constant point at the step field. -/
def dummyWrapSg : AffinePoint (FVar Fp) := Pickles.constPt dummyWrapSgPt

/-- The dummy key's commitments (PS `Common`): `σ₀…σ₆`, the 15 coefficient commitments and
the six index commitments, each one chunk at the generator. -/
def dummyKeyComms : Pickles.VkComms 1 (AffinePoint (FVar Fp)) :=
  VkComms.replicate #v[pallasGenerator]

/-- The sponge after the dummy key's index digest. -/
def dummyIndexSponge : CircuitM Fp C (SpongeVar Fp) :=
  indexSponge Bulletproof.IpaVesta.curve.frSponge.params dummyKeyComms

/-- An `ivp_{step,wrap}_circuit` input: the public input `pi`, the verified proof's deferred
values at `k` rounds and shifted values `s`, its messages and opening at one chunk, and the
claimed sponge digest before evaluations. The dumps lay the deferred values out as the plonk
claims, `cip`, `b`, `ξ`, the round challenges, and the opening as `δ`, `sg`, the `(L, R)`
pairs, `z₁`, `z₂`. -/
structure IvpHarnessInput (pi : Type) (k : ℕ) (f s : Type) where
  /-- The public input. -/
  publicInput : pi
  /-- The verified proof's deferred values. -/
  deferredValues : Pickles.DeferredValues k f s
  /-- The 15 witness commitments. -/
  wComm : Vector (Vector (AffinePoint f) 1) 15
  /-- The permutation commitment. -/
  zComm : Vector (AffinePoint f) 1
  /-- The 7 quotient chunks. -/
  tComm : Vector (AffinePoint f) 7
  /-- The opening. -/
  opening : Pickles.BulletproofOpening k f s
  /-- The claimed sponge digest before evaluations. -/
  claimedDigest : f

/-- The input is its fields in the dumps' order. -/
def IvpHarnessInput.equivProd (pi : Type) (k : ℕ) (f s : Type) :
    IvpHarnessInput pi k f s ≃
      pi × (Pickles.PlonkInCircuit f s × s × s × SizedF 128 f × Vector (SizedF 128 f) k) ×
        Vector (Vector (AffinePoint f) 1) 15 × Vector (AffinePoint f) 1 × Vector (AffinePoint f) 7 ×
        (AffinePoint f × AffinePoint f × Vector (AffinePoint f × AffinePoint f) k × s × s) × f :=
  ⟨fun i =>
    let dv := i.deferredValues
    let o := i.opening
    (i.publicInput, (dv.plonk, dv.combinedInnerProduct, dv.b, dv.xi, dv.bulletproofChallenges),
      i.wComm, i.zComm, i.tComm, (o.delta, o.sg, o.lr, o.z1, o.z2), i.claimedDigest),
   fun p =>
    let d := p.2.1
    let o := p.2.2.2.2.2.1
    ⟨p.1, ⟨d.1, d.2.1, d.2.2.2.1, d.2.2.2.2, d.2.2.1⟩, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1,
      ⟨o.2.2.1, o.2.2.2.1, o.2.2.2.2, o.1, o.2.1⟩, p.2.2.2.2.2.2⟩,
   fun _ => rfl, fun _ => rfl⟩

instance {F pi vpi s vs : Type} {k : ℕ} [CircuitType F pi vpi] [CircuitType F s vs] :
    CircuitType F (IvpHarnessInput pi k F s) (IvpHarnessInput vpi k (FVar F) vs) :=
  CircuitType.ofEquiv (IvpHarnessInput.equivProd pi k F s)
    (IvpHarnessInput.equivProd vpi k (FVar F) vs)

/-- The verified proof the group half takes. -/
def IvpHarnessInput.proof {pi f s : Type} {k : ℕ} (i : IvpHarnessInput pi k f s) :
    Pickles.IvpProof k 1 f s :=
  ⟨i.wComm, i.zComm, i.tComm, i.opening⟩

/-- `ivp_step_circuit`'s input: `xhat_step_circuit`'s, the wrap proof at 15 rounds, split
Type2-shifted. -/
abbrev IvpStepInput (f b : Type) : Type :=
  IvpHarnessInput (XhatStepInput f) 15 f (Type2 (SplitField f b))

/-- `ivp_step_circuit`: the index-digest sponge, `Pickles.incrementallyVerifyProof` on the
step side with `x_hat` the known-domain commitment of the public input, then the harness's
assertions — the digest against the claim and each returned round challenge against its
claim. -/
def ivpStepCircuit (pts : Array XhatStepCurve.Point) (h : AffinePoint (FVar Fp))
    (input : UnChecked (IvpStepInput (FVar Fp) (BoolVar Fp))) : CircuitM Fp C PUnit := do
  let i := input.val
  let dv := i.deferredValues
  let sv ← dummyIndexSponge
  let o ← Pickles.incrementallyVerifyProof Pickles.IpaScalarOps.step Pickles.IpaEndo.pallas
    Bulletproof.IpaVesta.curve.frSponge.params (.const Bulletproof.IpaVesta.curve.lam)
    Pickles.groupMapParamsPallas (fun _ => none) false h sv (i.publicInput.commit pts h)
    (Pickles.ivpInputOf dv #v[(none, dummyWrapSg), (none, dummyWrapSg)] dummyKeyComms i.proof)
  assertEqual o.spongeDigest i.claimedDigest
  for c in (dv.bulletproofChallenges.zip o.bulletproofChallenges).toList do
    assertEqual c.1.val c.2.val
  pure PUnit.unit

/-! ## The `verify` circuit (`Step_verifier.verify`)

Transcribes `Pickles.CircuitDiffs.PureScript.StepVerify`: the wrap proof verified against its
statement and the unfinalized proof, the per-proof witness's evaluations dead inputs. The key
and `sg_old` are the dummies of `ivp_step_circuit`, the index digest the same replayed absorb,
the Lagrange bases the same `pallasCrs15` export. -/

/-- The step-side verify harnesses' per-proof witness (OCaml `Per_proof_witness`): the
application state, the wrap proof at 15 rounds and one chunk, its statement's deferred values
at 16 rounds, the sponge digest, the evaluations, and the `w` previous challenge vectors and
`sg`s. The dumps lay the deferred values out in OCaml's hlist order: `α`, `β`, `γ`, `ζ`,
`ζ^{2^k}`, `ζⁿ`, `perm`, `cip`, `b`, `ξ`, the round challenges, the mask, the domain's `log2`. -/
structure PerProofWitnessInput (a : Type) (w : ℕ) (f b : Type) where
  /-- The application state. -/
  appState : a
  /-- The wrap proof. -/
  wrapProof : Pickles.IvpProof 15 1 f (Type2 (SplitField f b))
  /-- The wrap statement's deferred values. -/
  deferredValues : Pickles.WrapDeferredValues 16 f b (Type1 f)
  /-- The sponge digest before evaluations. -/
  spongeDigest : f
  /-- The evaluations. -/
  evals : Pickles.AllocEvals 1 f
  /-- The previous challenge vectors. -/
  prevChallenges : Vector (Vector f 16) w
  /-- The previous challenge polynomial commitments. -/
  prevSgs : Vector (AffinePoint f) w

/-- The witness is its fields in the dumps' order. -/
def PerProofWitnessInput.equivProd (a : Type) (w : ℕ) (f b : Type) :
    PerProofWitnessInput a w f b ≃
      a × Pickles.IvpProof 15 1 f (Type2 (SplitField f b)) × WrapDeferredHlist f b × f ×
        Pickles.AllocEvals 1 f × Vector (Vector f 16) w × Vector (AffinePoint f) w :=
  ⟨fun i => (i.appState, i.wrapProof, .of i.deferredValues, i.spongeDigest, i.evals,
      i.prevChallenges, i.prevSgs),
   fun p => ⟨p.1, p.2.1, WrapDeferredHlist.to p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1,
     p.2.2.2.2.2.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F a va : Type} {w : ℕ} [Zero F] [One F] [DecidableEq F] [NeZero (1 : F)]
    [CircuitType F a va] :
    CircuitType F (PerProofWitnessInput a w F Bool)
      (PerProofWitnessInput va w (FVar F) (BoolVar F)) :=
  CircuitType.ofEquiv (PerProofWitnessInput.equivProd a w F Bool)
    (PerProofWitnessInput.equivProd va w (FVar F) (BoolVar F))

/-- `step_verify_circuit`'s input: the per-proof witness with no application state and no
previous proofs, the unfinalized proof it is checked against (its finalize flag unread),
`is_base_case`, and the two message digests. -/
structure StepVerifyInput (f b : Type) where
  /-- The per-proof witness. -/
  witness : PerProofWitnessInput Unit 0 f b
  /-- The unfinalized proof. -/
  unfinalized : Pickles.AllocUnfinalized 15 f b (Type2 (SplitField f b))
  /-- Whether this is the base case. -/
  isBaseCase : b
  /-- The wrap-side message digest. -/
  messagesForNextWrapProof : f
  /-- The step-side message digest. -/
  messagesForNextStepProof : f

/-- The input is its fields, in order. -/
def StepVerifyInput.equivProd (f b : Type) :
    StepVerifyInput f b ≃
      PerProofWitnessInput Unit 0 f b × Pickles.AllocUnfinalized 15 f b (Type2 (SplitField f b)) ×
        b × f × f :=
  ⟨fun i => (i.witness, i.unfinalized, i.isBaseCase, i.messagesForNextWrapProof,
      i.messagesForNextStepProof),
   fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F : Type} [Zero F] [One F] [DecidableEq F] [NeZero (1 : F)] :
    CircuitType F (StepVerifyInput F Bool) (StepVerifyInput (FVar F) (BoolVar F)) :=
  CircuitType.ofEquiv (StepVerifyInput.equivProd F Bool)
    (StepVerifyInput.equivProd (FVar F) (BoolVar F))

/-- `step_verify_circuit`: the index-digest sponge, then `Pickles.verifyProofWith` — the gadget
`verifyProofAt` is at an environment's data — at the dump's points, the statement from the
witness and the two digests, the unfinalized proof always finalized. -/
def stepVerifyCircuit (pts : Array XhatStepCurve.Point) (h : XhatStepCurve.Point)
    (input : UnChecked (StepVerifyInput (FVar Fp) (BoolVar Fp))) : CircuitM Fp C PUnit := do
  let i := input.val
  let w := i.witness
  let statement : Pickles.WrapStatement Pickles.StepIPARounds (FVar Fp) (BoolVar Fp)
      (Type1 (FVar Fp)) :=
    { proofState := { deferredValues := w.deferredValues
                      spongeDigestBeforeEvaluations := w.spongeDigest
                      messagesForNextWrapProof := i.messagesForNextWrapProof }
      messagesForNextStepProof := i.messagesForNextStepProof }
  let unfinalized := { i.unfinalized.toUnfinalized with shouldFinalize := true_ }
  let sv ← dummyIndexSponge
  let _ ← Pickles.verifyProofWith h (oneChunk pts) sv i.isBaseCase statement unfinalized
    (Pickles.ivpInputOf unfinalized.deferredValues #v[(none, dummyWrapSg), (none, dummyWrapSg)]
      dummyKeyComms w.wrapProof)
  pure PUnit.unit

/-! ## One slot of the step circuit

Transcribes `Pickles.CircuitDiffs.PureScript.FullStepVerifyOne`: `Pickles.verifyOneBy` over one
previous proof of width 1, the check against `verifyProofWith` at `pallasCrs15`'s Lagrange bases
at domain 14 (the dump's `xhat` constants), the finalize at the dump's one known domain of
`log2 = 16`, the key's commitments the dummy generator and the padded `sg_old` the dummy wrap
`sg`. -/

/-- `full_step_verify_one_circuit`'s input: the per-proof witness with a one-cell application
state and one previous proof, the unfinalized proof, the wrap-side message, and `mustVerify`. -/
structure FullStepVerifyOneInput (f b : Type) where
  /-- The per-proof witness. -/
  witness : PerProofWitnessInput f 1 f b
  /-- The unfinalized proof. -/
  unfinalized : Pickles.AllocUnfinalized 15 f b (Type2 (SplitField f b))
  /-- The wrap-side message digest. -/
  messagesForNextWrapProof : f
  /-- Whether the proof must verify. -/
  mustVerify : b

/-- The input is its fields, in order. -/
def FullStepVerifyOneInput.equivProd (f b : Type) :
    FullStepVerifyOneInput f b ≃
      PerProofWitnessInput f 1 f b × Pickles.AllocUnfinalized 15 f b (Type2 (SplitField f b)) ×
        f × b :=
  ⟨fun i => (i.witness, i.unfinalized, i.messagesForNextWrapProof, i.mustVerify),
   fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F : Type} [Zero F] [One F] [DecidableEq F] [NeZero (1 : F)] :
    CircuitType F (FullStepVerifyOneInput F Bool) (FullStepVerifyOneInput (FVar F) (BoolVar F)) :=
  CircuitType.ofEquiv (FullStepVerifyOneInput.equivProd F Bool)
    (FullStepVerifyOneInput.equivProd (FVar F) (BoolVar F))

open Pickles in
/-- `full_step_verify_one_circuit`: the proof mask trimmed to the slot's last bit, `sg_old` the
dummy wrap `sg` then the proof's. -/
def fullStepVerifyOneCircuit (pts : Array XhatStepCurve.Point) (h : XhatStepCurve.Point)
    (input : UnChecked (FullStepVerifyOneInput (FVar Fp) (BoolVar Fp))) : CircuitM Fp C PUnit := do
  let i := input.val
  let w := i.witness
  let bd := w.deferredValues.branchData
  let inp : VerifyOneInput 1 16 15 1 1 1 :=
    { appState := #v[w.appState]
      deferred := w.deferredValues.toDeferredValues
      spongeDigest := w.spongeDigest
      branchData := bd
      messagesForNextWrapProof := i.messagesForNextWrapProof
      evals := w.evals.toChunked
      proofMask := #v[bd.proofsVerifiedMask[1]]
      prevChallenges := w.prevChallenges
      prevSgs := w.prevSgs
      sgOld := #v[dummyWrapSg] ++ w.prevSgs
      unfinalized := i.unfinalized.toUnfinalized
      proof := w.wrapProof
      mustVerify := i.mustVerify }
  let _ ← verifyOneBy (fun sv b st u cells => verifyProofWith h (oneChunk pts) sv b st u cells)
    (PicklesFixture.fopStepParams 1)
    [⟨16, Kimchi.Verifier.domainGenerator Bulletproof.IpaVesta.curve 16⟩] dummyKeyComms inp
  pure PUnit.unit

/-! ## The step circuits (`step_main_*`)

`Pickles.stepMain` at each dump's slots, its configuration from the dump's `stepMain` constants
(`stepMainOf`): the blinding `h`, and per slot its kind, width, candidate step domains, Lagrange
bases and wrap key. The tag's width is transcribed beside the rule. Only
the rule is transcribed per dump. `simple_chain_n2` has two self slots of width 2;
`two_phase_chain_make_zero` no slot in a tag of width 1, so one dummy unfinalized entry and one
padding message; `two_phase_chain_increment` one self slot of width 1 over the tag's two step
domains; `tree_proof_return` an external slot on No_recursion_return (width 0) and a self slot of
width 2; `import_two_phase_chain` an external slot on two_phase_chain (width 1, its two step
domains) and a self slot of width 2, run a second time with the external slot's candidates
reversed and repeated against the same dump. -/

/-! ## The wrap side's `incrementally_verify_proof`

Transcribes `Pickles.CircuitDiffs.PureScript.IvpWrap`: the wrap circuit's group half over a
step proof, at the conditional sponge with no `sg_old`, the key's commitments the dummy Vesta
generator, and `x_hat` the in-circuit-correction commitment of the packed step statement
(`WrapStepStatement`, one slot at the wrap SRS's 15 rounds). The Lagrange bases are the dump's
`xhat` constants, which the PS harness builds from the same `vestaCrs16` data it gives
`xhat_wrap_circuit`. -/

/-- The dummy key's commitments on the wrap side (PS `dummyVestaPt`, the Vesta generator):
`σ₀…σ₆`, the 15 coefficient commitments and the six index commitments, one chunk each. -/
def dummyWrapKeyComms : Pickles.VkComms 1 (AffinePoint (FVar Fq)) :=
  VkComms.replicate #v[vestaGenerator]

/-- `ivp_wrap_circuit`'s input: the step statement, the step proof at 16 rounds,
Type1-shifted. -/
abbrev IvpWrapInput (f b : Type) : Type :=
  IvpHarnessInput (WrapStepStatement f b) 16 f (Type1 f)

/-- `ivp_wrap_circuit`: the dummy key's index sponge, `Pickles.incrementallyVerifyProof` on the
conditional sponge with `x_hat` the packed step statement's commitment, then the harness's two
assertions — the digest against the claim and each claimed round challenge against the
returned one. -/
def ivpWrapCircuit (pts : Array XhatWrapCurve.Point) (h : AffinePoint (FVar Fq))
    (input : UnChecked (IvpWrapInput (FVar Fq) (BoolVar Fq))) : CircuitM Fq Cq PUnit := do
  let i := input.val
  let dv := i.deferredValues
  let st := i.publicInput.unfinalized
  let sv ← indexSponge Bulletproof.IpaVesta.curve.sponge.params dummyWrapKeyComms
  let computeXHat : CircuitM Fq Cq (Vector (AffinePoint (FVar Fq)) 1) :=
    Pickles.publicInputCommitFull h
      (Pickles.packLeavesOf st.packed (Pickles.XhatTable.ofKey st.packed (oneChunk pts)))
  let o ← Pickles.incrementallyVerifyProof Pickles.IpaScalarOps.wrap Pickles.IpaEndo.vesta
    Bulletproof.IpaVesta.curve.sponge.params (.const Bulletproof.IpaPallas.curve.lam)
    Pickles.groupMapParamsVesta vestaBase.sqrt? true h sv computeXHat
    (Pickles.ivpInputOf dv #v[] dummyWrapKeyComms i.proof)
  assertEqual o.spongeDigest i.claimedDigest
  for c in (dv.bulletproofChallenges.zip o.bulletproofChallenges).toList do
    assertEqual c.1.val c.2.val
  pure PUnit.unit

/-! ## The wrap circuit's verify block

Transcribes `Pickles.CircuitDiffs.PureScript.WrapVerify`: `Pickles.wrapVerifyWith` — the gadget
`wrapVerifyAt` is at an environment's data — at the dump's points, over `ivp_wrap_circuit`'s
input, now with one real accumulator, its `sg_old` under a constant keep bit. -/

/-- The message-hash sponge `wrap_verify_circuit` starts from: the state after absorbing the
one dummy challenge vector that pads its single real slot to `MaxProofsVerified` (PS
`dummyPaddingSpongeStates` at `n = 1`), so the padding costs no gates. -/
def wrapMsgSponge : SpongeVar Fq :=
  Pickles.wrapPaddingSponge Bulletproof.IpaVesta.curve.sponge.params dummyWrapChallenges 1

/-- `wrap_verify_circuit`'s input: `ivp_wrap_circuit`'s, the claimed
`messages_for_next_wrap_proof` digest, the new round challenges, one unused cell (the OCaml dump
computes the offset at 16 rounds where the wrap side has 15), and the `sg_old` point. -/
structure WrapVerifyInput (f b : Type) where
  /-- `ivp_wrap_circuit`'s input. -/
  ivp : IvpWrapInput f b
  /-- The claimed `messages_for_next_wrap_proof` digest. -/
  messagesForNextWrapProofDigest : f
  /-- The new round challenges. -/
  newBpChallenges : Vector (Vector f 15) 1
  /-- The unused cell. -/
  unused : f
  /-- The `sg_old` point. -/
  sgOld : Vector (AffinePoint f) 1

/-- The input is its fields, in order. -/
def WrapVerifyInput.equivProd (f b : Type) :
    WrapVerifyInput f b ≃
      IvpWrapInput f b × f × Vector (Vector f 15) 1 × f × Vector (AffinePoint f) 1 :=
  ⟨fun i => (i.ivp, i.messagesForNextWrapProofDigest, i.newBpChallenges, i.unused, i.sgOld),
   fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F : Type} [Zero F] [One F] [DecidableEq F] [NeZero (1 : F)] :
    CircuitType F (WrapVerifyInput F Bool) (WrapVerifyInput (FVar F) (BoolVar F)) :=
  CircuitType.ofEquiv (WrapVerifyInput.equivProd F Bool)
    (WrapVerifyInput.equivProd (FVar F) (BoolVar F))

/-- `wrap_verify_circuit`. -/
def wrapVerifyCircuit (pts : Array XhatWrapCurve.Point) (h : XhatWrapCurve.Point)
    (input : UnChecked (WrapVerifyInput (FVar Fq) (BoolVar Fq))) : CircuitM Fq Cq PUnit := do
  let i := input.val
  let dv := i.ivp.deferredValues
  let sv ← indexSponge Bulletproof.IpaVesta.curve.sponge.params dummyWrapKeyComms
  Pickles.wrapVerifyWith h (oneChunk pts) i.ivp.publicInput.unfinalized sv wrapMsgSponge
    i.newBpChallenges i.messagesForNextWrapProofDigest
    { deferredValues := dv, shouldFinalize := .unchecked (.const 1)
      spongeDigestBeforeEvaluations := i.ivp.claimedDigest }
    (Pickles.ivpInputOf dv (i.sgOld.map (some (BoolVar.unchecked (.const 1)), ·)) dummyWrapKeyComms
      i.ivp.proof)

/-! ## The `messages_for_next_wrap_proof` hash

Transcribes `Pickles.CircuitDiffs.PureScript.HashMessagesWrap`: the digest the wrap circuit
commits its accumulator advice to (`Pickles.hashMessagesForNextWrapProof`, OCaml
`wrap_hack.ml:119-142`), from the fresh sponge, asserted against the claimed digest. -/

/-- `hash_messages_for_next_wrap_proof_circuit`'s input, at `MaxProofsVerified = 2`: the
challenges first, in the hash's absorb order. -/
structure HashMessagesWrapInput (f : Type) where
  /-- The two expanded challenge vectors of `WrapIPARounds`. -/
  oldBulletproofChallenges : Vector (Vector f 15) 2
  /-- The accumulator `sg`. -/
  challengePolynomialCommitment : AffinePoint f
  /-- The claimed digest. -/
  claimedDigest : f

/-- The input is its fields, in order. -/
def HashMessagesWrapInput.equivProd (f : Type) :
    HashMessagesWrapInput f ≃ Vector (Vector f 15) 2 × AffinePoint f × f :=
  ⟨fun i => (i.oldBulletproofChallenges, i.challengePolynomialCommitment, i.claimedDigest),
   fun p => ⟨p.1, p.2.1, p.2.2⟩, fun _ => rfl, fun _ => rfl⟩

instance {F : Type} : CircuitType F (HashMessagesWrapInput F) (HashMessagesWrapInput (FVar F)) :=
  CircuitType.ofEquiv (HashMessagesWrapInput.equivProd F)
    (HashMessagesWrapInput.equivProd (FVar F))

/-- `hash_messages_for_next_wrap_proof_circuit`. -/
def hashMessagesWrapCircuit (input : UnChecked (HashMessagesWrapInput (FVar Fq))) :
    CircuitM Fq Cq PUnit := do
  let i := input.val
  let digest ← Pickles.hashMessagesForNextWrapProof Bulletproof.IpaVesta.curve.sponge.params
    SpongeVar.init ⟨i.challengePolynomialCommitment, i.oldBulletproofChallenges⟩
  assertEqual digest i.claimedDigest

/-! ## The step proof's accumulator digest

Transcribes `Pickles.CircuitDiffs.PureScript.HashMessagesStep`: the digest the step circuit
commits its predecessors' accumulator advice to, on the plain sponge
(`Pickles.hashMessagesForNextStepProof`, OCaml `step_verifier.ml:1167-1188`), with no
application state, asserted against the claimed digest. -/

/-- One previous proof's messages: its `sg` and its 15 expanded challenges. -/
structure PrevProofMessages (f : Type) where
  /-- The proof's accumulator `sg`. -/
  challengePolynomialCommitment : AffinePoint f
  /-- Its expanded challenges. -/
  oldBulletproofChallenges : Vector f 15

/-- The messages are their fields, in order. -/
def PrevProofMessages.equivProd (f : Type) : PrevProofMessages f ≃ AffinePoint f × Vector f 15 :=
  ⟨fun m => (m.challengePolynomialCommitment, m.oldBulletproofChallenges), fun p => ⟨p.1, p.2⟩,
   fun _ => rfl, fun _ => rfl⟩

instance {F : Type} : CircuitType F (PrevProofMessages F) (PrevProofMessages (FVar F)) :=
  CircuitType.ofEquiv (PrevProofMessages.equivProd F) (PrevProofMessages.equivProd (FVar F))

/-- `hash_messages_for_next_step_proof_circuit`'s input: the wrap key's one-chunk commitments,
the two previous proofs' messages, the claimed digest. -/
structure HashMessagesStepInput (f : Type) where
  /-- The wrap key's commitments. -/
  vk : Pickles.VkComms 1 (AffinePoint f)
  /-- The previous proofs' messages. -/
  proofs : Vector (PrevProofMessages f) 2
  /-- The claimed digest. -/
  claimedDigest : f

/-- The input is its fields, in order. -/
def HashMessagesStepInput.equivProd (f : Type) :
    HashMessagesStepInput f ≃
      Pickles.VkComms 1 (AffinePoint f) × Vector (PrevProofMessages f) 2 × f :=
  ⟨fun i => (i.vk, i.proofs, i.claimedDigest), fun p => ⟨p.1, p.2.1, p.2.2⟩, fun _ => rfl,
   fun _ => rfl⟩

instance {F : Type} : CircuitType F (HashMessagesStepInput F) (HashMessagesStepInput (FVar F)) :=
  CircuitType.ofEquiv (HashMessagesStepInput.equivProd F)
    (HashMessagesStepInput.equivProd (FVar F))

/-- `hash_messages_for_next_step_proof_circuit`. -/
def hashMessagesStepCircuit (input : UnChecked (HashMessagesStepInput (FVar Fp))) :
    CircuitM Fp C PUnit := do
  let i := input.val
  let digest ← Pickles.hashMessagesForNextStepProof Bulletproof.IpaPallas.curve.sponge.params
    ⟨#v[], i.vk, i.proofs.map (·.challengePolynomialCommitment),
      i.proofs.map (·.oldBulletproofChallenges)⟩
  assertEqual digest i.claimedDigest

/-- The corpus under comparison: the step column, then the wrap column, at the two SRS
blinding bases. -/
def targets (hStep : AffinePoint (FVar Fp)) (hWrap : AffinePoint (FVar Fq)) :
    List (String × Comparison) :=
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
      stepTarget (a := SpongeStateVal Fp) (b := SpongeStateVal Fp) poseidonCircuit),
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
    ("pow2_pow_step_circuit", stepTarget (a := Fp) (b := PUnit) pow2PowCircuit),
    ("b_correct_step_circuit",
      stepTarget (a := UnChecked (BCorrectInput Fp (Type1 Fp))) (b := PUnit)
        bCorrectCircuit),
    ("bullet_reduce_one_step_circuit",
      stepTarget (a := UnChecked (BulletReduceOneInput Fp)) (b := PUnit)
        bulletReduceOneCircuit),
    ("linearization_step_circuit",
      stepTarget (a := UnChecked (LinearizationInput Fp)) (b := Fp)
        (linearizationCircuit Kimchi.Fixture.PS.fpSide 16 Pickles.Linearization.fpTokens)),
    ("bullet_reduce_step_circuit",
      stepTarget (a := UnChecked (BulletReduceInput Fp)) (b := PUnit) bulletReduceCircuit),
    ("ft_eval0_step_circuit",
      stepTarget (a := UnChecked (FtEval0Input Fp)) (b := Fp)
        (ftEval0CsCircuit Kimchi.Fixture.PS.fpSide 16 Pickles.Linearization.fpTokens
          (fun i => Bulletproof.IpaVesta.curve.shifts[i]))),
    ("cip_step_circuit",
      stepTarget (a := UnChecked (CipStepInput Fp Bool)) (b := PUnit) cipStepCircuit),
    ("plonk_checks_passed_step_circuit",
      stepTarget (a := UnChecked (PlonkChecksPassedInput Fp (Type1 Fp))) (b := PUnit)
        plonkChecksPassedStepCircuit),
    ("expand_plonk_step_circuit",
      stepTarget (a := UnChecked (ExpandPlonkInput Fp)) (b := PUnit) expandPlonkStepCircuit),
    ("fq_sponge_transcript_step_circuit",
      stepTarget (a := UnChecked (FqSpongeStepInput Fp)) (b := PUnit)
        fqSpongeTranscriptStepCircuit),
    ("check_bulletproof_step_circuit",
      stepTarget
        (a := UnChecked (CheckBulletproofStepInput Fp (Type2 (SplitField Fp Bool))))
        (b := PUnit) (checkBulletproofStepCircuit hStep)),
    ("finalize_other_proof_step_circuit",
      stepTarget (a := UnChecked (FopStepInput 1 Fp Bool)) (b := PUnit) fopStepCircuit),
    ("finalize_other_proof_chunks2_step_circuit",
      stepTarget (a := UnChecked (FopStepInput 2 Fp Bool)) (b := PUnit) fopStepCircuit),
    ("ftcomm_step_circuit",
      stepTarget (a := UnChecked (FtcommInput Fp (Type2 (SplitField Fp Bool)))) (b := PUnit)
        ftcommStepCircuit),
    -- the wrap column
    ("group_map_wrap_circuit", wrapTarget (a := Fq) (b := PUnit) groupMapCircuitFq),
    ("linearization_wrap_circuit",
      wrapTarget (a := UnChecked (LinearizationInput Fq)) (b := Fq)
        (linearizationCircuit Kimchi.Fixture.PS.fqSide 15 Pickles.Linearization.fqTokens)),
    ("cip_wrap_circuit", wrapTarget (a := UnChecked (CipWrapInput Fq)) (b := PUnit) cipWrapCircuit),
    ("b_correct_wrap_circuit",
      wrapTarget (a := UnChecked (BCorrectInput Fq (Type2 Fq))) (b := PUnit) bCorrectWrapCircuit),
    ("plonk_checks_passed_wrap_circuit",
      wrapTarget (a := UnChecked (PlonkChecksPassedInput Fq (Type2 Fq))) (b := PUnit)
        plonkChecksPassedWrapCircuit),
    ("expand_plonk_wrap_circuit",
      wrapTarget (a := UnChecked (ExpandPlonkInput Fq)) (b := PUnit) expandPlonkWrapCircuit),
    ("fq_sponge_transcript_wrap_circuit",
      wrapTarget (a := UnChecked (FqSpongeWrapInput Fq)) (b := PUnit)
        fqSpongeTranscriptWrapCircuit),
    ("check_bulletproof_wrap_circuit",
      wrapTarget (a := UnChecked (CheckBulletproofWrapInput Fq Bool (Type1 Fq)))
        (b := PUnit) (checkBulletproofWrapCircuit hWrap)),
    ("finalize_other_proof_wrap_circuit",
      wrapTarget (a := UnChecked (FopWrapInput 16 Fq (Type2 Fq))) (b := PUnit)
        finalizeOtherProofWrapCircuit),
    ("wrap_finalize_n2_circuit",
      wrapTarget (a := UnChecked (WrapFinalizeInput Fq Bool)) (b := PUnit) wrapFinalizeN2Circuit),
    ("ftcomm_wrap_circuit",
      wrapTarget (a := UnChecked (FtcommInput Fq (Type1 Fq))) (b := PUnit) ftcommWrapCircuit),
    -- the Pseudo selection circuits, on both fields
    ("one_hot_n1_step_circuit", stepTarget (a := Fp) (b := PUnit) (oneHotCircuit 1)),
    ("one_hot_n3_step_circuit", stepTarget (a := Fp) (b := PUnit) (oneHotCircuit 3)),
    ("one_hot_n17_step_circuit", stepTarget (a := Fp) (b := PUnit) (oneHotCircuit 17)),
    ("one_hot_n1_wrap_circuit", wrapTarget (a := Fq) (b := PUnit) (oneHotCircuit 1)),
    ("one_hot_n3_wrap_circuit", wrapTarget (a := Fq) (b := PUnit) (oneHotCircuit 3)),
    ("one_hot_n17_wrap_circuit", wrapTarget (a := Fq) (b := PUnit) (oneHotCircuit 17)),
    ("pseudo_mask_n1_step_circuit",
      stepTarget (a := UnChecked (PseudoMaskInput 1 Fp)) (b := PUnit) (pseudoMaskCircuit 1)),
    ("pseudo_mask_n3_step_circuit",
      stepTarget (a := UnChecked (PseudoMaskInput 3 Fp)) (b := PUnit) (pseudoMaskCircuit 3)),
    ("pseudo_mask_n17_step_circuit", stepTarget (a := Fp) (b := PUnit) pseudoMaskConstCircuit),
    ("pseudo_mask_n1_wrap_circuit",
      wrapTarget (a := UnChecked (PseudoMaskInput 1 Fq)) (b := PUnit) (pseudoMaskCircuit 1)),
    ("pseudo_mask_n3_wrap_circuit",
      wrapTarget (a := UnChecked (PseudoMaskInput 3 Fq)) (b := PUnit) (pseudoMaskCircuit 3)),
    ("pseudo_mask_n17_wrap_circuit", wrapTarget (a := Fq) (b := PUnit) pseudoMaskConstCircuit),
    ("pseudo_choose_n1_step_circuit", stepTarget (a := Fp) (b := PUnit)
      (pseudoChooseCircuit 1 [42])),
    ("pseudo_choose_n3_step_circuit", stepTarget (a := Fp) (b := PUnit)
      (pseudoChooseCircuit 3 [13, 14, 15])),
    ("pseudo_choose_n1_wrap_circuit", wrapTarget (a := Fq) (b := PUnit)
      (pseudoChooseCircuit 1 [42])),
    ("pseudo_choose_n3_wrap_circuit", wrapTarget (a := Fq) (b := PUnit)
      (pseudoChooseCircuit 3 [13, 14, 15])),
    ("utils_ones_vector_n16_step_circuit",
      stepTarget (a := Fp) (b := PUnit) onesVectorN16Circuit),
    ("utils_ones_vector_n16_wrap_circuit",
      wrapTarget (a := Fq) (b := PUnit) onesVectorN16Circuit),
    ("choose_key_n1_wrap_circuit",
      wrapTarget (a := Fq) (b := PUnit) chooseKeyN1WrapCircuit),
    ("pseudo_to_domain_wrap_circuit",
      wrapTarget (a := UnChecked (PseudoToDomainInput Fq)) (b := PUnit)
        pseudoToDomainWrapCircuit),
    ("hash_messages_for_next_step_proof_circuit",
      stepTarget (a := UnChecked (HashMessagesStepInput Fp)) (b := PUnit)
        hashMessagesStepCircuit),
    ("hash_messages_for_next_wrap_proof_circuit",
      wrapTarget (a := UnChecked (HashMessagesWrapInput Fq)) (b := PUnit)
        hashMessagesWrapCircuit) ]

/-- The targets whose circuits are built from their own dumps' `x_hat` constants. -/
def xhatTargets : List (String × Comparison) :=
  [ ("full_step_verify_one_circuit", withConstants (xhat1Of XhatStepCurve) fun (pts, h) =>
      stepTarget (a := UnChecked (FullStepVerifyOneInput Fp Bool)) (b := PUnit)
        (fullStepVerifyOneCircuit pts h)),
    ("xhat_step_circuit", withConstants (xhat1Of XhatStepCurve) fun (pts, h) =>
      stepTarget (a := UnChecked (XhatStepInput Fp)) (b := PUnit)
        (xhatStepCircuit pts (xhatStepCell h))),
    ("ivp_step_circuit", withConstants (xhat1Of XhatStepCurve) fun (pts, h) =>
      stepTarget (a := UnChecked (IvpStepInput Fp Bool)) (b := PUnit)
        (ivpStepCircuit pts (xhatStepCell h))),
    ("step_verify_circuit", withConstants (xhat1Of XhatStepCurve) fun (pts, h) =>
      stepTarget (a := UnChecked (StepVerifyInput Fp Bool)) (b := PUnit) (stepVerifyCircuit pts h)),
    ("xhat_wrap_circuit", withConstants (xhatBasesOf 1) fun (pts, h) =>
      wrapTarget (a := UnChecked (WrapStepStatement Fq Bool)) (b := PUnit)
        (xhatWrapCircuit pts (xhatWrapCell h))),
    ("xhat_wrap_chunks2_circuit", withConstants (xhatBasesOf 2) fun (pts, h) =>
      wrapTarget (a := UnChecked (WrapStepStatement Fq Bool)) (b := PUnit)
        (xhatWrapCircuit pts (xhatWrapCell h))),
    ("ivp_wrap_circuit", withConstants (xhat1Of XhatWrapCurve) fun (pts, h) =>
      wrapTarget (a := UnChecked (IvpWrapInput Fq Bool)) (b := PUnit)
        (ivpWrapCircuit pts (xhatWrapCell h))),
    ("wrap_verify_circuit", withConstants (xhat1Of XhatWrapCurve) fun (pts, h) =>
      wrapTarget (a := UnChecked (WrapVerifyInput Fq Bool)) (b := PUnit) (wrapVerifyCircuit pts h)),
    ("xhat_wrap_branches_same_circuit", withConstants xhatBranchesOf fun (ls, h) =>
      wrapTarget (a := UnChecked (XhatBranchesInput Fq Bool)) (b := PUnit)
        (xhatBranchesCircuit true ls[0] ls[1] (xhatWrapCell h))),
    ("xhat_wrap_branches_diff_circuit", withConstants xhatBranchesOf fun (ls, h) =>
      wrapTarget (a := UnChecked (XhatBranchesInput Fq Bool)) (b := PUnit)
        (xhatBranchesCircuit false ls[0] ls[1] (xhatWrapCell h))) ]

def main : IO Unit := do
  let dir ← resultsDir
  let fdir := (← IO.getEnv "BULLETPROOF_FIXTURES_DIR").getD "bulletproof-pcs/fixtures"
  let hStepPt ← blindingBase Bulletproof.IpaPallas.curve s!"{fdir}/ipa_batch_pallas.json"
  let hWrapPt ← blindingBase Bulletproof.IpaVesta.curve s!"{fdir}/ipa_batch_vesta.json"
  let hStep := Pickles.constPt hStepPt
  let hWrap := Pickles.constPt hWrapPt
  -- `KIMCHI_CS_FILTER` narrows the corpus to targets whose name contains it — for local
  -- validation of one circuit against a partial results dir. Unset (CI) runs the whole corpus.
  let filter := (← IO.getEnv "KIMCHI_CS_FILTER").getD ""
  let wrapMains ← wrapMainDumps.filterMapM fun (name, bp, mpv, nc) => do
    let k ← dumpConstants filter (dir / s!"{name}.json") (wrapMainOf nc)
    k.mapM fun k => do
      let (main, tables) ←
        IO.ofExcept ((wrapMainCircuitOf bp mpv nc k).mapError (s!"{name}: " ++ ·))
      IO.ofExcept ((wrapMainHyps k tables hWrapPt).mapError (s!"{name}: " ++ ·))
      pure (name, wrapTarget (a := Pickles.StatementPacked 16 (Type1 Fq) Fq) (b := Unit) main)
  let stepConsts (name : String) (n w : ℕ) : IO (Option (StepMainConsts n 1)) :=
    dumpConstants filter (dir / s!"{name}.json") (stepMainOf n w 1)
  let chainN2 ← stepConsts "step_main_simple_chain_n2_circuit" 2 2
  let makeZero ← stepConsts "step_main_two_phase_chain_make_zero_circuit" 0 1
  let increment ← stepConsts "step_main_two_phase_chain_increment_circuit" 1 1
  let treeReturn ← stepConsts "step_main_tree_proof_return_circuit" 2 2
  let importTpc ← stepConsts "step_main_import_two_phase_chain_circuit" 2 2
  let stepMains :=
    (chainN2.toList.map fun k => ("step_main_simple_chain_n2_circuit",
      stepTarget (a := Unit) (b := Pickles.StepStatement (Pickles.UnfVal 15) Fp 2)
        (stepMainDumpCircuit (inVal := Fp) (outVal := Unit) 2 (by decide) k dummyUnfN0
          simpleChainN2Rule)))
    ++ (makeZero.toList.map fun k => ("step_main_two_phase_chain_make_zero_circuit",
      stepTarget (a := Unit) (b := Pickles.StepStatement (Pickles.UnfVal 15) Fp 1)
        (stepMainDumpCircuit (inVal := Fp) (outVal := Unit) 1 (by decide) k dummyUnfN0
          makeZeroRule)))
    ++ (increment.toList.map fun k => ("step_main_two_phase_chain_increment_circuit",
      stepTarget (a := Unit) (b := Pickles.StepStatement (Pickles.UnfVal 15) Fp 1)
        (stepMainDumpCircuit (inVal := Fp) (outVal := Unit) 1 (by decide) k dummyUnfN0
          incrementRule)))
    ++ (treeReturn.toList.map fun k => ("step_main_tree_proof_return_circuit",
      stepTarget (a := Unit) (b := Pickles.StepStatement (Pickles.UnfVal 15) Fp 2)
        (stepMainDumpCircuit (inVal := Unit) (outVal := Fp) 2 (by decide) k dummyUnfN0
          fun _ => treeProofReturnRule)))
    ++ (importTpc.toList.map fun k => ("step_main_import_two_phase_chain_circuit",
      stepTarget (a := Unit) (b := Pickles.StepStatement (Pickles.UnfVal 15) Fp 2)
        (stepMainDumpCircuit (inVal := Unit) (outVal := Fp) 2 (by decide) k dummyUnfN0
          fun _ => importTwoPhaseChainRule)))
  -- the import's candidates reversed and repeated: the circuit sorts and dedups them, so the
  -- dump is the same
  let importTpcUnsorted := importTpc.toList.map fun (k : StepMainConsts 2 1) =>
    let s0 := k.slots[0]
    let d : Pickles.KnownDomains 1 :=
      { log2s := s0.domains.log2s.reverse ++ s0.domains.log2s
        log2s_le := fun x hx => s0.domains.log2s_le x (by simpa using hx)
        log2s_zkRows := fun x hx => s0.domains.log2s_zkRows x (by simpa using hx) }
    let s0' := { s0 with domains := d }
    ("step_main_import_two_phase_chain_circuit (candidates reversed, repeated)",
      "step_main_import_two_phase_chain_circuit",
      stepTarget (a := Unit) (b := Pickles.StepStatement (Pickles.UnfVal 15) Fp 2)
        (stepMainDumpCircuit (inVal := Unit) (outVal := Fp) 2 (by decide)
          { k with slots := k.slots.set 0 s0' } dummyUnfN0
          fun _ => importTwoPhaseChainRule))
  let named : List (String × String ×
      Comparison) :=
    (targets hStep hWrap
      ++ xhatTargets ++ wrapMains
      ++ stepMains).map fun (n, c) => (n, n, c)
  let selected := (named ++ importTpcUnsorted).filter fun (n, _) =>
    filter.isEmpty || (n.splitOn filter).length > 1
  let mut failures := 0
  for (name, dump, compare) in selected do
    let path := dir / s!"{dump}.json"
    let raw ← IO.FS.readFile path
    match Json.parse raw >>= compare with
    | .error e =>
      failures := failures + 1
      IO.println s!"✗ {name}: parse error: {e}"
    | .ok none =>
      failures := failures + 1
      IO.println s!"✗ {name}: not a comparison dump"
    | .ok (some checks) =>
      let bad := checks.filter (!·.2)
      if bad.isEmpty then
        IO.println s!"✓ {name}"
      else
        failures := failures + 1
        IO.println s!"✗ {name}: {String.intercalate ", " (bad.map (·.1))}"
  if failures > 0 then
    throw <| IO.userError s!"CS-equality FAILED ({failures} circuit(s))"
  IO.println s!"── CS equality OK ({selected.length} circuits) ──"
