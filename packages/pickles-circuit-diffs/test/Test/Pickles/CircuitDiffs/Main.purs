module Test.Pickles.CircuitDiffs.Main where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Perms (all, mkPerms)
import Node.FS.Sync as FS
import Pickles.CircuitDiffs.Circuit (Circuit, ComparableCircuit, comparable, fromCompiledCircuit, parseOcamlFixtures)
import Pickles.CircuitDiffs.PureScript.BCorrect (compileBCorrect)
import Pickles.CircuitDiffs.PureScript.BulletReduce (compileBulletReduce)
import Pickles.CircuitDiffs.PureScript.BulletReduceOne (compileBulletReduceOne)
import Pickles.CircuitDiffs.PureScript.BulletReduceOneStep (compileBulletReduceOneStep)
import Pickles.CircuitDiffs.PureScript.BulletReduceStep (compileBulletReduceStep)
import Pickles.CircuitDiffs.PureScript.CombinePoly (compileCombinePoly)
import Pickles.CircuitDiffs.PureScript.FopStep (compileFopStep)
import Pickles.CircuitDiffs.PureScript.FopWrap (compileFopWrap)
import Pickles.CircuitDiffs.PureScript.Ftcomm (compileFtcomm)
import Pickles.CircuitDiffs.PureScript.FtcommStep (compileFtcommStep)
import Pickles.CircuitDiffs.PureScript.FullStepVerifyOne (compileFullStepVerifyOne)
import Pickles.CircuitDiffs.PureScript.FullStepVerifyOneN2 (compileFullStepVerifyOneN2)
import Pickles.CircuitDiffs.PureScript.GroupMap (compileGroupMap)
import Pickles.CircuitDiffs.PureScript.GroupMapStep (compileGroupMapStep)
import Pickles.CircuitDiffs.PureScript.HashMessagesStep (compileHashMessagesStep)
import Pickles.CircuitDiffs.PureScript.HashMessagesWrap (compileHashMessagesWrap)
import Pickles.CircuitDiffs.PureScript.IvpStep (compileIvpStep)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams, compileIvpWrap)
import Pickles.CircuitDiffs.PureScript.LinearizationStep (compileLinearizationStep)
import Pickles.CircuitDiffs.PureScript.LinearizationWrap (compileLinearizationWrap)
import Pickles.CircuitDiffs.PureScript.OtherFieldCheck (compileOtherFieldCheck)
import Pickles.CircuitDiffs.PureScript.Pow2Pow (compilePow2Pow)
import Pickles.CircuitDiffs.PureScript.PseudoCircuits (compileChooseKeyN1Wrap, compileOneHotN17Step, compileOneHotN17Wrap, compileOneHotN1Step, compileOneHotN1Wrap, compileOneHotN3Step, compileOneHotN3Wrap, compilePseudoChooseN1Step, compilePseudoChooseN1Wrap, compilePseudoChooseN3Step, compilePseudoChooseN3Wrap, compilePseudoMaskN17Step, compilePseudoMaskN17Wrap, compilePseudoMaskN1Step, compilePseudoMaskN1Wrap, compilePseudoMaskN3Step, compilePseudoMaskN3Wrap, compileSideloadedVkTypStep, compileUtilsOnesVectorN16Step, compileUtilsOnesVectorN16Wrap)
import Pickles.CircuitDiffs.PureScript.StepMainAddOneReturn (compileStepMainAddOneReturn)
import Pickles.CircuitDiffs.PureScript.StepMainNoRecursionReturn (StepMainNoRecursionReturnParams, compileStepMainNoRecursionReturn)
import Pickles.CircuitDiffs.PureScript.StepMainSideLoadedChild (compileStepMainSideLoadedChild)
import Pickles.CircuitDiffs.PureScript.StepMainSideLoadedMain (compileStepMainSideLoadedMain)
import Pickles.CircuitDiffs.PureScript.StepMainSimpleChain (compileStepMainSimpleChain)
import Pickles.CircuitDiffs.PureScript.StepMainSimpleChainN2 (compileStepMainSimpleChainN2)
import Pickles.CircuitDiffs.PureScript.StepMainTreeProofReturn (compileStepMainTreeProofReturn)
import Pickles.CircuitDiffs.PureScript.StepMainTwoPhaseChainIncrement (compileStepMainTwoPhaseChainIncrement)
import Pickles.CircuitDiffs.PureScript.StepMainTwoPhaseChainMakeZero (compileStepMainTwoPhaseChainMakeZero)
import Pickles.CircuitDiffs.PureScript.StepVerify (compileStepVerify)
import Pickles.CircuitDiffs.PureScript.StepVerifyN2 (compileStepVerifyN2)
import Pickles.CircuitDiffs.PureScript.WrapMain (compileWrapMainN1)
import Pickles.CircuitDiffs.PureScript.WrapMainSideLoadedMain (compileWrapMainSideLoadedMain)
import Pickles.CircuitDiffs.PureScript.WrapMainAddOneReturn (compileWrapMainAddOneReturn)
import Pickles.CircuitDiffs.PureScript.WrapMainN2 (compileWrapMainN2)
import Pickles.CircuitDiffs.PureScript.WrapMainTreeProofReturn (compileWrapMainTreeProofReturn)
import Pickles.CircuitDiffs.PureScript.WrapMainTwoPhaseChain (compileWrapMainTwoPhaseChain)
import Pickles.CircuitDiffs.PureScript.WrapVerify (compileWrapVerify)
import Pickles.CircuitDiffs.PureScript.WrapVerifyN2 (compileWrapVerifyN2)
import Pickles.CircuitDiffs.PureScript.Xhat (compileXhat)
import Pickles.CircuitDiffs.PureScript.XhatStep (compileXhatStep)
import Pickles.CircuitDiffs.Types (CircuitComparison)
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Safe.Coerce (coerce)
import Simple.JSON (writeJSON)
import Snarky.Backend.Compile (compilePure)
import Snarky.Backend.Kimchi.Impl.Pallas (pallasCrsCreate)
import Snarky.Backend.Kimchi.Impl.Vesta (vestaCrsCreate)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (BoolVar, F(..), FVar, SizedF, all_, and_, any_, assertEqual_, assertNonZero_, assertNotEqual_, assertSquare_, assert_, const_, div_, equals_, exists, if_, inv_, mul_, or_, pow_, unpack_, xor_)
import Snarky.Circuit.DSL.Monad (class CircuitM, Snarky)
import Snarky.Circuit.Kimchi.AddComplete (Finiteness(..), addFast)
import Snarky.Circuit.Kimchi.EndoMul (endo)
import Snarky.Circuit.Kimchi.EndoScalar (toField)
import Snarky.Circuit.Kimchi.Poseidon (poseidon)
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast1, scaleFast2')
import Snarky.Constraint.Kimchi (KimchiConstraint, initialState)
import Snarky.Curves.Class (class PrimeField, class SerdeHex, EndoScalar(..), endoScalar)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (Type1(..))
import Test.Spec (SpecT, beforeAll_, describe, it, pending')
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess')
import Test.Spec.Runner.Node.Config as Cfg
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

type Fp = Vesta.ScalarField
type Fq = Pallas.ScalarField

fixtureDir :: String
fixtureDir = "packages/pickles-circuit-diffs/circuits/ocaml/"

readFixture :: String -> Effect String
readFixture path = do
  buf <- FS.readFile path
  Buffer.toString UTF8 buf

--------------------------------------------------------------------------------
-- SRS FFI

foreign import pallasSrsLagrangeCommitments :: CRS VestaG -> Int -> Int -> Array (AffinePoint Fq)
foreign import pallasSrsBlindingGenerator :: CRS VestaG -> AffinePoint Fq
foreign import vestaSrsLagrangeCommitments :: CRS PallasG -> Int -> Int -> Array (AffinePoint Fp)
foreign import vestaSrsBlindingGenerator :: CRS PallasG -> AffinePoint Fp

-- Index-based per-commitment lookup, OCaml-parity for
-- `Kimchi_bindings.Protocol.SRS.Fq/Fp.lagrange_commitment`. The per-index
-- variants remove the "numPublic" parameter at call sites — the walk fetches
-- commitments on demand from kimchi's cached basis.
foreign import pallasSrsLagrangeCommitmentAt :: CRS VestaG -> Int -> Int -> AffinePoint Fq
foreign import vestaSrsLagrangeCommitmentAt :: CRS PallasG -> Int -> Int -> AffinePoint Fp

--------------------------------------------------------------------------------
-- Output directories for serialized comparable circuits

resultsDir :: String
resultsDir = "packages/pickles-circuit-diffs/circuits/results/"

writeComparison :: String -> CircuitComparison -> Effect Unit
writeComparison path c = FS.writeTextFile UTF8 path (writeJSON c)

appendManifest :: String -> String -> Effect Unit
appendManifest name status =
  FS.appendTextFile UTF8 (resultsDir <> "manifest.jsonl")
    (writeJSON { name, status } <> "\n")

resetOutputDirs :: Effect Unit
resetOutputDirs = do
  let rmOpts = { force: true, maxRetries: 0, recursive: true, retryDelay: 0 }
  let mkdirOpts = { recursive: true, mode: mkPerms all all all }
  FS.rm' resultsDir rmOpts
  FS.mkdir' resultsDir mkdirOpts

--------------------------------------------------------------------------------
-- Compile helpers (basic circuits, Fp only)

compileFF :: (forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m (FVar Fp)) -> Circuit Fp
compileFF circuit = fromCompiledCircuit $
  compilePure (Proxy @(F Fp)) (Proxy @(F Fp)) (Proxy @(KimchiConstraint Fp)) circuit initialState

compileFB :: (forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m (BoolVar Fp)) -> Circuit Fp
compileFB circuit = fromCompiledCircuit $
  compilePure (Proxy @(F Fp)) (Proxy @Boolean) (Proxy @(KimchiConstraint Fp)) circuit initialState

compileFU :: (forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m Unit) -> Circuit Fp
compileFU circuit = fromCompiledCircuit $
  compilePure (Proxy @(F Fp)) (Proxy @Unit) (Proxy @(KimchiConstraint Fp)) circuit initialState

compileBB :: (forall c t m. CircuitM Fp c t m => BoolVar Fp -> Snarky c t m (BoolVar Fp)) -> Circuit Fp
compileBB circuit = fromCompiledCircuit $
  compilePure (Proxy @Boolean) (Proxy @Boolean) (Proxy @(KimchiConstraint Fp)) circuit initialState

compileBU :: (forall c t m. CircuitM Fp c t m => BoolVar Fp -> Snarky c t m Unit) -> Circuit Fp
compileBU circuit = fromCompiledCircuit $
  compilePure (Proxy @Boolean) (Proxy @Unit) (Proxy @(KimchiConstraint Fp)) circuit initialState

type TwoPoints = Tuple (AffinePoint (F Fp)) (AffinePoint (F Fp))
type Point = AffinePoint (F Fp)
type PointField = Tuple (AffinePoint (F Fp)) (F Fp)
type V3 = Vector 3 (F Fp)

compilePP
  :: ( forall t m
        . CircuitM Fp (KimchiConstraint Fp) t m
       => Tuple (AffinePoint (FVar Fp)) (AffinePoint (FVar Fp))
       -> Snarky (KimchiConstraint Fp) t m (AffinePoint (FVar Fp))
     )
  -> Circuit Fp
compilePP circuit = fromCompiledCircuit $
  compilePure (Proxy @TwoPoints) (Proxy @Point) (Proxy @(KimchiConstraint Fp)) circuit initialState

compilePF
  :: ( forall t m
        . CircuitM Fp (KimchiConstraint Fp) t m
       => Tuple (AffinePoint (FVar Fp)) (FVar Fp)
       -> Snarky (KimchiConstraint Fp) t m (AffinePoint (FVar Fp))
     )
  -> Circuit Fp
compilePF circuit = fromCompiledCircuit $
  compilePure (Proxy @PointField) (Proxy @Point) (Proxy @(KimchiConstraint Fp)) circuit initialState

compileKFF
  :: ( forall t m
        . CircuitM Fp (KimchiConstraint Fp) t m
       => FVar Fp
       -> Snarky (KimchiConstraint Fp) t m (FVar Fp)
     )
  -> Circuit Fp
compileKFF circuit = fromCompiledCircuit $
  compilePure (Proxy @(F Fp)) (Proxy @(F Fp)) (Proxy @(KimchiConstraint Fp)) circuit initialState

compileV3
  :: ( forall t m
        . CircuitM Fp (KimchiConstraint Fp) t m
       => Vector 3 (FVar Fp)
       -> Snarky (KimchiConstraint Fp) t m (Vector 3 (FVar Fp))
     )
  -> Circuit Fp
compileV3 circuit = fromCompiledCircuit $
  compilePure (Proxy @V3) (Proxy @V3) (Proxy @(KimchiConstraint Fp)) circuit initialState

--------------------------------------------------------------------------------
-- Field arithmetic circuits

mulCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m (FVar Fp)
mulCircuit x = do
  y <- exists (pure (zero :: F Fp))
  mul_ x y

invCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m (FVar Fp)
invCircuit x = inv_ x

divCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m (FVar Fp)
divCircuit x = do
  y <- exists (pure (zero :: F Fp))
  div_ x y

ifCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m (FVar Fp)
ifCircuit x = do
  y <- exists (pure (zero :: F Fp))
  b <- exists (pure true)
  if_ b x y

equalsCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m (BoolVar Fp)
equalsCircuit x = do
  y <- exists (pure (zero :: F Fp))
  equals_ x y

pow7Circuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m (FVar Fp)
pow7Circuit x = pow_ x 7

pow8Circuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m (FVar Fp)
pow8Circuit x = pow_ x 8

--------------------------------------------------------------------------------
-- Assertion circuits

assertEqualCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m Unit
assertEqualCircuit x = do
  y <- exists (pure (zero :: F Fp))
  assertEqual_ x y

-- | Application body for `dump_two_phase_chain`'s branch 0
-- | (`make_zero`): assert that the public input equals zero. PS
-- | mirror of `app_circuit_two_phase_chain_make_zero` in
-- | `dump_circuit_impl.ml`. Foundational for the multi-branch
-- | trace-diff loop — if PS and OCaml disagree on the gate
-- | sequence for this trivial body, every downstream step_main /
-- | wrap_main / witness comparison is meaningless.
makeZeroAppCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m Unit
makeZeroAppCircuit x = assertEqual_ x (const_ zero)

-- | Application body for `dump_two_phase_chain`'s branch 1
-- | (`increment`): allocate prev as a witness, assert that the
-- | public input equals `prev + 1`. PS mirror of
-- | `app_circuit_two_phase_chain_increment`.
incrementAppCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m Unit
incrementAppCircuit x = do
  prev <- exists (pure (zero :: F Fp))
  assertEqual_ x (CVar.add_ (const_ one) prev)

assertSquareCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m Unit
assertSquareCircuit x = do
  y <- exists (pure (zero :: F Fp))
  assertSquare_ x y

assertNonZeroCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m Unit
assertNonZeroCircuit x = assertNonZero_ x

assertNotEqualCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m Unit
assertNotEqualCircuit x = do
  y <- exists (pure (zero :: F Fp))
  assertNotEqual_ x y

unpackCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m Unit
unpackCircuit x = do
  _ <- unpack_ x (Proxy @254)
  pure unit

--------------------------------------------------------------------------------
-- Boolean circuits

boolAndCircuit :: forall c t m. CircuitM Fp c t m => BoolVar Fp -> Snarky c t m (BoolVar Fp)
boolAndCircuit x = do
  y <- exists (pure true)
  and_ x y

boolOrCircuit :: forall c t m. CircuitM Fp c t m => BoolVar Fp -> Snarky c t m (BoolVar Fp)
boolOrCircuit x = do
  y <- exists (pure true)
  or_ x y

boolXorCircuit :: forall c t m. CircuitM Fp c t m => BoolVar Fp -> Snarky c t m (BoolVar Fp)
boolXorCircuit x = do
  y <- exists (pure true)
  xor_ x y

boolAllCircuit :: forall c t m. CircuitM Fp c t m => BoolVar Fp -> Snarky c t m (BoolVar Fp)
boolAllCircuit x = do
  y <- exists (pure true)
  w <- exists (pure true)
  all_ [ x, y, w ]

boolAnyCircuit :: forall c t m. CircuitM Fp c t m => BoolVar Fp -> Snarky c t m (BoolVar Fp)
boolAnyCircuit x = do
  y <- exists (pure true)
  w <- exists (pure true)
  any_ [ x, y, w ]

boolAssertCircuit :: forall c t m. CircuitM Fp c t m => BoolVar Fp -> Snarky c t m Unit
boolAssertCircuit x = assert_ x

--------------------------------------------------------------------------------
-- Kimchi gate circuits

addCompleteCircuit
  :: forall t m
   . CircuitM Fp (KimchiConstraint Fp) t m
  => Tuple (AffinePoint (FVar Fp)) (AffinePoint (FVar Fp))
  -> Snarky (KimchiConstraint Fp) t m (AffinePoint (FVar Fp))
addCompleteCircuit (Tuple p1 p2) =
  _.p <$> addFast DontCheckFinite p1 p2

endoScalarCircuit
  :: forall t m
   . CircuitM Fp (KimchiConstraint Fp) t m
  => FVar Fp
  -> Snarky (KimchiConstraint Fp) t m (FVar Fp)
endoScalarCircuit scalar =
  let
    EndoScalar es = endoScalar @Vesta.BaseField @Fp
  in
    toField @8 (unsafeCoerce scalar :: SizedF 128 (FVar Fp)) (const_ es)

varBaseMulCircuit
  :: forall t m
   . CircuitM Fp (KimchiConstraint Fp) t m
  => Tuple (AffinePoint (FVar Fp)) (FVar Fp)
  -> Snarky (KimchiConstraint Fp) t m (AffinePoint (FVar Fp))
varBaseMulCircuit (Tuple g scalar) =
  scaleFast1 @51 g (Type1 scalar)

endoMulCircuit
  :: forall t m
   . CircuitM Fp (KimchiConstraint Fp) t m
  => Tuple (AffinePoint (FVar Fp)) (FVar Fp)
  -> Snarky (KimchiConstraint Fp) t m (AffinePoint (FVar Fp))
endoMulCircuit (Tuple g scalar) =
  endo @128 @32 g (unsafeCoerce scalar :: SizedF 128 (FVar Fp))

scaleFast2_128Circuit
  :: forall t m
   . CircuitM Fp (KimchiConstraint Fp) t m
  => Tuple (AffinePoint (FVar Fp)) (FVar Fp)
  -> Snarky (KimchiConstraint Fp) t m (AffinePoint (FVar Fp))
scaleFast2_128Circuit (Tuple g scalar) =
  scaleFast2' @26 @127 g scalar

poseidonCircuit
  :: forall t m
   . CircuitM Fp (KimchiConstraint Fp) t m
  => Vector 3 (FVar Fp)
  -> Snarky (KimchiConstraint Fp) t m (Vector 3 (FVar Fp))
poseidonCircuit = poseidon

--------------------------------------------------------------------------------
-- Test infrastructure

loadOcamlCircuit :: forall f. Ord f => SerdeHex f => PrimeField f => String -> Effect (Circuit f)
loadOcamlCircuit name = do
  circuit <- readFixture (fixtureDir <> name <> ".json")
  cachedConstants <- readFixture (fixtureDir <> name <> "_cached_constants.json")
  gateLabels <- readFixture (fixtureDir <> name <> "_gate_labels.jsonl")
  case parseOcamlFixtures { circuit, cachedConstants, gateLabels } of
    Right c -> pure c
    Left e -> throw $ "Failed to parse OCaml fixtures: " <> show e

-- | Strip metadata fields for equality comparison (context and variables are not part of the constraint system)
stripMetadata :: ComparableCircuit -> ComparableCircuit
stripMetadata c = c
  { gates = map (_ { context = [], variables = Nothing }) c.gates
  , cachedConstants = Array.sort $ map (\cc -> cc { variable = 0 }) c.cachedConstants
  }

exactMatch :: forall f. Ord f => SerdeHex f => PrimeField f => String -> Circuit f -> SpecT Aff Unit Aff Unit
exactMatch name ps = exactMatchEff name (pure ps)

-- | Variant for circuits whose construction is `Effect`-bound (e.g. the
-- | `compileStepMain*` helpers that thread `CircuitBuilderT` state through
-- | a real `Effect` context). Equivalent to `exactMatch` after running the
-- | producing action — provided so call sites don't need an
-- | `unsafePerformEffect` shim at the boundary.
exactMatchEff
  :: forall f
   . Ord f
  => SerdeHex f
  => PrimeField f
  => String
  -> Effect (Circuit f)
  -> SpecT Aff Unit Aff Unit
exactMatchEff name effPs =
  it (name <> " matches OCaml") do
    ps <- liftEffect effPs
    ocaml <- liftEffect $ (loadOcamlCircuit name :: Effect (Circuit f))
    let psCircuit = comparable ps
    let ocamlCircuit = comparable ocaml
    let psNoCtx = stripMetadata psCircuit
    let ocamlNoCtx = stripMetadata ocamlCircuit
    let status = if psNoCtx == ocamlNoCtx then "match" else "mismatch"
    let comparison = { name, status, purescript: psCircuit, ocaml: ocamlCircuit }
    liftEffect do
      writeComparison (resultsDir <> name <> ".json") comparison
      appendManifest name status
    unless (status == "match") $
      psNoCtx `shouldEqual` ocamlNoCtx

--------------------------------------------------------------------------------
-- Test spec

main :: Effect Unit
main =
  runSpecAndExitProcess' { defaultConfig: Cfg.defaultConfig, parseCLIOptions: true }
    [ consoleReporter ]
    spec

spec :: SpecT Aff Unit Aff Unit
spec =
  beforeAll_ (liftEffect resetOutputDirs) $
    describe "Circuit comparison" do
      describe "Field arithmetic" do
        exactMatch "mul_step_circuit" (compileFF mulCircuit)
        exactMatch "inv_step_circuit" (compileFF invCircuit)
        exactMatch "div_step_circuit" (compileFF divCircuit)
        exactMatch "if_step_circuit" (compileFF ifCircuit)
        exactMatch "equals_step_circuit" (compileFB equalsCircuit)
        exactMatch "pow7_step_circuit" (compileFF pow7Circuit)
        exactMatch "pow8_step_circuit" (compileFF pow8Circuit)
      describe "Assertions" do
        exactMatch "assert_equal_step_circuit" (compileFU assertEqualCircuit)
        exactMatch "assert_non_zero_step_circuit" (compileFU assertNonZeroCircuit)
        exactMatch "assert_not_equal_step_circuit" (compileFU assertNotEqualCircuit)
        exactMatch "assert_square_step_circuit" (compileFU assertSquareCircuit)
        exactMatch "unpack_step_circuit" (compileFU unpackCircuit)
      describe "Boolean" do
        exactMatch "bool_and_step_circuit" (compileBB boolAndCircuit)
        exactMatch "bool_or_step_circuit" (compileBB boolOrCircuit)
        exactMatch "bool_xor_step_circuit" (compileBB boolXorCircuit)
        exactMatch "bool_all_step_circuit" (compileBB boolAllCircuit)
        exactMatch "bool_any_step_circuit" (compileBB boolAnyCircuit)
        exactMatch "bool_assert_step_circuit" (compileBU boolAssertCircuit)
      describe "Two-phase chain application circuits" do
        -- App-level rule bodies for `dump_two_phase_chain` (the
        -- minimal multi-branch fixture). We byte-compare ONLY the
        -- application bodies — without step_main scaffolding —
        -- because rule-body parity is the foundation: if the user-
        -- written assertions don't compile to the same gates in PS
        -- and OCaml, every downstream comparison (witness, oracles,
        -- deferred values, wrap_main) is rooted in noise. The full
        -- multi-branch step_main diff comes later, once PS supports
        -- multi-branch compile.
        exactMatch "app_circuit_two_phase_chain_make_zero" (compileFU makeZeroAppCircuit)
        exactMatch "app_circuit_two_phase_chain_increment" (compileFU incrementAppCircuit)
      describe "Kimchi gates" do
        exactMatch "add_complete_step_circuit" (compilePP addCompleteCircuit)
        exactMatch "endo_scalar_step_circuit" (compileKFF endoScalarCircuit)
        exactMatch "var_base_mul_step_circuit" (compilePF varBaseMulCircuit)
        exactMatch "endo_mul_step_circuit" (compilePF endoMulCircuit)
        exactMatch "scale_fast2_128_step_circuit" (compilePF scaleFast2_128Circuit)
        exactMatch "poseidon_step_circuit" (compileV3 poseidonCircuit)
      describe "Pickles Step sub-circuits" do
        exactMatch "pow2_pow_step_circuit" (fromCompiledCircuit compilePow2Pow)
        exactMatch "b_correct_step_circuit" (fromCompiledCircuit compileBCorrect)
        exactMatch "hash_messages_for_next_step_proof_circuit" (fromCompiledCircuit compileHashMessagesStep)
        exactMatch "finalize_other_proof_step_circuit" (fromCompiledCircuit compileFopStep)
        exactMatch "group_map_step_circuit" (fromCompiledCircuit compileGroupMapStep)
        exactMatch "bullet_reduce_one_step_circuit" (fromCompiledCircuit compileBulletReduceOneStep)
        exactMatch "bullet_reduce_step_circuit" (fromCompiledCircuit compileBulletReduceStep)
        exactMatch "ftcomm_step_circuit" (fromCompiledCircuit compileFtcommStep)
        let
          stepSrs = pallasCrsCreate (2 `Int.pow` 16)
          stepSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                (coerce (vestaSrsLagrangeCommitmentAt stepSrs 16 i)) :: AffinePoint (F Fp)
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepSrs) :: AffinePoint (F Fp)
            }
        exactMatch "xhat_step_circuit" (fromCompiledCircuit $ compileXhatStep stepSrsData)
      describe "Pickles Wrap sub-circuits" do
        exactMatch "hash_messages_for_next_wrap_proof_circuit" (fromCompiledCircuit compileHashMessagesWrap)
        exactMatch "finalize_other_proof_wrap_circuit" (fromCompiledCircuit compileFopWrap)
        exactMatch "group_map_wrap_circuit" (fromCompiledCircuit compileGroupMap)
        exactMatch "bullet_reduce_one_wrap_circuit" (fromCompiledCircuit compileBulletReduceOne)
        exactMatch "bullet_reduce_wrap_circuit" (fromCompiledCircuit compileBulletReduce)
        exactMatch "ftcomm_wrap_circuit" (fromCompiledCircuit compileFtcomm)
        exactMatch "combine_poly_wrap_circuit" (fromCompiledCircuit compileCombinePoly)
        let
          srs = vestaCrsCreate (2 `Int.pow` 16)
          wrapSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                coerce (pallasSrsLagrangeCommitmentAt srs 16 i)
            , blindingH: coerce $ pallasSrsBlindingGenerator srs
            }
        exactMatch "xhat_wrap_circuit" (fromCompiledCircuit $ compileXhat wrapSrsData)
      describe "IVP" do
        let
          wrapSrs = vestaCrsCreate (2 `Int.pow` 16)
          wrapSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                coerce (pallasSrsLagrangeCommitmentAt wrapSrs 16 i)
            , blindingH: coerce $ pallasSrsBlindingGenerator wrapSrs
            }
        exactMatch "ivp_wrap_circuit" (fromCompiledCircuit $ compileIvpWrap wrapSrsData)
        exactMatch "wrap_verify_circuit" (fromCompiledCircuit $ compileWrapVerify wrapSrsData)
        exactMatch "wrap_verify_n2_circuit" (fromCompiledCircuit $ compileWrapVerifyN2 wrapSrsData)
        let
          -- wrap_main_circuit fixture uses domainLog2 = 14 to match the
          -- production Simple_chain N1 wrap compile (verified via OCaml
          -- `compile.wrap_domains.h.log2` trace). The matching change in
          -- dump_circuit_impl.ml passes ~domain_log2:14 to
          -- Wrap_main_for_dump.build, and the PS WrapMain.purs config
          -- pins domainLog2s = 14. The lagrange closure here has to
          -- return commitments at domain size 2^14 to match.
          wrapMainSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                coerce (pallasSrsLagrangeCommitmentAt wrapSrs 14 i)
            , blindingH: coerce $ pallasSrsBlindingGenerator wrapSrs
            }
          -- N=1 step CS commits over the Vesta SRS at log2=14. The
          -- step shape is the same one `step_main_simple_chain_circuit`
          -- already byte-matches.
          wrapMainN1StepSrs = pallasCrsCreate (2 `Int.pow` 15)
          wrapMainN1StepSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                (coerce (vestaSrsLagrangeCommitmentAt wrapMainN1StepSrs 14 i)) :: AffinePoint (F Fp)
            , blindingH: (coerce $ vestaSrsBlindingGenerator wrapMainN1StepSrs) :: AffinePoint (F Fp)
            }
        -- N=1 Input mode (Simple_chain). step_widths=[1], padded=[[0];[1]].
        -- `compileWrapMainN1` deterministically computes the step VK by
        -- recompiling the matching step CS and running the kimchi
        -- commitment pipeline (mirrors the wrap_main_n2_circuit fix at
        -- commit `cf352650`).
        exactMatchEff "wrap_main_circuit"
          (fromCompiledCircuit <$> compileWrapMainN1 wrapMainSrsData wrapMainN1StepSrsData)
        -- N=1 side-loaded parent (`Simple_chain` from `dump_side_loaded_main`).
        -- Same shape as `wrap_main_circuit` but the prev slot's bound is
        -- N2 instead of N1: step_widths=[1], padded=[[0];[2]],
        -- domain_log2=14. `compileWrapMainSideLoadedMain` deterministically
        -- computes the step VK by recompiling the matching step CS
        -- (mirrors the wrap_main_n2_circuit fix in commit `cf352650`).
        let
          -- Step SRS data for SideLoadedMain: same shape as
          -- `wrapMainN1StepSrsData` but with the side-loaded
          -- per-domain lagrange tables at log2 ∈ {13, 14, 15}.
          wrapMainSlmStepSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                (coerce (vestaSrsLagrangeCommitmentAt wrapMainN1StepSrs 14 i)) :: AffinePoint (F Fp)
            , sideloadedPerDomainLagrangeAt:
                ( \i -> (coerce (vestaSrsLagrangeCommitmentAt wrapMainN1StepSrs 13 i)) :: AffinePoint (F Fp) )
                  :< ( \i -> (coerce (vestaSrsLagrangeCommitmentAt wrapMainN1StepSrs 14 i)) :: AffinePoint (F Fp) )
                  :< ( \i -> (coerce (vestaSrsLagrangeCommitmentAt wrapMainN1StepSrs 15 i)) :: AffinePoint (F Fp) )
                  :< Vector.nil
            , blindingH: (coerce $ vestaSrsBlindingGenerator wrapMainN1StepSrs) :: AffinePoint (F Fp)
            }
        exactMatchEff "wrap_main_side_loaded_main_circuit"
          (fromCompiledCircuit <$> compileWrapMainSideLoadedMain wrapMainSrsData wrapMainSlmStepSrsData)
        -- N=2 Input mode (Simple_chain_n2). step_widths=[2], padded=[[0;2];[0;2]].
        -- `compileWrapMainN2` deterministically computes the step VK by
        -- recompiling the matching step CS and running the kimchi
        -- commitment pipeline. Needs `stepMainN2StepSrsData` (the same
        -- data used by `step_main_simple_chain_n2_circuit` below).
        --
        -- The wrap-side lagrange basis is at log2=14 (same as
        -- `wrap_main_circuit`): `dump_simple_chain_n2.ml` passes
        -- `~override_wrap_domain:Proofs_verified.N1`, so the wrap
        -- domain is N1 = Pow_2_roots_of_unity 14.
        let
          wrapMainN2SrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                coerce (pallasSrsLagrangeCommitmentAt wrapSrs 15 i)
            , blindingH: coerce $ pallasSrsBlindingGenerator wrapSrs
            }
          wrapMainN2StepSrs = pallasCrsCreate (2 `Int.pow` 15)
          wrapMainN2StepSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                (coerce (vestaSrsLagrangeCommitmentAt wrapMainN2StepSrs 14 i)) :: AffinePoint (F Fp)
            , blindingH: (coerce $ vestaSrsBlindingGenerator wrapMainN2StepSrs) :: AffinePoint (F Fp)
            }
        exactMatchEff "wrap_main_n2_circuit"
          (fromCompiledCircuit <$> compileWrapMainN2 wrapMainN2SrsData wrapMainN2StepSrsData)
        -- N=0 Input_and_output mode (Add_one_return). step_widths=[0],
        -- padded=[[0];[0]]. First (and only) N=0 wrap fixture — exercises
        -- the wrap verify-one-of-step path with a step proof whose own
        -- public input is just the msgForNextStep digest (no unfinalized
        -- proofs, no msg_wrap entries). Uses domain_log2=13 (step domain
        -- for the N=0 step circuit is 2^9, wrap domain is 2^13 per OCaml
        -- dump_add_one_return's `compile.wrap_domains.h.log2` trace).
        let
          -- Lagrange lookup is for the STEP proof's evaluation domain
          -- (= step circuit's domain log2 = 9 for AOR), NOT the wrap
          -- circuit's domain log2 = 13. Mirrors `wrap_main_circuit`
          -- and `wrap_main_n2_circuit` test setups where the lagrange
          -- log2 matches `domainLog2s` (the step proof's domain).
          wrapMainAddOneReturnSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                coerce (pallasSrsLagrangeCommitmentAt wrapSrs 9 i)
            , blindingH: coerce $ pallasSrsBlindingGenerator wrapSrs
            }
          -- Step CS params for Add_one_return (mpv=0, no prev proofs).
          -- Lagrange lookup is unused at mpv=0 (perSlotLagrangeAt is
          -- Vector.nil). blindingH and SRS size match the Vesta CRS
          -- used by createCRS in deriveStepVKFromCompiled.
          aorStepSrs = pallasCrsCreate (2 `Int.pow` 15)
          aorStepSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                (coerce (vestaSrsLagrangeCommitmentAt aorStepSrs 14 i)) :: AffinePoint (F Fp)
            , blindingH: (coerce $ vestaSrsBlindingGenerator aorStepSrs) :: AffinePoint (F Fp)
            }
        exactMatchEff "wrap_main_add_one_return_circuit"
          (fromCompiledCircuit <$> compileWrapMainAddOneReturn wrapMainAddOneReturnSrsData aorStepSrsData)
        -- N=2 Output mode (Tree_proof_return). Single branch with
        -- heterogeneous prev slots [0; 2] (No_recursion_return at
        -- slot 0, self at slot 1). step_widths=[2], padded=[[0];[2]].
        -- TPR step CS has step_domain log2 = 15 (empirically verified
        -- via OC's `branch_data` row 81 R coeff = 4*15 = 60); wrap
        -- circuit uses override_wrap_domain:N1 → wrap domain log2 = 14.
        -- The IVP MSM lagrange lookup is at the STEP domain log2 (15),
        -- matching `domainLog2s` in the WrapMainConfig.
        let
          wrapMainTprSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                coerce (pallasSrsLagrangeCommitmentAt wrapSrs 15 i)
            , blindingH: coerce $ pallasSrsBlindingGenerator wrapSrs
            }
          -- Step CS params for TPR (mpv=2, heterogeneous prevs [N0,N2]).
          -- Per-slot lagrange domains: slot 0 (NRR) at 2^13, slot 1
          -- (self) at 2^14 (override_wrap_domain:N1). Same shape used
          -- by `step_main_tree_proof_return_circuit`'s direct test.
          tprStepSrs = pallasCrsCreate (2 `Int.pow` 15)
          tprLagrangeAtD13 = mkConstLagrangeBaseLookup \i ->
            (coerce (vestaSrsLagrangeCommitmentAt tprStepSrs 13 i)) :: AffinePoint (F Fp)
          tprLagrangeAtD14 = mkConstLagrangeBaseLookup \i ->
            (coerce (vestaSrsLagrangeCommitmentAt tprStepSrs 14 i)) :: AffinePoint (F Fp)
          -- NRR wrap+step SRS data for the chained NRR compile inside
          -- compileStepMainTreeProofReturn (the wrap fixture goes through
          -- it transitively via compileWrapMainTreeProofReturn).
          wrapTprNrrWrapSrsData :: IvpWrapParams
          wrapTprNrrWrapSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                coerce (pallasSrsLagrangeCommitmentAt wrapSrs 9 i)
            , blindingH: coerce $ pallasSrsBlindingGenerator wrapSrs
            }
          wrapTprNrrStepSrsData :: StepMainNoRecursionReturnParams
          wrapTprNrrStepSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                (coerce (vestaSrsLagrangeCommitmentAt tprStepSrs 14 i)) :: AffinePoint (F Fp)
            , blindingH: (coerce $ vestaSrsBlindingGenerator tprStepSrs) :: AffinePoint (F Fp)
            }
          tprStepSrsData =
            { perSlotLagrangeAt: tprLagrangeAtD13 :< tprLagrangeAtD14 :< Vector.nil
            , blindingH: (coerce $ vestaSrsBlindingGenerator tprStepSrs) :: AffinePoint (F Fp)
            , nrrWrapSrsData: wrapTprNrrWrapSrsData
            , nrrStepSrsData: wrapTprNrrStepSrsData
            }
        exactMatchEff "wrap_main_tree_proof_return_circuit"
          (fromCompiledCircuit <$> compileWrapMainTreeProofReturn wrapMainTprSrsData tprStepSrsData)
        -- Multi-branch (2 branches: make_zero + increment) sharing ONE wrap
        -- key. step_widths=[0;1], padded=[[0;0];[0;1]]; per-branch step
        -- domains [9; 14] differ (make_zero is tiny, increment full),
        -- so wrap_main goes through the per-branch dispatch path.
        -- Lagrange lookup is per-branch — needs the wrap SRS directly.
        -- Step VKs are derived per-branch (mirrors the deterministic
        -- VK fix family — wrap_main_circuit, wrap_main_tree_proof_return).
        let
          tpcStepSrs = pallasCrsCreate (2 `Int.pow` 15)
          tpcMakeZeroSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                (coerce (vestaSrsLagrangeCommitmentAt tpcStepSrs 14 i)) :: AffinePoint (F Fp)
            , blindingH: (coerce $ vestaSrsBlindingGenerator tpcStepSrs) :: AffinePoint (F Fp)
            }
          tpcIncrementSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                (coerce (vestaSrsLagrangeCommitmentAt tpcStepSrs 14 i)) :: AffinePoint (F Fp)
            , blindingH: (coerce $ vestaSrsBlindingGenerator tpcStepSrs) :: AffinePoint (F Fp)
            }
          wrapMainTpcParams =
            { vestaSrs: wrapSrs
            , lagrangeAt: wrapMainSrsData.lagrangeAt
            , blindingH: wrapMainSrsData.blindingH
            , makeZeroStepSrsData: tpcMakeZeroSrsData
            , incrementStepSrsData: tpcIncrementSrsData
            }
        exactMatchEff "wrap_main_two_phase_chain_circuit"
          (fromCompiledCircuit <$> compileWrapMainTwoPhaseChain wrapMainTpcParams)
        let
          -- OCaml uses SRS.Fq.create (1 lsl 15) and domain Pow_2_roots_of_unity 15
          stepSrs = pallasCrsCreate (2 `Int.pow` 15)
          stepSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                (coerce (vestaSrsLagrangeCommitmentAt stepSrs 15 i)) :: AffinePoint (F Fp)
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepSrs) :: AffinePoint (F Fp)
            }
        exactMatch "ivp_step_circuit" (fromCompiledCircuit $ compileIvpStep stepSrsData)
      describe "Step verify" do
        let
          -- Same SRS as IVP step: OCaml uses SRS.Fq.create (1 lsl 15) and domain 15
          stepVerifySrs = pallasCrsCreate (2 `Int.pow` 15)
          stepVerifySrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                (coerce (vestaSrsLagrangeCommitmentAt stepVerifySrs 15 i)) :: AffinePoint (F Fp)
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepVerifySrs) :: AffinePoint (F Fp)
            }
        exactMatch "step_verify_circuit" (fromCompiledCircuit $ compileStepVerify stepVerifySrsData)
        let
          stepVerifyN2SrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                (coerce (vestaSrsLagrangeCommitmentAt stepVerifySrs 15 i)) :: AffinePoint (F Fp)
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepVerifySrs) :: AffinePoint (F Fp)
            }
        exactMatch "step_verify_n2_circuit" (fromCompiledCircuit $ compileStepVerifyN2 stepVerifyN2SrsData)
      describe "Full step verify_one" do
        let
          fullStepSrs = pallasCrsCreate (2 `Int.pow` 15)
          fullStepSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                (coerce (vestaSrsLagrangeCommitmentAt fullStepSrs 14 i)) :: AffinePoint (F Fp)
            , blindingH: (coerce $ vestaSrsBlindingGenerator fullStepSrs) :: AffinePoint (F Fp)
            }
        exactMatch "full_step_verify_one_circuit" (fromCompiledCircuit $ compileFullStepVerifyOne fullStepSrsData)
        let
          fullStepN2SrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                (coerce (vestaSrsLagrangeCommitmentAt fullStepSrs 14 i)) :: AffinePoint (F Fp)
            , blindingH: (coerce $ vestaSrsBlindingGenerator fullStepSrs) :: AffinePoint (F Fp)
            }
        exactMatch "full_step_verify_one_n2_circuit" (fromCompiledCircuit $ compileFullStepVerifyOneN2 fullStepN2SrsData)
      describe "Typ checks" do
        exactMatch "other_field_check_step_circuit" (fromCompiledCircuit compileOtherFieldCheck)
      describe "Step main" do
        let
          -- OCaml uses SRS.Fq.create (1 lsl 15), wrap domain Pow_2_roots_of_unity 14
          stepMainSrs = pallasCrsCreate (2 `Int.pow` 15)
          stepMainSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                (coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 14 i)) :: AffinePoint (F Fp)
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepMainSrs) :: AffinePoint (F Fp)
            }
        -- N=1, Input mode. Public input layout is input field only.
        exactMatchEff "step_main_simple_chain_circuit" (fromCompiledCircuit <$> compileStepMainSimpleChain stepMainSrsData)
        let
          stepMainN2SrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                (coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 14 i)) :: AffinePoint (F Fp)
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepMainSrs) :: AffinePoint (F Fp)
            }
        -- N=2, Input mode. Two prev proofs verified by verify_one.
        exactMatchEff "step_main_simple_chain_n2_circuit" (fromCompiledCircuit <$> compileStepMainSimpleChainN2 stepMainN2SrsData)
        -- N=0, Input_and_output mode — Add_one_return. No recursion,
        -- no verify_one; the hash_messages_for_next_step_proof absorbs
        -- BOTH input and output fields (OCaml step_main.ml:566-573
        -- Input_and_output branch → `to_field_elements (app_state, ret_var)`).
        exactMatchEff "step_main_add_one_return_circuit" (fromCompiledCircuit <$> compileStepMainAddOneReturn stepMainSrsData)
        -- N=0, Output mode — No_recursion_return. Rule returns
        -- `output = 0` with no input. Exercises the Output-mode branch
        -- of step_main.ml:566-573 (`Output _ -> ret_var`) at N=0: the
        -- hash_messages_for_next_step_proof absorbs ONLY the output
        -- field (no input contribution). Precursor to Tree_proof_return's
        -- proof-level byte-for-byte test, which consumes a real
        -- No_recursion_return proof in slot 0.
        exactMatchEff "step_main_no_recursion_return_circuit" (fromCompiledCircuit <$> compileStepMainNoRecursionReturn stepMainSrsData)
        -- N=2, Output mode, HETEROGENEOUS prevs (No_recursion_return @ N0,
        -- self @ N2). All four layers of heterogeneity wired up:
        -- * per-slot SPPW sizing  (`PrevsSpecCons 0 (PrevsSpecCons 2 …)`)
        -- * per-slot FOP domain   (`[13, 14]`)
        -- * per-slot wrap VK      (`[Just no_rec_vk, Nothing]`)
        -- * per-slot lagrange     (`[domain 13 lookup, domain 14 lookup]`).
        let
          lagrangeAtD13 =
            mkConstLagrangeBaseLookup \i ->
              (coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 13 i)) :: AffinePoint (F Fp)
          lagrangeAtD14 =
            mkConstLagrangeBaseLookup \i ->
              (coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 14 i)) :: AffinePoint (F Fp)
          -- SRS data for compiling NRR's wrap CS up-front, used to
          -- derive slot 0's known wrap key (replacing the prior
          -- 28-copies-of-Pallas-generator placeholder). Mirrors
          -- `wrapMainAddOneReturnSrsData` (NRR is N=0 leaf rule, same
          -- wrap config as AOR — IVP MSM lookup at step domain log2 9).
          tprNrrWrapSrs = vestaCrsCreate (2 `Int.pow` 16)
          tprNrrWrapSrsData :: IvpWrapParams
          tprNrrWrapSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                coerce (pallasSrsLagrangeCommitmentAt tprNrrWrapSrs 9 i)
            , blindingH: coerce $ pallasSrsBlindingGenerator tprNrrWrapSrs
            }
          -- NRR step CS SRS data. lagrangeAt is unused at mpv=0
          -- (`compileStepMainNoRecursionReturn` passes Vector.nil for
          -- perSlotLagrangeAt) but still required by the params type.
          -- Same shape as `aorStepSrsData`.
          tprNrrStepSrsData :: StepMainNoRecursionReturnParams
          tprNrrStepSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                (coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 14 i)) :: AffinePoint (F Fp)
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepMainSrs) :: AffinePoint (F Fp)
            }
          treeProofReturnSrsData =
            { perSlotLagrangeAt: lagrangeAtD13 :< lagrangeAtD14 :< Vector.nil
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepMainSrs) :: AffinePoint (F Fp)
            , nrrWrapSrsData: tprNrrWrapSrsData
            , nrrStepSrsData: tprNrrStepSrsData
            }
        exactMatchEff "step_main_tree_proof_return_circuit" (fromCompiledCircuit <$> compileStepMainTreeProofReturn treeProofReturnSrsData)
        -- N=1 parent + single SIDE-LOADED prev (mpv=N2 upper bound).
        -- Mirrors `dump_side_loaded_main.ml`'s Simple_chain rule. Drives
        -- the byte-equality validation for β2 (one-hot wrap-domain
        -- lagrange mux), β3 (pseudo step-domain dispatch), and β4
        -- (max_proofs_verified runtime mask). The three per-domain
        -- lagrange tables are at log2 ∈ {13, 14, 15} — the wrap-domain
        -- log2s for `actual_wrap_domain_size ∈ {N0, N1, N2}` per
        -- `common.ml:25-29`. OCaml's side_loaded_domain (step_verifier.ml:817)
        -- muxes these via the runtime one-hot bits.
        let
          lagrangeAtD15 =
            mkConstLagrangeBaseLookup \i ->
              (coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 15 i)) :: AffinePoint (F Fp)
          sideLoadedMainSrsData =
            { lagrangeAt: lagrangeAtD14
            , sideloadedPerDomainLagrangeAt:
                ( \i ->
                    (coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 13 i)) :: AffinePoint (F Fp)
                )
                  :<
                    ( \i ->
                        (coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 14 i)) :: AffinePoint (F Fp)
                    )
                  :<
                    ( \i ->
                        (coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 15 i)) :: AffinePoint (F Fp)
                    )
                  :< Vector.nil
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepMainSrs) :: AffinePoint (F Fp)
            }
          _ = lagrangeAtD15 -- keep available in case the diff loop wants the LBL form
        -- N=1 parent + side-loaded prev. Current state: −63 Generic.
        -- PS labels in fixture output (`context` field) localize the
        -- deficit to `step6_ivp / ivp_xhat / public-input-commit`
        -- (rows 3993-4085) — PS `InCircuitCorrections` mode vs OCaml
        -- `public_input_commitment_dynamic` (step_verifier.ml:457-512)
        -- emit different specific R1CS Generic counts despite
        -- structurally equivalent math. CompleteAdd, VarBaseMul,
        -- EndoMul, Poseidon counts all match exactly. Sub-targets:
        -- step2_fop −64, step6_ivp −22, +23 PS-extra in misc labels
        -- (sponge_after_index, step8_assert_bp).
        --
        -- Pending until residual is closed.
        --
        -- To run the diff manually:
        --   `npx spago test -p pickles-circuit-diffs -- --example "side_loaded_main"`
        -- after switching `pending'` below back to `exactMatchEff`.
        exactMatchEff "step_main_side_loaded_main_circuit" (fromCompiledCircuit <$> compileStepMainSideLoadedMain sideLoadedMainSrsData)
        -- N=0, Input mode — side-loaded CHILD (No_recursion + dummy_constraints).
        -- The inner rule whose proof gets verified by the side-loaded
        -- parent in `dump_side_loaded_main.ml`. Full body translated:
        -- on-curve `g`, `toFieldChecked' @1`, `scaleFast1 @1 @5` ×2,
        -- `endo @4 @1`, then `Field.Assert.equal self Field.zero`.
        let
          sideLoadedChildSrsData =
            { blindingH: (coerce $ vestaSrsBlindingGenerator stepMainSrs) :: AffinePoint (F Fp)
            }
        exactMatchEff "step_main_side_loaded_child_circuit" (fromCompiledCircuit <$> compileStepMainSideLoadedChild sideLoadedChildSrsData)
        -- N=1 Input mode (`increment` branch of two_phase_chain).
        -- Step domain log2 = 14. Body asserts `self_v = prev + 1` (single
        -- R1CS) with `proofMustVerify = true_`. mpvMax=1, mpvPad=0.
        -- The OCaml fixture is one of TWO step CSes the
        -- `dump_two_phase_chain.exe` driver emits (step_0=make_zero,
        -- step_1=increment); both feed into the shared wrap CS via
        -- `choose_key`-style step VK dispatch.
        let
          twoPhaseChainIncrementSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                (coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 14 i)) :: AffinePoint (F Fp)
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepMainSrs) :: AffinePoint (F Fp)
            }
        exactMatchEff "step_main_two_phase_chain_increment_circuit"
          (fromCompiledCircuit <$> compileStepMainTwoPhaseChainIncrement twoPhaseChainIncrementSrsData)
        -- N=0 Input mode (`make_zero` branch of two_phase_chain). Rule
        -- has no prevs but the multi-branch wrap is mpv=N1, so the
        -- step PI is 34 entries (mpvPad=1 → 1 front-padded dummy slot).
        -- Step domain log2 = 9. Body asserts `self_v = 0` (single R1CS).
        let
          twoPhaseChainMakeZeroSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                (coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 14 i)) :: AffinePoint (F Fp)
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepMainSrs) :: AffinePoint (F Fp)
            }
        exactMatchEff "step_main_two_phase_chain_make_zero_circuit"
          (fromCompiledCircuit <$> compileStepMainTwoPhaseChainMakeZero twoPhaseChainMakeZeroSrsData)
      describe "Linearization" do
        exactMatch "linearization_step_circuit" (fromCompiledCircuit compileLinearizationStep)
        exactMatch "linearization_wrap_circuit" (fromCompiledCircuit compileLinearizationWrap)
      describe "Pseudo module" do
        exactMatch "utils_ones_vector_n16_step_circuit" (fromCompiledCircuit compileUtilsOnesVectorN16Step)
        exactMatch "utils_ones_vector_n16_wrap_circuit" (fromCompiledCircuit compileUtilsOnesVectorN16Wrap)
        exactMatch "one_hot_n1_step_circuit" (fromCompiledCircuit compileOneHotN1Step)
        exactMatch "one_hot_n1_wrap_circuit" (fromCompiledCircuit compileOneHotN1Wrap)
        exactMatch "one_hot_n17_step_circuit" (fromCompiledCircuit compileOneHotN17Step)
        exactMatch "one_hot_n17_wrap_circuit" (fromCompiledCircuit compileOneHotN17Wrap)
        exactMatch "one_hot_n3_step_circuit" (fromCompiledCircuit compileOneHotN3Step)
        exactMatch "one_hot_n3_wrap_circuit" (fromCompiledCircuit compileOneHotN3Wrap)
        exactMatch "pseudo_mask_n1_step_circuit" (fromCompiledCircuit compilePseudoMaskN1Step)
        exactMatch "pseudo_mask_n1_wrap_circuit" (fromCompiledCircuit compilePseudoMaskN1Wrap)
        exactMatch "pseudo_mask_n3_step_circuit" (fromCompiledCircuit compilePseudoMaskN3Step)
        exactMatch "pseudo_mask_n3_wrap_circuit" (fromCompiledCircuit compilePseudoMaskN3Wrap)
        exactMatch "pseudo_mask_n17_step_circuit" (fromCompiledCircuit compilePseudoMaskN17Step)
        exactMatch "pseudo_mask_n17_wrap_circuit" (fromCompiledCircuit compilePseudoMaskN17Wrap)
        exactMatch "pseudo_choose_n1_step_circuit" (fromCompiledCircuit compilePseudoChooseN1Step)
        exactMatch "pseudo_choose_n1_wrap_circuit" (fromCompiledCircuit compilePseudoChooseN1Wrap)
        exactMatch "pseudo_choose_n3_step_circuit" (fromCompiledCircuit compilePseudoChooseN3Step)
        exactMatch "pseudo_choose_n3_wrap_circuit" (fromCompiledCircuit compilePseudoChooseN3Wrap)
        exactMatch "choose_key_n1_wrap_circuit" (fromCompiledCircuit compileChooseKeyN1Wrap)
        exactMatch "sideloaded_vk_typ_step_circuit" (fromCompiledCircuit compileSideloadedVkTypStep)
