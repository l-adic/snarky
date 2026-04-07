module Test.Pickles.CircuitDiffs.Main where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
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
import Pickles.CircuitDiffs.PureScript.ChallengeDigest (compileChallengeDigest)
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
import Pickles.CircuitDiffs.PureScript.IvpWrap (compileIvpWrap)
import Pickles.CircuitDiffs.PureScript.LinearizationStep (compileLinearizationStep)
import Pickles.CircuitDiffs.PureScript.LinearizationWrap (compileLinearizationWrap)
import Pickles.CircuitDiffs.PureScript.Pow2Pow (compilePow2Pow)
import Pickles.CircuitDiffs.PureScript.PseudoCircuits (compileChooseKeyN1Wrap, compileOneHotN1Step, compileOneHotN1Wrap, compileOneHotN3Step, compileOneHotN3Wrap, compilePseudoChooseN1Step, compilePseudoChooseN1Wrap, compilePseudoChooseN3Step, compilePseudoChooseN3Wrap, compilePseudoMaskN1Step, compilePseudoMaskN1Wrap, compilePseudoMaskN3Step, compilePseudoMaskN3Wrap)
import Pickles.CircuitDiffs.PureScript.StepVerify (compileStepVerify)
import Pickles.CircuitDiffs.PureScript.OtherFieldCheck (compileOtherFieldCheck)
import Pickles.CircuitDiffs.PureScript.StepMainSimpleChain (compileStepMainSimpleChain)
import Pickles.CircuitDiffs.PureScript.StepVerifyN2 (compileStepVerifyN2)
import Pickles.CircuitDiffs.PureScript.WrapMain (compileWrapMainN1)
import Pickles.CircuitDiffs.PureScript.WrapMainN2 (compileWrapMainN2)
import Pickles.CircuitDiffs.PureScript.WrapVerify (compileWrapVerify)
import Pickles.CircuitDiffs.PureScript.WrapVerifyN2 (compileWrapVerifyN2)
import Pickles.CircuitDiffs.PureScript.Xhat (compileXhat)
import Pickles.CircuitDiffs.PureScript.XhatStep (compileXhatStep)
import Pickles.CircuitDiffs.Types (CircuitComparison)
import Pickles.PublicInputCommit (mkConstLagrangeBase)
import Safe.Coerce (coerce)
import Simple.JSON (writeJSON)
import Snarky.Backend.Compile (compilePure)
import Snarky.Backend.Kimchi.Impl.Pallas (pallasCrsCreate)
import Snarky.Backend.Kimchi.Impl.Vesta (vestaCrsCreate)
import Snarky.Backend.Kimchi.Types (CRS)
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
import Test.DummyFixture as DummyFixture
import Test.Spec (SpecT, beforeAll_, describe, it)
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
  endo g (unsafeCoerce scalar :: SizedF 128 (FVar Fp))

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
exactMatch name ps =
  it (name <> " matches OCaml") do
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
        exactMatch "challenge_digest_step_circuit" (fromCompiledCircuit compileChallengeDigest)
        exactMatch "hash_messages_for_next_step_proof_circuit" (fromCompiledCircuit compileHashMessagesStep)
        exactMatch "finalize_other_proof_step_circuit" (fromCompiledCircuit compileFopStep)
        exactMatch "group_map_step_circuit" (fromCompiledCircuit compileGroupMapStep)
        exactMatch "bullet_reduce_one_step_circuit" (fromCompiledCircuit compileBulletReduceOneStep)
        exactMatch "bullet_reduce_step_circuit" (fromCompiledCircuit compileBulletReduceStep)
        exactMatch "ftcomm_step_circuit" (fromCompiledCircuit compileFtcommStep)
        let
          stepSrs = pallasCrsCreate (2 `Int.pow` 16)
          stepSrsData =
            { lagrangeComms: map mkConstLagrangeBase ((coerce $ vestaSrsLagrangeCommitments stepSrs 16 30) :: Array (AffinePoint (F Fp)))
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
            { lagrangeComms: map mkConstLagrangeBase (coerce $ pallasSrsLagrangeCommitments srs 16 177)
            , blindingH: coerce $ pallasSrsBlindingGenerator srs
            }
        exactMatch "xhat_wrap_circuit" (fromCompiledCircuit $ compileXhat wrapSrsData)
      describe "IVP" do
        let
          wrapSrs = vestaCrsCreate (2 `Int.pow` 16)
          wrapSrsData =
            { lagrangeComms: map mkConstLagrangeBase (coerce $ pallasSrsLagrangeCommitments wrapSrs 16 177)
            , blindingH: coerce $ pallasSrsBlindingGenerator wrapSrs
            }
        exactMatch "ivp_wrap_circuit" (fromCompiledCircuit $ compileIvpWrap wrapSrsData)
        exactMatch "wrap_verify_circuit" (fromCompiledCircuit $ compileWrapVerify wrapSrsData)
        exactMatch "wrap_verify_n2_circuit" (fromCompiledCircuit $ compileWrapVerifyN2 wrapSrsData)
        exactMatch "wrap_main_circuit" (fromCompiledCircuit $ compileWrapMainN1 wrapSrsData)
        exactMatch "wrap_main_n2_circuit" (fromCompiledCircuit $ compileWrapMainN2 wrapSrsData)
        let
          -- OCaml uses SRS.Fq.create (1 lsl 15) and domain Pow_2_roots_of_unity 15
          stepSrs = pallasCrsCreate (2 `Int.pow` 15)
          stepSrsData =
            { lagrangeComms: map mkConstLagrangeBase ((coerce $ vestaSrsLagrangeCommitments stepSrs 15 175) :: Array (AffinePoint (F Fp)))
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepSrs) :: AffinePoint (F Fp)
            }
        exactMatch "ivp_step_circuit" (fromCompiledCircuit $ compileIvpStep stepSrsData)
      describe "Step verify" do
        let
          -- Same SRS as IVP step: OCaml uses SRS.Fq.create (1 lsl 15) and domain 15
          stepVerifySrs = pallasCrsCreate (2 `Int.pow` 15)
          stepVerifySrsData =
            { lagrangeComms: map mkConstLagrangeBase ((coerce $ vestaSrsLagrangeCommitments stepVerifySrs 15 268) :: Array (AffinePoint (F Fp)))
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepVerifySrs) :: AffinePoint (F Fp)
            }
        exactMatch "step_verify_circuit" (fromCompiledCircuit $ compileStepVerify stepVerifySrsData)
        let
          stepVerifyN2SrsData =
            { lagrangeComms: map mkConstLagrangeBase ((coerce $ vestaSrsLagrangeCommitments stepVerifySrs 15 304) :: Array (AffinePoint (F Fp)))
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepVerifySrs) :: AffinePoint (F Fp)
            }
        exactMatch "step_verify_n2_circuit" (fromCompiledCircuit $ compileStepVerifyN2 stepVerifyN2SrsData)
      describe "Full step verify_one" do
        let
          fullStepSrs = pallasCrsCreate (2 `Int.pow` 15)
          fullStepSrsData =
            { lagrangeComms: map mkConstLagrangeBase ((coerce $ vestaSrsLagrangeCommitments fullStepSrs 14 286) :: Array (AffinePoint (F Fp)))
            , blindingH: (coerce $ vestaSrsBlindingGenerator fullStepSrs) :: AffinePoint (F Fp)
            }
        exactMatch "full_step_verify_one_circuit" (fromCompiledCircuit $ compileFullStepVerifyOne fullStepSrsData)
        let
          fullStepN2SrsData =
            { lagrangeComms: map mkConstLagrangeBase ((coerce $ vestaSrsLagrangeCommitments fullStepSrs 14 304) :: Array (AffinePoint (F Fp)))
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
            { lagrangeComms: map mkConstLagrangeBase ((coerce $ vestaSrsLagrangeCommitments stepMainSrs 14 286) :: Array (AffinePoint (F Fp)))
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepMainSrs) :: AffinePoint (F Fp)
            }
        exactMatch "step_main_simple_chain_circuit" (fromCompiledCircuit $ compileStepMainSimpleChain stepMainSrsData)
      describe "Linearization" do
        exactMatch "linearization_step_circuit" (fromCompiledCircuit compileLinearizationStep)
        exactMatch "linearization_wrap_circuit" (fromCompiledCircuit compileLinearizationWrap)
      describe "Pseudo module" do
        exactMatch "one_hot_n1_step_circuit" (fromCompiledCircuit compileOneHotN1Step)
        exactMatch "one_hot_n1_wrap_circuit" (fromCompiledCircuit compileOneHotN1Wrap)
        exactMatch "one_hot_n3_step_circuit" (fromCompiledCircuit compileOneHotN3Step)
        exactMatch "one_hot_n3_wrap_circuit" (fromCompiledCircuit compileOneHotN3Wrap)
        exactMatch "pseudo_mask_n1_step_circuit" (fromCompiledCircuit compilePseudoMaskN1Step)
        exactMatch "pseudo_mask_n1_wrap_circuit" (fromCompiledCircuit compilePseudoMaskN1Wrap)
        exactMatch "pseudo_mask_n3_step_circuit" (fromCompiledCircuit compilePseudoMaskN3Step)
        exactMatch "pseudo_mask_n3_wrap_circuit" (fromCompiledCircuit compilePseudoMaskN3Wrap)
        exactMatch "pseudo_choose_n1_step_circuit" (fromCompiledCircuit compilePseudoChooseN1Step)
        exactMatch "pseudo_choose_n1_wrap_circuit" (fromCompiledCircuit compilePseudoChooseN1Wrap)
        exactMatch "pseudo_choose_n3_step_circuit" (fromCompiledCircuit compilePseudoChooseN3Step)
        exactMatch "pseudo_choose_n3_wrap_circuit" (fromCompiledCircuit compilePseudoChooseN3Wrap)
        exactMatch "choose_key_n1_wrap_circuit" (fromCompiledCircuit compileChooseKeyN1Wrap)
      DummyFixture.spec
