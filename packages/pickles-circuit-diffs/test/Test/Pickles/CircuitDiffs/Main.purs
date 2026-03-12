module Test.Pickles.CircuitDiffs.Main where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Pickles.CircuitDiffs.Circuit (Circuit, fromCompiledCircuit, parseCachedConstants, parseCircuitJson)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (BoolVar, F, FVar, SizedF, all_, and_, any_, assertEqual_, assertNonZero_, assertNotEqual_, assertSquare_, assert_, const_, div_, equals_, exists, if_, inv_, mul_, or_, pow_, unpack_, xor_)
import Snarky.Circuit.DSL.Monad (class CircuitM, Snarky)
import Snarky.Circuit.Kimchi.AddComplete (Finiteness(..), addFast)
import Snarky.Circuit.Kimchi.EndoMul (endo)
import Snarky.Circuit.Kimchi.EndoScalar (toField)
import Snarky.Circuit.Kimchi.Poseidon (poseidon)
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast1, scaleFast2')
import Snarky.Constraint.Kimchi (KimchiConstraint, initialState)
import Snarky.Constraint.Kimchi.Types (GateKind)
import Snarky.Curves.Class (EndoScalar(..), endoScalar)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (Type1(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

type Fp = Vesta.ScalarField

fixtureDir :: String
fixtureDir = "packages/snarky-kimchi/test/fixtures/"

readFixture :: String -> Effect String
readFixture path = do
  buf <- FS.readFile path
  Buffer.toString UTF8 buf

-- | The parts of a circuit that are comparable between OCaml fixtures and PureScript.
-- | OCaml fixtures don't have variables or context, so we strip those.
type ComparableGate f =
  { kind :: GateKind
  , wires :: Array { row :: Int, col :: Int }
  , coeffs :: Array f
  }

type ComparableCircuit f =
  { publicInputSize :: Int
  , gates :: Array (ComparableGate f)
  , cachedConstants :: Array f
  }

comparable :: forall f. Ord f => Circuit f -> ComparableCircuit f
comparable c =
  { publicInputSize: c.publicInputSize
  , gates: map (\g -> { kind: g.kind, wires: g.wires, coeffs: g.coeffs }) c.gates
  , cachedConstants: Array.sort $ map _.value c.cachedConstants
  }

--------------------------------------------------------------------------------
-- Compile helpers

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

loadOcamlCircuit :: String -> Effect (Circuit Fp)
loadOcamlCircuit name = do
  circuitJson <- readFixture (fixtureDir <> name <> ".json")
  cachedJson <- readFixture (fixtureDir <> name <> "_cached_constants.json")
  case parseCircuitJson circuitJson, parseCachedConstants cachedJson of
    Right { publicInputSize, gates }, Right cachedConstants ->
      pure { publicInputSize, gates, cachedConstants }
    Left e, _ -> throw $ "Failed to parse circuit JSON: " <> show e
    _, Left e -> throw $ "Failed to parse cached constants: " <> show e

exactMatch :: String -> Circuit Fp -> Spec Unit
exactMatch name ps =
  it (name <> " matches OCaml") do
    ocaml <- liftEffect $ loadOcamlCircuit name
    comparable ps `shouldEqual` comparable ocaml

--------------------------------------------------------------------------------
-- Test spec

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] spec

spec :: Spec Unit
spec =
  describe "Circuit comparison" do
    describe "Field arithmetic" do
      exactMatch "mul_circuit" (compileFF mulCircuit)
      exactMatch "inv_circuit" (compileFF invCircuit)
      exactMatch "div_circuit" (compileFF divCircuit)
      exactMatch "if_circuit" (compileFF ifCircuit)
      exactMatch "equals_circuit" (compileFB equalsCircuit)
      exactMatch "pow7_circuit" (compileFF pow7Circuit)
      exactMatch "pow8_circuit" (compileFF pow8Circuit)
    describe "Assertions" do
      exactMatch "assert_equal_circuit" (compileFU assertEqualCircuit)
      exactMatch "assert_non_zero_circuit" (compileFU assertNonZeroCircuit)
      exactMatch "assert_not_equal_circuit" (compileFU assertNotEqualCircuit)
      exactMatch "assert_square_circuit" (compileFU assertSquareCircuit)
      exactMatch "unpack_circuit" (compileFU unpackCircuit)
    describe "Boolean" do
      exactMatch "bool_and_circuit" (compileBB boolAndCircuit)
      exactMatch "bool_or_circuit" (compileBB boolOrCircuit)
      exactMatch "bool_xor_circuit" (compileBB boolXorCircuit)
      exactMatch "bool_all_circuit" (compileBB boolAllCircuit)
      exactMatch "bool_any_circuit" (compileBB boolAnyCircuit)
      exactMatch "bool_assert_circuit" (compileBU boolAssertCircuit)
    describe "Kimchi gates" do
      exactMatch "add_complete_circuit" (compilePP addCompleteCircuit)
      exactMatch "endo_scalar_circuit" (compileKFF endoScalarCircuit)
      exactMatch "var_base_mul_circuit" (compilePF varBaseMulCircuit)
      exactMatch "endo_mul_circuit" (compilePF endoMulCircuit)
      exactMatch "scale_fast2_128_circuit" (compilePF scaleFast2_128Circuit)
      exactMatch "poseidon_circuit" (compileV3 poseidonCircuit)
