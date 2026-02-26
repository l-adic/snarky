module Test.Snarky.Circuit.Kimchi.CircuitJson (spec) where

import Prelude

import Data.Either (Either(..))
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Snarky.Backend.Compile (compilePure)
import Snarky.Backend.Kimchi.CircuitJson (CircuitData, circuitToJson, readCircuitJson)
import Snarky.Circuit.DSL (BoolVar, F, FVar, SizedF, all_, and_, any_, assertEqual_, assertNonZero_, assertNotEqual_, assertSquare_, assert_, const_, div_, equals_, exists, if_, inv_, mul_, or_, pow_, unpack_, xor_)
import Snarky.Circuit.DSL.Monad (class CircuitM, Snarky)
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Circuit.Kimchi.EndoMul (endo)
import Snarky.Circuit.Kimchi.EndoScalar (toField)
import Snarky.Circuit.Kimchi.Poseidon (poseidon)
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast1, scaleFast2')
import Snarky.Constraint.Kimchi (KimchiConstraint, initialState)
import Snarky.Curves.Class (class SerdeHex, EndoScalar(..), endoScalar)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (Type1(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

type Fp = Vesta.ScalarField

--------------------------------------------------------------------------------
-- File IO helpers (test-only, not in library code)

loadCircuits
  :: forall @f
   . SerdeHex f
  => String
  -> String
  -> Aff { ocaml :: CircuitData f, ps :: CircuitData f }
loadCircuits ocamlPath psJson = do
  ocamlJson <- liftEffect do
    buf <- FS.readFile ocamlPath
    Buffer.toString UTF8 buf
  let
    ocamlCircuit :: Either _ (CircuitData f)
    ocamlCircuit = readCircuitJson ocamlJson

    psCircuit :: Either _ (CircuitData f)
    psCircuit = readCircuitJson psJson
  case ocamlCircuit, psCircuit of
    Right oc, Right ps -> pure { ocaml: oc, ps }
    Left e, _ -> liftEffect $ throw $ "Failed to parse OCaml JSON: " <> show e
    _, Left e -> liftEffect $ throw $ "Failed to parse PureScript JSON: " <> show e

fixtureDir :: String
fixtureDir = "packages/snarky-kimchi/test/fixtures/"

exactMatch :: String -> String -> Spec Unit
exactMatch name psJson =
  it (name <> " matches OCaml exactly") do
    c <- loadCircuits @Fp (fixtureDir <> name <> ".json") psJson
    c.ps.publicInputSize `shouldEqual` c.ocaml.publicInputSize
    c.ps.gates `shouldEqual` c.ocaml.gates

--------------------------------------------------------------------------------
-- Field arithmetic circuits (input: field, output: field)

compileFF
  :: (forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m (FVar Fp))
  -> String
compileFF circuit = circuitToJson @Fp $
  compilePure (Proxy @(F Fp)) (Proxy @(F Fp)) (Proxy @(KimchiConstraint Fp)) circuit initialState

compileFB
  :: (forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m (BoolVar Fp))
  -> String
compileFB circuit = circuitToJson @Fp $
  compilePure (Proxy @(F Fp)) (Proxy @Boolean) (Proxy @(KimchiConstraint Fp)) circuit initialState

compileFU
  :: (forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m Unit)
  -> String
compileFU circuit = circuitToJson @Fp $
  compilePure (Proxy @(F Fp)) (Proxy @Unit) (Proxy @(KimchiConstraint Fp)) circuit initialState

compileBB
  :: (forall c t m. CircuitM Fp c t m => BoolVar Fp -> Snarky c t m (BoolVar Fp))
  -> String
compileBB circuit = circuitToJson @Fp $
  compilePure (Proxy @Boolean) (Proxy @Boolean) (Proxy @(KimchiConstraint Fp)) circuit initialState

compileBU
  :: (forall c t m. CircuitM Fp c t m => BoolVar Fp -> Snarky c t m Unit)
  -> String
compileBU circuit = circuitToJson @Fp $
  compilePure (Proxy @Boolean) (Proxy @Unit) (Proxy @(KimchiConstraint Fp)) circuit initialState

--------------------------------------------------------------------------------
-- Kimchi gate compile helpers

type TwoPoints = Tuple (AffinePoint (F Fp)) (AffinePoint (F Fp))

type Point = AffinePoint (F Fp)

compilePP
  :: ( forall t m
        . CircuitM Fp (KimchiConstraint Fp) t m
       => Tuple (AffinePoint (FVar Fp)) (AffinePoint (FVar Fp))
       -> Snarky (KimchiConstraint Fp) t m (AffinePoint (FVar Fp))
     )
  -> String
compilePP circuit = circuitToJson @Fp $
  compilePure (Proxy @TwoPoints) (Proxy @Point) (Proxy @(KimchiConstraint Fp)) circuit initialState

type PointField = Tuple (AffinePoint (F Fp)) (F Fp)

compilePF
  :: ( forall t m
        . CircuitM Fp (KimchiConstraint Fp) t m
       => Tuple (AffinePoint (FVar Fp)) (FVar Fp)
       -> Snarky (KimchiConstraint Fp) t m (AffinePoint (FVar Fp))
     )
  -> String
compilePF circuit = circuitToJson @Fp $
  compilePure (Proxy @PointField) (Proxy @Point) (Proxy @(KimchiConstraint Fp)) circuit initialState

compileKFF
  :: ( forall t m
        . CircuitM Fp (KimchiConstraint Fp) t m
       => FVar Fp
       -> Snarky (KimchiConstraint Fp) t m (FVar Fp)
     )
  -> String
compileKFF circuit = circuitToJson @Fp $
  compilePure (Proxy @(F Fp)) (Proxy @(F Fp)) (Proxy @(KimchiConstraint Fp)) circuit initialState

type V3 = Vector 3 (F Fp)

compileV3
  :: ( forall t m
        . CircuitM Fp (KimchiConstraint Fp) t m
       => Vector 3 (FVar Fp)
       -> Snarky (KimchiConstraint Fp) t m (Vector 3 (FVar Fp))
     )
  -> String
compileV3 circuit = circuitToJson @Fp $
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
  _.p <$> addComplete p1 p2

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
-- Test spec

spec :: Spec Unit
spec =
  describe "CircuitJson comparison" do
    describe "Exact matches" do
      exactMatch "mul_circuit" (compileFF mulCircuit)
      exactMatch "inv_circuit" (compileFF invCircuit)
      exactMatch "assert_equal_circuit" (compileFU assertEqualCircuit)
      exactMatch "assert_non_zero_circuit" (compileFU assertNonZeroCircuit)
      exactMatch "div_circuit" (compileFF divCircuit)
      exactMatch "equals_circuit" (compileFB equalsCircuit)
      exactMatch "if_circuit" (compileFF ifCircuit)
      exactMatch "assert_not_equal_circuit" (compileFU assertNotEqualCircuit)
      exactMatch "bool_and_circuit" (compileBB boolAndCircuit)
      exactMatch "bool_or_circuit" (compileBB boolOrCircuit)
      exactMatch "bool_assert_circuit" (compileBU boolAssertCircuit)
      exactMatch "bool_xor_circuit" (compileBB boolXorCircuit)
      exactMatch "bool_all_circuit" (compileBB boolAllCircuit)
      exactMatch "bool_any_circuit" (compileBB boolAnyCircuit)
      exactMatch "assert_square_circuit" (compileFU assertSquareCircuit)
      exactMatch "unpack_circuit" (compileFU unpackCircuit)
      exactMatch "pow7_circuit" (compileFF pow7Circuit)
      exactMatch "pow8_circuit" (compileFF pow8Circuit)
    describe "Kimchi gate matches" do
      exactMatch "add_complete_circuit" (compilePP addCompleteCircuit)
      exactMatch "endo_scalar_circuit" (compileKFF endoScalarCircuit)
      exactMatch "var_base_mul_circuit" (compilePF varBaseMulCircuit)
      exactMatch "endo_mul_circuit" (compilePF endoMulCircuit)
      exactMatch "poseidon_circuit" (compileV3 poseidonCircuit)
      exactMatch "scale_fast2_128_circuit" (compilePF scaleFast2_128Circuit)
