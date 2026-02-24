module Test.Snarky.Circuit.Kimchi.VarBaseMul where

import Prelude

import Control.Monad.Error.Class (try)
import Data.Array.NonEmpty as NEA
import Data.Either (Either(..))
import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.String as String
import Data.Tuple (Tuple(..), uncurry)
import Effect.Class (liftEffect)
import Effect.Exception (message)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, Snarky)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Circuit.Kimchi.VarBaseMul (joinField, scaleFast1, scaleFast2, scaleFast2', splitField)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint, KimchiGate, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (class PrimeField, fromAffine, fromBigInt, scalarMul, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.EllipticCurve as EC
import Snarky.Types.Shifted (Type1(..), Type2(..), fieldSizeBits, forbiddenType1Values, forbiddenType2Values, fromShifted, toShifted)
import Test.QuickCheck (Result, arbitrary, (===))
import Test.QuickCheck.Gen (Gen, elements)
import Test.Snarky.Circuit.Utils (Expectation, TestConfig, circuitTest', circuitTestM', satisfied, unsatisfied)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail)
import Test.Spec.QuickCheck (quickCheck)
import Type.Proxy (Proxy(..))

kimchiTestConfig :: forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)
kimchiTestConfig = { checker: eval, postCondition: Kimchi.postCondition, initState: Kimchi.initialState }

spec :: Spec Unit
spec = do
  describe "splitField / joinField" do
    it "roundtrips in Vesta.BaseField" $
      quickCheck (splitJoinRoundtrip @Vesta.BaseField)
    it "roundtrips in Vesta.ScalarField" $
      quickCheck (splitJoinRoundtrip @Vesta.ScalarField)

  -- Type1: Vesta circuit (field = Vesta.BaseField)
  -- Uses Vesta.G curve (coordinates in Vesta.BaseField = circuit field)
  -- Scalars are in Vesta.ScalarField (smaller than circuit field)
  describe "VarBaseMul Type1 (Vesta circuit)" do
    it "varBaseMul Circuit is Valid for Type1" $ unsafePartial do
      let
        f :: Tuple (AffinePoint (F Vesta.BaseField)) (Type1 (F Vesta.BaseField)) -> AffinePoint (F Vesta.BaseField)
        f (Tuple { x: F x, y: F y } scalar_) =
          let
            base = fromAffine @Vesta.BaseField @Vesta.G { x, y }
            scalar = case fromShifted scalar_ of F a -> a
            result = scalarMul scalar base
            { x: x', y: y' } = unsafePartial $ fromJust $ toAffine @Vesta.BaseField result
          in
            { x: F x', y: F y' }

        circuit1
          :: forall t
           . CircuitM Vesta.BaseField (KimchiConstraint Vesta.BaseField) t Identity
          => Tuple (AffinePoint (FVar Vesta.BaseField)) (Type1 (FVar Vesta.BaseField))
          -> Snarky (KimchiConstraint Vesta.BaseField) t Identity (AffinePoint (FVar Vesta.BaseField))
        circuit1 = uncurry \p t -> do
          g <- scaleFast1 @51 p t
          pure g

        gen :: Gen (Tuple (AffinePoint (F Vesta.BaseField)) (Type1 (F Vesta.BaseField)))
        gen = do
          p <- EC.genAffinePoint (Proxy @Vesta.G)
          -- Generate the shifted value directly in the circuit field
          -- (don't go through toShifted which crosses fields)
          t <- arbitrary @(F Vesta.ScalarField)
          pure $ Tuple p (toShifted t)

      { builtState, solver } <- circuitTest' @Vesta.BaseField 100
        kimchiTestConfig
        ( NEA.singleton
            { testFunction: satisfied f
            , gen
            }
        )
        circuit1
      liftEffect $ verifyCircuit { s: builtState, gen, solver }

    it "rejects forbidden Type1 values" $ unsafePartial do
      let
        circuit1
          :: forall t
           . CircuitM Vesta.BaseField (KimchiConstraint Vesta.BaseField) t Identity
          => Tuple (AffinePoint (FVar Vesta.BaseField)) (Type1 (FVar Vesta.BaseField))
          -> Snarky (KimchiConstraint Vesta.BaseField) t Identity (AffinePoint (FVar Vesta.BaseField))
        circuit1 = uncurry \p t -> do
          g <- scaleFast1 @51 p t
          pure g

        -- Generator that picks from forbidden values
        genForbidden :: Gen (Tuple (AffinePoint (F Vesta.BaseField)) (Type1 (F Vesta.BaseField)))
        genForbidden = do
          p <- EC.genAffinePoint (Proxy @Vesta.G)
          forbiddenVal <- elements (fromJust $ NEA.fromArray forbiddenType1Values)
          pure $ Tuple p (Type1 forbiddenVal)

      void $ circuitTest' @Vesta.BaseField 10
        kimchiTestConfig
        ( NEA.singleton
            { testFunction: (unsatisfied :: _ -> Expectation (AffinePoint (F Vesta.BaseField)))
            , gen: genForbidden
            }
        )
        circuit1

  -- Type2: Pallas circuit, scalar field (Pallas.ScalarField) is LARGER than circuit field (Pallas.BaseField)
  describe "VarBaseMul Type2 (Pallas circuit)" do
    it "varBaseMul Circuit is Valid for Type2" $ unsafePartial do
      let
        f :: Tuple (AffinePoint (F Pallas.BaseField)) (Type2 (F Pallas.BaseField) Boolean) -> AffinePoint (F Pallas.BaseField)
        f (Tuple { x: F x, y: F y } scalar_) =
          let
            base = fromAffine @Pallas.BaseField @Pallas.G { x, y }

            scalar :: Pallas.ScalarField
            scalar = case fromShifted scalar_ of F a -> a
            result = scalarMul scalar base
            { x: x', y: y' } = unsafePartial $ fromJust $ toAffine @Pallas.BaseField result
          in
            { x: F x', y: F y' }

        circuit2
          :: forall t
           . CircuitM Pallas.BaseField (KimchiConstraint Pallas.BaseField) t Identity
          => Tuple (AffinePoint (FVar Pallas.BaseField)) (Type2 (FVar Pallas.BaseField) (BoolVar Pallas.BaseField))
          -> Snarky (KimchiConstraint Pallas.BaseField) t Identity (AffinePoint (FVar Pallas.BaseField))
        circuit2 = uncurry \p t -> scaleFast2 @51 @254 p t

        gen :: Gen (Tuple (AffinePoint (F Pallas.BaseField)) (Type2 (F Pallas.BaseField) Boolean))
        gen = do
          p <- EC.genAffinePoint (Proxy @Pallas.G)
          circuitVal <- arbitrary @(F Pallas.ScalarField)
          pure $ Tuple p (toShifted circuitVal)

      { builtState, solver } <- circuitTest' @Pallas.BaseField 100
        kimchiTestConfig
        ( NEA.singleton
            { testFunction: satisfied f
            , gen
            }
        )
        circuit2
      liftEffect $ verifyCircuit { s: builtState, gen, solver }

    -- Forbidden Type2 values cause "Division by zero" in the Rust FFI during scalar multiplication
    -- (the forbidden value check constraints are added but the FFI computation fails first)
    it "rejects forbidden Type2 values" $ unsafePartial do
      let
        circuit2M
          :: forall t m
           . CircuitM Pallas.BaseField (KimchiConstraint Pallas.BaseField) t m
          => Tuple (AffinePoint (FVar Pallas.BaseField)) (Type2 (FVar Pallas.BaseField) (BoolVar Pallas.BaseField))
          -> Snarky (KimchiConstraint Pallas.BaseField) t m (AffinePoint (FVar Pallas.BaseField))
        circuit2M = uncurry \p t -> scaleFast2 @51 @254 p t

        -- Generator that picks from forbidden values
        genForbidden :: Gen (Tuple (AffinePoint (F Pallas.BaseField)) (Type2 (F Pallas.BaseField) Boolean))
        genForbidden = do
          p <- EC.genAffinePoint (Proxy @Pallas.G)
          { sDiv2, sOdd } <- elements (fromJust $ NEA.fromArray forbiddenType2Values)
          pure $ Tuple p (Type2 { sDiv2, sOdd })

      -- Run in Effect to catch JS FFI exception as test failure
      try
        ( circuitTestM' @Pallas.BaseField 10 identity
            kimchiTestConfig
            ( NEA.singleton
                { testFunction: (unsatisfied :: _ -> Expectation (AffinePoint (F Pallas.BaseField)))
                , gen: genForbidden
                }
            )
            circuit2M
        ) >>= case _ of
        Left err | String.contains (String.Pattern "Division by zero") (message err) -> pure unit
        Left err -> fail $ "Unexpected error: " <> message err
        Right _ -> fail "Expected Division by zero error but test passed"

  -- scaleFast2': takes a raw field element, splits it, then computes [s + 2^n] * base
  describe "VarBaseMul scaleFast2' (Pallas circuit)" do
    it "scaleFast2' circuit matches [s + 2^n] * base" $ unsafePartial do
      let
        -- Pure function: [s + 2^n] * base
        f :: Tuple (AffinePoint (F Pallas.BaseField)) (F Pallas.BaseField) -> AffinePoint (F Pallas.BaseField)
        f (Tuple { x: F x, y: F y } (F sVal)) =
          let
            base = fromAffine @Pallas.BaseField @Pallas.G { x, y }
            -- Convert base field element to scalar field with 2^n shift
            n = fieldSizeBits (Proxy @Pallas.BaseField)
            sBigInt = toBigInt sVal
            twoToN = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)

            scalar :: Pallas.ScalarField
            scalar = fromBigInt (sBigInt + twoToN)
            result = scalarMul scalar base
            { x: x', y: y' } = unsafePartial $ fromJust $ toAffine @Pallas.BaseField result
          in
            { x: F x', y: F y' }

        circuit3
          :: forall t
           . CircuitM Pallas.BaseField (KimchiConstraint Pallas.BaseField) t Identity
          => Tuple (AffinePoint (FVar Pallas.BaseField)) (FVar Pallas.BaseField)
          -> Snarky (KimchiConstraint Pallas.BaseField) t Identity (AffinePoint (FVar Pallas.BaseField))
        circuit3 = uncurry \p scalar -> scaleFast2' @51 @254 p scalar

        gen :: Gen (Tuple (AffinePoint (F Pallas.BaseField)) (F Pallas.BaseField))
        gen = do
          p <- EC.genAffinePoint (Proxy @Pallas.G)
          scalar <- arbitrary @(F Pallas.BaseField)
          pure $ Tuple p scalar

      { builtState, solver } <- circuitTest' @Pallas.BaseField 100
        kimchiTestConfig
        ( NEA.singleton
            { testFunction: satisfied f
            , gen
            }
        )
        circuit3
      liftEffect $ verifyCircuit { s: builtState, gen, solver }

--------------------------------------------------------------------------------
-- splitField / joinField roundtrip (within same field)
--------------------------------------------------------------------------------

splitJoinRoundtrip :: forall @f. PrimeField f => F f -> Result
splitJoinRoundtrip x =
  let
    { sDiv2: F d, sOdd } = splitField x
    reconstructed = F (joinField { sDiv2: d, sOdd })
  in
    reconstructed === x
