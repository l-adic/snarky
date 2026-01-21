module Test.Pickles.ScalarChallenge where

import Prelude

import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import JS.BigInt as BigInt
import Pickles.ScalarChallenge (Challenge(..), ScalarChallenge(..), lowest128Bits, lowest128BitsConstant, squeezeChallenge, squeezeChallengePure, squeezeScalar, squeezeScalarPure)
import RandomOracle.Sponge as Sponge
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (Snarky)
import Snarky.Circuit.DSL.Monad (class CircuitM)
import Snarky.Circuit.RandomOracle.Sponge as CircuitSponge
import Snarky.Circuit.Types (F(..), FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (Result(..), arbitrary, (===))
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy)
import Test.Spec.QuickCheck (quickCheck)
import Type.Proxy (Proxy(..))

-- | Maximum value for 128 bits: 2^128 - 1
max128Bits :: BigInt.BigInt
max128Bits = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 128) - BigInt.fromInt 1

-- | Check if a BigInt value fits in 128 bits
fitsIn128Bits :: BigInt.BigInt -> Boolean
fitsIn128Bits bi = bi >= BigInt.fromInt 0 && bi <= max128Bits

-- | Create a test sponge state for Pallas
testStatePallas :: Vector 3 Pallas.BaseField
testStatePallas = one :< (one + one) :< (one + one + one) :< Vector.nil

-- | Create a test sponge state for Vesta
testStateVesta :: Vector 3 Vesta.BaseField
testStateVesta = one :< (one + one) :< (one + one + one) :< Vector.nil

spec :: Spec Unit
spec = do
  describe "Pickles.ScalarChallenge" do
    describe "lowest128BitsConstant" do
      it "returns value that fits in 128 bits (Pallas)" $
        quickCheck propLowest128BitsFitsPallas
      it "returns value that fits in 128 bits (Vesta)" $
        quickCheck propLowest128BitsFitsVesta
      it "is idempotent for small values (Pallas)" $
        quickCheck propIdempotentSmallPallas
      it "is idempotent for small values (Vesta)" $
        quickCheck propIdempotentSmallVesta

    describe "squeezeChallengePure" do
      it "produces deterministic output (Pallas)" do
        let
          sponge = Sponge.create testStatePallas
          { result: Challenge r1 } = squeezeChallengePure sponge
          { result: Challenge r2 } = squeezeChallengePure sponge
        r1 `shouldEqual` r2

      it "produces deterministic output (Vesta)" do
        let
          sponge = Sponge.create testStateVesta
          { result: Challenge r1 } = squeezeChallengePure sponge
          { result: Challenge r2 } = squeezeChallengePure sponge
        r1 `shouldEqual` r2

      it "produces value in 128-bit range (Pallas)" do
        let
          sponge = Sponge.create testStatePallas
          { result: Challenge result } = squeezeChallengePure sponge
        toBigInt result `shouldSatisfy` fitsIn128Bits

      it "produces value in 128-bit range (Vesta)" do
        let
          sponge = Sponge.create testStateVesta
          { result: Challenge result } = squeezeChallengePure sponge
        toBigInt result `shouldSatisfy` fitsIn128Bits

    describe "squeezeScalarPure" do
      it "produces deterministic output (Pallas)" do
        let
          sponge = Sponge.create testStatePallas
          { result: ScalarChallenge r1 } = squeezeScalarPure sponge
          { result: ScalarChallenge r2 } = squeezeScalarPure sponge
        r1 `shouldEqual` r2

      it "produces deterministic output (Vesta)" do
        let
          sponge = Sponge.create testStateVesta
          { result: ScalarChallenge r1 } = squeezeScalarPure sponge
          { result: ScalarChallenge r2 } = squeezeScalarPure sponge
        r1 `shouldEqual` r2

    describe "Circuit versions match pure (Pallas)" do
      it "lowest128Bits matches lowest128BitsConstant" $
        circuitLowest128BitsTest (Proxy :: Proxy Pallas.BaseField)
      it "squeezeChallenge matches squeezeChallengePure" $
        circuitSqueezeChallengeTest (Proxy :: Proxy Pallas.BaseField)
      it "squeezeScalar matches squeezeScalarPure" $
        circuitSqueezeScalarTest (Proxy :: Proxy Pallas.BaseField)

    describe "Circuit versions match pure (Vesta)" do
      it "lowest128Bits matches lowest128BitsConstant" $
        circuitLowest128BitsTest (Proxy :: Proxy Vesta.BaseField)
      it "squeezeChallenge matches squeezeChallengePure" $
        circuitSqueezeChallengeTest (Proxy :: Proxy Vesta.BaseField)
      it "squeezeScalar matches squeezeScalarPure" $
        circuitSqueezeScalarTest (Proxy :: Proxy Vesta.BaseField)

-- | Property: lowest128BitsConstant returns a value that fits in 128 bits (Pallas)
propLowest128BitsFitsPallas :: Pallas.ScalarField -> Result
propLowest128BitsFitsPallas x =
  let
    result = lowest128BitsConstant x
    resultBigInt = toBigInt result
  in
    if fitsIn128Bits resultBigInt then Success
    else Failed $ "Result " <> show result <> " does not fit in 128 bits"

-- | Property: lowest128BitsConstant returns a value that fits in 128 bits (Vesta)
propLowest128BitsFitsVesta :: Vesta.ScalarField -> Result
propLowest128BitsFitsVesta x =
  let
    result = lowest128BitsConstant x
    resultBigInt = toBigInt result
  in
    if fitsIn128Bits resultBigInt then Success
    else Failed $ "Result " <> show result <> " does not fit in 128 bits"

-- | Property: for values < 2^128, lowest128BitsConstant is identity (Pallas)
propIdempotentSmallPallas :: Pallas.ScalarField -> Result
propIdempotentSmallPallas x =
  let
    xBigInt = toBigInt x
    lo = lowest128BitsConstant x
  in
    if xBigInt <= max128Bits then lo === x
    else Success -- Skip large values

-- | Property: for values < 2^128, lowest128BitsConstant is identity (Vesta)
propIdempotentSmallVesta :: Vesta.ScalarField -> Result
propIdempotentSmallVesta x =
  let
    xBigInt = toBigInt x
    lo = lowest128BitsConstant x
  in
    if xBigInt <= max128Bits then lo === x
    else Success -- Skip large values

-------------------------------------------------------------------------------
-- | Circuit tests: verify circuit versions match pure versions
-------------------------------------------------------------------------------

-- | Test that circuit lowest128Bits matches pure lowest128BitsConstant
circuitLowest128BitsTest
  :: forall f f'
   . PrimeField f
  => FieldSizeInBits f 255
  => Kimchi.KimchiVerify f f'
  => Proxy f
  -> Aff Unit
circuitLowest128BitsTest _ =
  let
    referenceFn :: F f -> F f
    referenceFn (F x) = F $ lowest128BitsConstant x

    circuitFn
      :: forall t m
       . CircuitM f (KimchiConstraint f) t m
      => FVar f
      -> Snarky (KimchiConstraint f) t m (FVar f)
    circuitFn = lowest128Bits

    solver = makeSolver (Proxy @(KimchiConstraint f)) circuitFn
    builtState = compilePure
      (Proxy @(F f))
      (Proxy @(F f))
      (Proxy @(KimchiConstraint f))
      circuitFn
      Kimchi.initialState
    genInputs = F <$> arbitrary
  in
    circuitSpecPure' 100
      { builtState
      , checker: eval
      , solver
      , testFunction: satisfied referenceFn
      , postCondition: Kimchi.postCondition
      }
      genInputs

-- | Test that circuit squeezeChallenge matches pure squeezeChallengePure
circuitSqueezeChallengeTest
  :: forall f f'
   . PrimeField f
  => FieldSizeInBits f 255
  => Kimchi.KimchiVerify f f'
  => Proxy f
  -> Aff Unit
circuitSqueezeChallengeTest _ =
  let
    -- Reference: absorb 2 elements, then squeeze challenge
    referenceFn :: Tuple (F f) (F f) -> F f
    referenceFn (Tuple (F a) (F b)) =
      let
        pureSponge = Sponge.create Sponge.initialState
        s1 = Sponge.absorb a pureSponge
        s2 = Sponge.absorb b s1
        { result: Challenge r } = squeezeChallengePure s2
      in
        F r

    circuitFn
      :: forall t m
       . CircuitM f (KimchiConstraint f) t m
      => Tuple (FVar f) (FVar f)
      -> Snarky (KimchiConstraint f) t m (FVar f)
    circuitFn (Tuple a b) = do
      let sponge0 = CircuitSponge.create CircuitSponge.initialState
      sponge1 <- CircuitSponge.absorb a sponge0
      sponge2 <- CircuitSponge.absorb b sponge1
      { result: Challenge r } <- squeezeChallenge sponge2
      pure r

    solver = makeSolver (Proxy @(KimchiConstraint f)) circuitFn
    builtState = compilePure
      (Proxy @(Tuple (F f) (F f)))
      (Proxy @(F f))
      (Proxy @(KimchiConstraint f))
      circuitFn
      Kimchi.initialState
    genInputs = Tuple <$> (F <$> arbitrary) <*> (F <$> arbitrary)
  in
    circuitSpecPure' 100
      { builtState
      , checker: eval
      , solver
      , testFunction: satisfied referenceFn
      , postCondition: Kimchi.postCondition
      }
      genInputs

-- | Test that circuit squeezeScalar matches pure squeezeScalarPure
circuitSqueezeScalarTest
  :: forall f f'
   . PrimeField f
  => FieldSizeInBits f 255
  => Kimchi.KimchiVerify f f'
  => Proxy f
  -> Aff Unit
circuitSqueezeScalarTest _ =
  let
    -- Reference: absorb 2 elements, then squeeze scalar
    referenceFn :: Tuple (F f) (F f) -> F f
    referenceFn (Tuple (F a) (F b)) =
      let
        pureSponge = Sponge.create Sponge.initialState
        s1 = Sponge.absorb a pureSponge
        s2 = Sponge.absorb b s1
        { result: ScalarChallenge r } = squeezeScalarPure s2
      in
        F r

    circuitFn
      :: forall t m
       . CircuitM f (KimchiConstraint f) t m
      => Tuple (FVar f) (FVar f)
      -> Snarky (KimchiConstraint f) t m (FVar f)
    circuitFn (Tuple a b) = do
      let sponge0 = CircuitSponge.create CircuitSponge.initialState
      sponge1 <- CircuitSponge.absorb a sponge0
      sponge2 <- CircuitSponge.absorb b sponge1
      { result: ScalarChallenge r } <- squeezeScalar sponge2
      pure r

    solver = makeSolver (Proxy @(KimchiConstraint f)) circuitFn
    builtState = compilePure
      (Proxy @(Tuple (F f) (F f)))
      (Proxy @(F f))
      (Proxy @(KimchiConstraint f))
      circuitFn
      Kimchi.initialState
    genInputs = Tuple <$> (F <$> arbitrary) <*> (F <$> arbitrary)
  in
    circuitSpecPure' 100
      { builtState
      , checker: eval
      , solver
      , testFunction: satisfied referenceFn
      , postCondition: Kimchi.postCondition
      }
      genInputs
