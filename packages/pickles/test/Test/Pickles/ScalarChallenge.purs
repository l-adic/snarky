module Test.Pickles.ScalarChallenge where

import Prelude

import Data.Newtype (unwrap)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import JS.BigInt as BigInt
import Pickles.ScalarChallenge (Challenge(..), lowest128Bits, lowest128BitsConstant, squeezeChallenge, squeezeChallengePure, squeezeScalar, squeezeScalarPure)
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
import Snarky.Data.SizedF (SizedF(..))
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

spec :: Spec Unit
spec = do
  describe "Pickles.ScalarChallenge" do
    describe "Pallas" do
      scalarChallengeTests (Proxy @Pallas.BaseField)
    describe "Vesta" do
      scalarChallengeTests (Proxy @Vesta.BaseField)

-- | All scalar challenge tests parameterized by field type
scalarChallengeTests
  :: forall f f'
   . PrimeField f
  => FieldSizeInBits f 255
  => Kimchi.KimchiVerify f f'
  => Proxy f
  -> Spec Unit
scalarChallengeTests pf = do
  describe "lowest128BitsConstant" do
    it "returns value that fits in 128 bits" $
      quickCheck (propLowest128BitsFits pf)
    it "is idempotent for small values" $
      quickCheck (propIdempotentSmall pf)

  describe "squeezeChallengePure" do
    it "produces deterministic output" do
      let
        sponge :: Sponge.Sponge f
        sponge = Sponge.create Sponge.initialState
        { result: Challenge r1 } = squeezeChallengePure sponge
        { result: Challenge r2 } = squeezeChallengePure sponge
      r1 `shouldEqual` r2

    it "produces value in 128-bit range" do
      let
        sponge :: Sponge.Sponge f
        sponge = Sponge.create Sponge.initialState
        { result: Challenge result } = squeezeChallengePure sponge
      toBigInt result `shouldSatisfy` fitsIn128Bits

  describe "squeezeScalarPure" do
    it "produces deterministic output" do
      let
        sponge :: Sponge.Sponge f
        sponge = Sponge.create Sponge.initialState
        { result: SizedF r1 } = squeezeScalarPure sponge
        { result: SizedF r2 } = squeezeScalarPure sponge
      r1 `shouldEqual` r2

  describe "Circuit versions match pure" do
    it "lowest128Bits matches lowest128BitsConstant" $
      circuitLowest128BitsTest pf
    it "squeezeChallenge matches squeezeChallengePure" $
      circuitSqueezeChallengeTest pf
    it "squeezeScalar matches squeezeScalarPure" $
      circuitSqueezeScalarTest pf

-- | Property: lowest128BitsConstant returns a value that fits in 128 bits
propLowest128BitsFits :: forall f. PrimeField f => FieldSizeInBits f 255 => Proxy f -> f -> Result
propLowest128BitsFits _ x =
  let
    result = lowest128BitsConstant x
    resultBigInt = toBigInt result
  in
    if fitsIn128Bits resultBigInt then Success
    else Failed $ "Result " <> show result <> " does not fit in 128 bits"

-- | Property: for values < 2^128, lowest128BitsConstant is identity
propIdempotentSmall :: forall f. PrimeField f => FieldSizeInBits f 255 => Proxy f -> f -> Result
propIdempotentSmall _ x =
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
        { result } = squeezeScalarPure s2
      in
        F $ unwrap result

    circuitFn
      :: forall t m
       . CircuitM f (KimchiConstraint f) t m
      => Tuple (FVar f) (FVar f)
      -> Snarky (KimchiConstraint f) t m (FVar f)
    circuitFn (Tuple a b) = do
      let sponge0 = CircuitSponge.create CircuitSponge.initialState
      sponge1 <- CircuitSponge.absorb a sponge0
      sponge2 <- CircuitSponge.absorb b sponge1
      { result } <- squeezeScalar sponge2
      pure $ unwrap result

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
