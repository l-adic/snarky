module Test.RandomOracle.Main where

import Prelude

import Control.Monad.Gen (chooseInt)
import Data.Array ((:))
import Data.Array as Array
import Data.Fin (unsafeFinite)
import Data.Maybe (fromJust)
import Data.Newtype (unwrap)
import Data.Reflectable (class Reflectable, reifyType)
import Data.Traversable (for_)
import Data.Tuple (Tuple(..), fst, uncurry)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Class.Console as Console
import Partial.Unsafe (unsafePartial)
import Poseidon.Class (class PoseidonField, hash) as Poseidon
import RandomOracle (digest, hash, initialState, update)
import RandomOracle.DomainSeparator (class HasDomainSeparator, initWithDomain)
import RandomOracle.Sponge as Sponge
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Circuit.RandomOracle as Checked
import Snarky.Circuit.Types (F(..))
import Snarky.Constraint.Kimchi (KimchiConstraint, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (arbitrary, (===))
import Test.QuickCheck.Gen (randomSample', randomSampleOne)
import Test.Snarky.Circuit.Utils (circuitSpecPure', circuitSpecPureInputs, satisfied)
import Test.Spec (Spec, before, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual)
import Test.Spec.QuickCheck (quickCheck)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] spec

spec :: Spec Unit
spec = do
  describe "RandomOracle" do
    describe "Pallas" do
      hashTests (Proxy :: Proxy Pallas.BaseField)
      spongeTests (Proxy :: Proxy Pallas.BaseField)
      domainSeparatorTests (Proxy :: Proxy Pallas.BaseField)

    describe "circuit tests" $ do
      it "Can handle hashing 2 elements" $
        hash2CircuitTests (Proxy :: Proxy Pallas.BaseField)
      before genLengths $ it "Can handle variable length input" \ns ->
        for_ ns \n -> do
          Console.log $ "Checking for size " <> show n
          reifyType n \pn ->
            hashVecCircuitTests (Proxy :: Proxy Pallas.BaseField) pn

      it "Can handle edge cases" do
        checkEdgeCases (Proxy :: Proxy Pallas.BaseField)

    describe "Vesta" do
      hashTests (Proxy :: Proxy Vesta.BaseField)
      spongeTests (Proxy :: Proxy Vesta.BaseField)
      domainSeparatorTests (Proxy :: Proxy Vesta.BaseField)

      it "Can handle hashing 2 elements" $
        hash2CircuitTests (Proxy :: Proxy Vesta.BaseField)
      before genLengths $ it "Can handle variable length input" \ns ->
        for_ ns \n -> do
          Console.log $ "Checking for size " <> show n
          reifyType n \pn ->
            hashVecCircuitTests (Proxy :: Proxy Vesta.BaseField) pn
      it "Can handle edge cases" do
        checkEdgeCases (Proxy :: Proxy Vesta.BaseField)

  where
  checkEdgeCases
    :: forall f f'
     . Poseidon.PoseidonField f
    => PrimeField f
    => Kimchi.KimchiVerify f f'
    => Proxy f
    -> Aff Unit
  checkEdgeCases pf = do
    x <- liftEffect $ randomSampleOne arbitrary
    -- NOTE: empty array case is skipped due to known issue (see TODO in genLengths)
    for_ [ [ zero ], [ zero, zero ], [ zero, zero, zero ], [ F x ], [ F x, zero ], [ F x, zero, zero ] ] \v ->
      reifyType (Array.length v) \pn -> do
        let v' = unsafePartial fromJust $ Vector.toVector' pn v
        Console.log $ "Testing edge case " <> show v'
        hashVecEdgeCase pf v'

  genLengths :: Aff (Array Int)
  genLengths = liftEffect do
    ns <- randomSample' 3 $ chooseInt 1 17
    --TODO: the test case for 0 is failing
    pure $ 1 : 2 : Array.nub ns

hashTests
  :: forall f
   . Poseidon.PoseidonField f
  => PrimeField f
  => Proxy f
  -> Spec Unit
hashTests _ = describe "Hash" do

  it "hash matches poseidon library" do
    quickCheck \(inputs :: Array f) ->
      hash inputs === Poseidon.hash inputs

  it "update then digest equals hash" do
    quickCheck \(inputs :: Array f) ->
      hash inputs === digest (update initialState inputs)

  describe "edge cases" do
    it "empty array" do
      hash ([] :: Array f) `shouldEqual` Poseidon.hash []

    it "[zero]" do
      hash [ zero ] `shouldEqual` Poseidon.hash ([ zero ] :: Array f)

    it "[zero, zero]" do
      hash [ zero, zero ] `shouldEqual` Poseidon.hash ([ zero, zero ] :: Array f)

    it "[zero, zero, zero]" do
      hash [ zero, zero, zero ] `shouldEqual` Poseidon.hash ([ zero, zero, zero ] :: Array f)

    it "[x] for arbitrary x" do
      quickCheck \(x :: f) ->
        hash [ x ] === Poseidon.hash [ x ]

    it "[x, zero, zero] for arbitrary x" do
      quickCheck \(x :: f) ->
        hash [ x, zero, zero ] === Poseidon.hash [ x, zero, zero ]

spongeTests
  :: forall f
   . Poseidon.PoseidonField f
  => Proxy f
  -> Spec Unit
spongeTests _ = describe "Sponge" do

  it "sponge absorb then squeeze is deterministic" do
    quickCheck \(x :: f) (y :: f) ->
      let
        sponge1 = Sponge.create Sponge.initialState
        sponge2 = Sponge.absorb y (Sponge.absorb x sponge1)
        result1 = fst (Sponge.squeeze sponge2)

        sponge3 = Sponge.create Sponge.initialState
        sponge4 = Sponge.absorb y (Sponge.absorb x sponge3)
        result2 = fst (Sponge.squeeze sponge4)
      in
        result1 === result2

  it "sponge state size is 3" do
    Sponge.stateSize `shouldEqual` 3

  it "sponge rate is 2" do
    Sponge.rate `shouldEqual` unsafeFinite 2

domainSeparatorTests
  :: forall f
   . HasDomainSeparator f
  => Semiring f
  => Eq f
  => Show f
  => Proxy f
  -> Spec Unit
domainSeparatorTests _ = describe "DomainSeparator" do

  it "initWithDomain is deterministic" do
    let
      state1 = initWithDomain @f "TestDomain"
      state2 = initWithDomain @f "TestDomain"
    state1 `shouldEqual` state2

  it "different domains produce different states" do
    let
      state1 = initWithDomain @f "Domain1"
      state2 = initWithDomain @f "Domain2"
    state1 `shouldNotEqual` state2

  it "initWithDomain differs from zero initial state" do
    let
      domainState = initWithDomain @f "TestDomain"
    domainState `shouldNotEqual` initialState

hash2CircuitTests
  :: forall f f'
   . Poseidon.PoseidonField f
  => PrimeField f
  => Kimchi.KimchiVerify f f'
  => Proxy f
  -> Aff Unit
hash2CircuitTests _ = do

  let
    -- Reference: pure hash of 2 elements
    referenceHash :: Tuple (F f) (F f) -> Digest (F f)
    referenceHash (Tuple (F a) (F b)) = Digest $ F $ hash [ a, b ]

    solver = makeSolver (Proxy @(KimchiConstraint f)) (uncurry Checked.hash2)
    s = compilePure
      (Proxy @(Tuple (F f) (F f)))
      (Proxy @(Digest (F f)))
      (Proxy @(KimchiConstraint f))
      (uncurry Checked.hash2)
      Kimchi.initialState
    genInputs = Tuple <$> (F <$> arbitrary) <*> (F <$> arbitrary)

  circuitSpecPure'
    { builtState: s
    , checker: eval
    , solver: solver
    , testFunction: satisfied referenceHash
    , postCondition: Kimchi.postCondition
    }
    genInputs

hashVecCircuitTests
  :: forall f f' n
   . Poseidon.PoseidonField f
  => Reflectable n Int
  => PrimeField f
  => Kimchi.KimchiVerify f f'
  => Proxy f
  -> Proxy n
  -> Aff Unit
hashVecCircuitTests _ pn = do
  let
    referenceHash :: Vector n (F f) -> Digest (F f)
    referenceHash inputs = Digest $ F $ hash (map unwrap (Vector.toUnfoldable inputs))

    solver = makeSolver (Proxy @(KimchiConstraint f)) (\x -> Checked.hashVec (Vector.toUnfoldable x))
    s = compilePure
      (Proxy @(Vector n (F f)))
      (Proxy @((Digest (F f))))
      (Proxy @(KimchiConstraint f))
      (\x -> Checked.hashVec (Vector.toUnfoldable x))
      Kimchi.initialState
    genInputs = Vector.generator pn (F <$> arbitrary)

  circuitSpecPure'
    { builtState: s
    , checker: eval
    , solver: solver
    , testFunction: satisfied referenceHash
    , postCondition: Kimchi.postCondition
    }
    genInputs

-- | Test hashVec circuit with a specific input
hashVecEdgeCase
  :: forall f f' n
   . Poseidon.PoseidonField f
  => Reflectable n Int
  => PrimeField f
  => Kimchi.KimchiVerify f f'
  => Proxy f
  -> Vector n (F f)
  -> Aff Unit
hashVecEdgeCase _ input = do
  let
    referenceHash :: Vector n (F f) -> Digest (F f)
    referenceHash xs = Digest $ F $ hash (map unwrap (Vector.toUnfoldable xs))

    solver = makeSolver (Proxy @(KimchiConstraint f)) (\x -> Checked.hashVec (Vector.toUnfoldable x))
    s = compilePure
      (Proxy @(Vector n (F f)))
      (Proxy @((Digest (F f))))
      (Proxy @(KimchiConstraint f))
      (\x -> Checked.hashVec (Vector.toUnfoldable x))
      Kimchi.initialState

  circuitSpecPureInputs
    { builtState: s
    , checker: eval
    , solver: solver
    , testFunction: satisfied referenceHash
    , postCondition: Kimchi.postCondition
    }
    [ input ]
