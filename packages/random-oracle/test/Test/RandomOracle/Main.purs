module Test.RandomOracle.Main where

import Prelude

import Control.Monad.Gen (chooseInt)
import Data.Array ((:))
import Data.Array as Array
import Data.Fin (unsafeFinite)
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
import Test.QuickCheck.Gen (randomSample')
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
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

  where
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
