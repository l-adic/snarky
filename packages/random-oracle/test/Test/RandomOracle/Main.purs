module Test.RandomOracle.Main where

import Prelude

import Data.Newtype (unwrap)
import Data.Fin (unsafeFinite)
import Data.Tuple (fst, Tuple(..), uncurry)
import Effect (Effect)
import Poseidon.Class (class PoseidonField, hash) as Poseidon
import RandomOracle (hash, update, initialState, digest)
import RandomOracle.Checked as Checked
import RandomOracle.DomainSeparator (class HasDomainSeparator, initWithDomain)
import RandomOracle.Sponge as Sponge
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.Types (F(..))
import Snarky.Constraint.Kimchi (KimchiConstraint, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Data.Vector (Vector)
import Data.Vector as Vector
import Test.QuickCheck ((===), arbitrary)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
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
      circuitTests (Proxy :: Proxy Pallas.BaseField)

    describe "Vesta" do
      hashTests (Proxy :: Proxy Vesta.BaseField)
      spongeTests (Proxy :: Proxy Vesta.BaseField)
      domainSeparatorTests (Proxy :: Proxy Vesta.BaseField)
      circuitTests (Proxy :: Proxy Vesta.BaseField)

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

circuitTests
  :: forall f f'
   . Poseidon.PoseidonField f
  => PrimeField f
  => Kimchi.KimchiVerify f f'
  => Proxy f
  -> Spec Unit
circuitTests _ = describe "Circuit" do

  it "hashChecked2 circuit matches pure hash" do
    let
      -- Reference: pure hash of 2 elements
      referenceHash :: Tuple (F f) (F f) -> F f
      referenceHash (Tuple (F a) (F b)) = F $ hash [ a, b ]

      solver = makeSolver (Proxy @(KimchiConstraint f)) (uncurry Checked.hashChecked2)
      s = compilePure
        (Proxy @(Tuple (F f) (F f)))
        (Proxy @(F f))
        (Proxy @(KimchiConstraint f))
        (uncurry Checked.hashChecked2)
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

  it "hashChecked circuit matches pure hash for 4 elements" do
    let
      -- Reference: pure hash of 4 elements
      referenceHash :: Vector 4 (F f) -> F f
      referenceHash inputs = F $ hash (map unwrap (Vector.toUnfoldable inputs))

      solver = makeSolver (Proxy @(KimchiConstraint f)) (Checked.hashChecked @4 @2)
      s = compilePure
        (Proxy @(Vector 4 (F f)))
        (Proxy @(F f))
        (Proxy @(KimchiConstraint f))
        (Checked.hashChecked @4 @2)
        Kimchi.initialState
      genInputs = Vector.generator (Proxy @4) (F <$> arbitrary)

    circuitSpecPure'
      { builtState: s
      , checker: eval
      , solver: solver
      , testFunction: satisfied referenceHash
      , postCondition: Kimchi.postCondition
      }
      genInputs
