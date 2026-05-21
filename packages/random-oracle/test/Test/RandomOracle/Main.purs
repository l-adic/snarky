module Test.RandomOracle.Main where

import Prelude

import Control.Monad.Gen (chooseInt)
import Data.Array ((:))
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Fin (unsafeFinite)
import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable, reifyType)
import Data.Traversable (for_)
import Data.Tuple (Tuple(..), uncurry)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Class.Console as Console
import Partial.Unsafe (unsafePartial)
import Poseidon (class PoseidonField, hash) as Poseidon
import RandomOracle (digest, hash, initialState, update)
import RandomOracle.DomainSeparator (class HasDomainSeparator, initWithDomain)
import RandomOracle.Sponge as Sponge
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky)
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Circuit.RandomOracle as Checked
import Snarky.Circuit.RandomOracle.Sponge as CircuitSponge
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint, KimchiGate, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (arbitrary, (===))
import Test.QuickCheck.Gen (randomSample', randomSampleOne)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTest', satisfied)
import Test.Spec (Spec, before, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual)
import Test.Spec.QuickCheck (quickCheck)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))

kimchiTestConfig :: forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)
kimchiTestConfig = { checker: eval, postCondition: Kimchi.postCondition, initState: Kimchi.initialState }

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

      describe "circuit sponge" do
        circuitSpongeTests (Proxy :: Proxy Pallas.BaseField)

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

      describe "circuit sponge" do
        circuitSpongeTests (Proxy :: Proxy Vesta.BaseField)

  -- (`Sponge matches Rust FFI` describe block + `spongeFFITests` helper
  -- removed alongside `snarky-crypto` — that suite was a parity check
  -- against the Rust `mina_poseidon::ArithmeticSponge` FFI. The PS-side
  -- sponge has its own correctness specs above; permutation byte-parity
  -- against kimchi-napi's `caml_pasta_f{p,q}_poseidon_block_cipher`
  -- lives in `packages/curves/test/poseidon-parity-harness.mjs`.)

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
    for_ [ [], [ zero ], [ zero, zero ], [ zero, zero, zero ], [ F x ], [ F x, zero ], [ F x, zero, zero ] ] \v ->
      reifyType (Array.length v) \pn -> do
        let v' = unsafePartial fromJust $ Vector.toVector' pn v
        Console.log $ "Testing edge case " <> show v'
        hashVecEdgeCase pf v'

  genLengths :: Aff (Array Int)
  genLengths = liftEffect do
    ns <- randomSample' 3 $ chooseInt 1 17
    pure $ 0 : 1 : 2 : Array.nub ns

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
        result1 = (Sponge.squeeze sponge2).result

        sponge3 = Sponge.create Sponge.initialState
        sponge4 = Sponge.absorb y (Sponge.absorb x sponge3)
        result2 = (Sponge.squeeze sponge4).result
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

    circuit'
      :: forall t
       . CircuitM f (KimchiConstraint f) t Identity
      => Tuple (FVar f) (FVar f)
      -> Snarky (KimchiConstraint f) t Identity (Digest (FVar f))
    circuit' = uncurry Checked.hash2

    genInputs = Tuple <$> (F <$> arbitrary) <*> (F <$> arbitrary)

  void $ circuitTest' @f
    kimchiTestConfig
    (NEA.singleton { testFunction: satisfied referenceHash, input: QuickCheck 100 genInputs })
    circuit'

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
    referenceHash inputs =
      let
        xs :: Array f
        xs = coerce (Vector.toUnfoldable inputs :: Array (F f))
      in
        Digest $ F $ hash xs

    circuit'
      :: forall t
       . CircuitM f (KimchiConstraint f) t Identity
      => Vector n (FVar f)
      -> Snarky (KimchiConstraint f) t Identity (Digest (FVar f))
    circuit' x = Checked.hashVec (Vector.toUnfoldable x)

    genInputs = Vector.generator pn (F <$> arbitrary)

  void $ circuitTest' @f
    kimchiTestConfig
    (NEA.singleton { testFunction: satisfied referenceHash, input: QuickCheck 100 genInputs })
    circuit'

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
    referenceHash xs =
      let
        xs' :: Array f
        xs' = coerce (Vector.toUnfoldable xs :: Array (F f))
      in
        Digest $ F $ hash xs'

    circuit'
      :: forall t
       . CircuitM f (KimchiConstraint f) t Identity
      => Vector n (FVar f)
      -> Snarky (KimchiConstraint f) t Identity (Digest (FVar f))
    circuit' x = Checked.hashVec (Vector.toUnfoldable x)

  void $ circuitTest' @f
    kimchiTestConfig
    (NEA.singleton { testFunction: satisfied referenceHash, input: Exact (NEA.singleton input) })
    circuit'

-- | Test circuit sponge absorb/squeeze matches pure sponge
circuitSpongeTests
  :: forall f f'
   . Poseidon.PoseidonField f
  => PrimeField f
  => Kimchi.KimchiVerify f f'
  => Proxy f
  -> Spec Unit
circuitSpongeTests _ = do
  it "absorb then squeeze matches pure sponge" do
    absorbSqueezeTest

  it "multiple absorb/squeeze cycles match pure sponge" do
    multiCycleTest

  where
  -- Test: absorb 2 elements, squeeze 1
  absorbSqueezeTest :: Aff Unit
  absorbSqueezeTest = do
    let
      -- Reference: pure sponge
      referenceFn :: Tuple (F f) (F f) -> F f
      referenceFn (Tuple (F a) (F b)) =
        let
          pureSponge = Sponge.create Sponge.initialState
          s1 = Sponge.absorb a pureSponge
          s2 = Sponge.absorb b s1
        in
          F (Sponge.squeeze s2).result

      -- Circuit version (fixed to Identity)
      circuit'
        :: forall t
         . CircuitM f (KimchiConstraint f) t Identity
        => Tuple (FVar f) (FVar f)
        -> Snarky (KimchiConstraint f) t Identity (FVar f)
      circuit' (Tuple a b) = do
        let sponge0 = CircuitSponge.create CircuitSponge.initialState
        sponge1 <- CircuitSponge.absorb a sponge0
        sponge2 <- CircuitSponge.absorb b sponge1
        { result } <- CircuitSponge.squeeze sponge2
        pure result

      genInputs = Tuple <$> (F <$> arbitrary) <*> (F <$> arbitrary)

    void $ circuitTest' @f
      kimchiTestConfig
      (NEA.singleton { testFunction: satisfied referenceFn, input: QuickCheck 100 genInputs })
      circuit'

  -- Test: absorb 3, squeeze 2
  multiCycleTest :: Aff Unit
  multiCycleTest = do
    let
      -- Reference: pure sponge
      referenceFn :: Tuple (F f) (Tuple (F f) (F f)) -> Tuple (F f) (F f)
      referenceFn (Tuple (F a) (Tuple (F b) (F c))) =
        let
          pureSponge = Sponge.create Sponge.initialState
          s1 = Sponge.absorb a pureSponge
          s2 = Sponge.absorb b s1
          s3 = Sponge.absorb c s2
          { result: r1, sponge: s4 } = Sponge.squeeze s3
          { result: r2 } = Sponge.squeeze s4
        in
          Tuple (F r1) (F r2)

      -- Circuit version (fixed to Identity)
      circuit'
        :: forall t
         . CircuitM f (KimchiConstraint f) t Identity
        => Tuple (FVar f) (Tuple (FVar f) (FVar f))
        -> Snarky (KimchiConstraint f) t Identity (Tuple (FVar f) (FVar f))
      circuit' (Tuple a (Tuple b c)) = do
        let sponge0 = CircuitSponge.create CircuitSponge.initialState
        sponge1 <- CircuitSponge.absorb a sponge0
        sponge2 <- CircuitSponge.absorb b sponge1
        sponge3 <- CircuitSponge.absorb c sponge2
        { result: r1, sponge: sponge4 } <- CircuitSponge.squeeze sponge3
        { result: r2 } <- CircuitSponge.squeeze sponge4
        pure $ Tuple r1 r2

      genInputs = Tuple <$> (F <$> arbitrary) <*> (Tuple <$> (F <$> arbitrary) <*> (F <$> arbitrary))

    void $ circuitTest' @f
      kimchiTestConfig
      (NEA.singleton { testFunction: satisfied referenceFn, input: QuickCheck 100 genInputs })
      circuit'
