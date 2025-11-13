module Snarky.Test.Circuit.Circuit (spec) where

import Prelude

import Data.Array (filter, foldMap, foldl, (..))
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray, fromArray)
import Data.Either (Either(..))
import Data.Foldable (for_, sum)
import Data.Identity (Identity)
import Data.Int (pow)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust)
import Data.Monoid.Conj (Conj(..))
import Data.Monoid.Disj (Disj(..))
import Data.Newtype (un)
import Data.Reflectable (class Reflectable, reflectType, reifyType)
import Data.Traversable (sequence)
import Data.Tuple (Tuple(..), uncurry)
import Data.Tuple.Nested (Tuple3, uncurry3)
import Effect.Aff (throwError)
import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafeCrashWith, unsafePartial)
import Snarky.Circuit.Builder (CircuitBuilderState, emptyCircuitBuilderState, runCircuitBuilder)
import Snarky.Circuit.CVar (CVar, EvaluationError(..))
import Snarky.Circuit.Constraint (R1CS, R1CSCircuit(..), evalR1CSCircuit)
import Snarky.Circuit.DSL (class CircuitM, publicInputs, read, runAsProver)
import Snarky.Circuit.DSL.Assert (assertEqual, assertNonZero)
import Snarky.Circuit.DSL.Bits (pack, unpack)
import Snarky.Circuit.DSL.Boolean (all_, and_, any_, ifThenElse_, not_, or_, xor_)
import Snarky.Circuit.DSL.Field (div_, eq_, inv_, mul_, square_, sum_)
import Snarky.Circuit.Prover (assignPublicInputs, emptyProverState, runProver)
import Snarky.Circuit.Types (class ConstrainedType, Bool, FieldElem(..), Variable)
import Snarky.Curves.BN254 as BN254
import Snarky.Curves.Types (fromBigInt, toBigInt)
import Snarky.Data.Vector (Vector, toVector, unVector)
import Snarky.Data.Vector as Vector
import Test.QuickCheck (Result, arbitrary, quickCheckGen, quickCheckGen', withHelp)
import Test.QuickCheck.Gen (Gen, chooseInt)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck)
import Type.Proxy (Proxy(..))

spec :: Spec Unit
spec = do
  fieldSpec
  boolSpec
  assertSpec
  bitsSpec

type Fr = BN254.ScalarField

type ConstraintSystem = R1CS Fr Variable

type Inputs2 =
  Tuple
    (FieldElem Fr)
    (FieldElem Fr)

mulCircuit
  :: forall m n
   . CircuitM Fr ConstraintSystem m n
  => m (CVar Fr Variable)
mulCircuit = do
  publicInputs @Fr (Proxy @Inputs2) >>= \(Tuple a b) ->
    mul_ a b

squareCircuit
  :: forall m p
   . CircuitM Fr ConstraintSystem m p
  => m (CVar Fr Variable)
squareCircuit =
  publicInputs @Fr (Proxy @(FieldElem Fr)) >>= \a ->
    square_ a

eqCircuit
  :: forall m n
   . CircuitM Fr ConstraintSystem m n
  => m (CVar Fr (Bool Variable))
eqCircuit = do
  publicInputs @Fr (Proxy @Inputs2) >>= \(Tuple a b) ->
    eq_ a b

invCircuit
  :: forall m n
   . CircuitM Fr ConstraintSystem m n
  => m (CVar Fr Variable)
invCircuit =
  publicInputs @Fr (Proxy @(FieldElem Fr)) >>= \a ->
    inv_ a

divCircuit
  :: forall m n
   . CircuitM Fr ConstraintSystem m n
  => m (CVar Fr Variable)
divCircuit =
  publicInputs @Fr (Proxy @Inputs2) >>= \(Tuple a b) ->
    div_ a b

notCircuit
  :: forall m n
   . CircuitM Fr ConstraintSystem m n
  => m (CVar Fr (Bool Variable))
notCircuit = do
  publicInputs @Fr (Proxy @Boolean) >>= \a ->
    pure $ not_ a

type BoolInputs2 =
  Tuple
    Boolean
    Boolean

andCircuit
  :: forall m n
   . CircuitM Fr ConstraintSystem m n
  => m (CVar Fr (Bool Variable))
andCircuit = do
  publicInputs @Fr (Proxy @BoolInputs2) >>= \(Tuple a b) ->
    and_ a b

orCircuit
  :: forall m n
   . CircuitM Fr ConstraintSystem m n
  => m (CVar Fr (Bool Variable))
orCircuit = do
  publicInputs @Fr (Proxy @BoolInputs2) >>= \(Tuple a b) ->
    or_ a b

xorCircuit
  :: forall m n
   . CircuitM Fr ConstraintSystem m n
  => m (CVar Fr (Bool Variable))
xorCircuit = do
  publicInputs @Fr (Proxy @BoolInputs2) >>= \(Tuple a b) ->
    xor_ a b

type IfThenElseInputs =
  Tuple3 Boolean (FieldElem Fr) (FieldElem Fr)

ifThenElseCircuit
  :: forall m n
   . CircuitM Fr ConstraintSystem m n
  => m (CVar Fr Variable)
ifThenElseCircuit =
  publicInputs @Fr (Proxy @IfThenElseInputs) >>= \(Tuple b (Tuple t e)) ->
    ifThenElse_ b t e

intSizes :: NonEmptyArray Int
intSizes = case fromArray $ filter (\x -> x `mod` 8 == 0) (8 .. 256) of
  Nothing -> unsafeCrashWith "intSizes: impossible"
  Just x -> x

allCircuit
  :: forall m n p
   . CircuitM Fr ConstraintSystem m p
  => Reflectable n Int
  => Proxy n
  -> m (CVar Fr (Bool Variable))
allCircuit _ =
  publicInputs @Fr (Proxy @(Vector n Boolean)) >>= \bs ->
    all_ (unVector bs)

anyCircuit
  :: forall m n p
   . CircuitM Fr ConstraintSystem m p
  => Reflectable n Int
  => Proxy n
  -> m (CVar Fr (Bool Variable))
anyCircuit _ =
  publicInputs @Fr (Proxy @(Vector n Boolean)) >>= \bs ->
    any_ (unVector bs)

sumCircuit
  :: forall m n p
   . CircuitM Fr ConstraintSystem m p
  => Reflectable n Int
  => Proxy n
  -> m (CVar Fr Variable)
sumCircuit _ =
  publicInputs @Fr (Proxy @(Vector n (FieldElem Fr))) >>= \bs ->
    pure $ sum_ (unVector bs)

assertNonZeroCircuit
  :: forall m n
   . CircuitM Fr ConstraintSystem m n
  => m Unit
assertNonZeroCircuit = do
  publicInputs @Fr (Proxy @(FieldElem Fr)) >>= \a ->
    assertNonZero a

assertEqualCircuit
  :: forall m n
   . CircuitM Fr ConstraintSystem m n
  => m Unit
assertEqualCircuit = do
  publicInputs @Fr (Proxy @(FieldElem Fr)) >>= \a ->
    assertEqual a a

mkCircuitSpec
  :: forall a b avar bvar
   . ConstrainedType Fr a ConstraintSystem avar
  => ConstrainedType Fr b ConstraintSystem bvar
  => Eq b
  => Gen a
  -> (forall m. CircuitM Fr ConstraintSystem m Identity => m bvar)
  -> (a -> b)
  -> Gen Result
mkCircuitSpec inputsGen circuit f = do
  inputs <- inputsGen
  let
    Tuple _ { constraints, publicInputs } =
      runCircuitBuilder circuit (emptyCircuitBuilderState :: CircuitBuilderState ConstraintSystem)
    Tuple result (assignments :: Map Variable Fr) =
      let
        proverState = emptyProverState { publicInputs = publicInputs }
      in
        case runProver (assignPublicInputs inputs *> circuit) proverState of
          Tuple (Left e) _ -> unsafeCrashWith $ "Error in circuit: " <> show e
          Tuple (Right c) { assignments } -> Tuple c assignments
    _lookup v = case Map.lookup v assignments of
      Nothing -> throwError $ MissingVariable v
      Just res -> pure res
    eres = runAsProver
      ( do
          isSatisfied <- evalR1CSCircuit _lookup (R1CSCircuit constraints)
          b <- read result
          pure $ isSatisfied && f inputs == b
      )
      assignments
  pure $
    case eres of
      Right res -> withHelp res "Circuit constraints satisfied and evals correctly"
      Left e -> withHelp false ("Failed to parse circuit output: " <> show e)

fieldSpec :: Spec Unit
fieldSpec = describe "Field Circuit Specs" do

  it "mul Circuit is Valid" $ quickCheck $
    mkCircuitSpec arbitrary mulCircuit \(Tuple (FieldElem a) (FieldElem b)) ->
      FieldElem @Fr (a * b)

  it "square Circuit is Valid" $ quickCheck $
    mkCircuitSpec arbitrary squareCircuit \(FieldElem a) ->
      FieldElem @Fr (a * a)

  it "eq Circuit is Valid" $ quickCheck $
    let
      f :: Tuple (FieldElem Fr) (FieldElem Fr) -> Boolean
      f = uncurry (==)
    in
      mkCircuitSpec arbitrary eqCircuit f

  it "inv Circuit is Valid" $ quickCheck $
    mkCircuitSpec arbitrary invCircuit \(FieldElem a) ->
      if a == zero then FieldElem zero
      else FieldElem @Fr (recip a)

  it "div Circuit is Valid" $ quickCheck $
    mkCircuitSpec arbitrary divCircuit \(Tuple (FieldElem a) (FieldElem b)) ->
      if b == zero then FieldElem zero
      else FieldElem @Fr (a / b)

  it "sum Circuit is Valid" $
    let
      f :: forall n. Vector n (FieldElem Fr) -> FieldElem Fr
      f as = FieldElem $ sum (un FieldElem <$> as)
    in
      liftEffect $
        for_ intSizes \n -> quickCheckGen' 10 do
          k <- chooseInt 1 n
          reifyType k \pk ->
            mkCircuitSpec (Vector.generator pk arbitrary) (sumCircuit pk) f

boolSpec :: Spec Unit
boolSpec = describe "Boolean Circuit Specs" do

  it "not Circuit is Valid" $ quickCheck $
    let
      f :: Boolean -> Boolean
      f = not
    in
      mkCircuitSpec arbitrary notCircuit f

  it "and Circuit is Valid" $ quickCheck $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f = uncurry (&&)
    in
      mkCircuitSpec arbitrary andCircuit f

  it "or Circuit is Valid" $ quickCheck $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f = uncurry (||)
    in
      mkCircuitSpec arbitrary orCircuit f

  it "xor Circuit is Valid" $ quickCheck $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f (Tuple a b) = (a && not b) || (not a && b)
    in
      mkCircuitSpec arbitrary xorCircuit f

  it "ifThenElse Circuit is Valid" $ quickCheck $
    let
      f :: Tuple3 Boolean (FieldElem Fr) (FieldElem Fr) -> FieldElem Fr
      f = uncurry3 \b t e ->
        if b then t else e
    in
      mkCircuitSpec arbitrary ifThenElseCircuit f

  it "all Circuit is Valid" $
    let
      f :: forall n. Vector n Boolean -> Boolean
      f = un Conj <<< foldMap Conj <<< unVector
    in
      liftEffect $
        for_ intSizes \n -> quickCheckGen' 10 do
          k <- chooseInt 1 n
          reifyType k \pk ->
            mkCircuitSpec (Vector.generator pk arbitrary) (allCircuit pk) f

  it "any Circuit is Valid" $
    let
      f :: forall n. Vector n Boolean -> Boolean
      f = un Disj <<< foldMap Disj <<< unVector
    in
      liftEffect $
        for_ intSizes \n -> quickCheckGen' 10 do
          k <- chooseInt 1 n
          reifyType k \pk ->
            mkCircuitSpec (Vector.generator pk arbitrary) (anyCircuit pk) f

mkAssertionSpec
  :: forall a avar
   . ConstrainedType Fr a ConstraintSystem avar
  => Gen a
  -> (forall m. CircuitM Fr ConstraintSystem m Identity => m Unit)
  -> (a -> Boolean) -- predicate that should be true for valid inputs
  -> Gen Result
mkAssertionSpec inputsGen circuit isValid = do
  inputs <- inputsGen
  let
    shouldSucceed = isValid inputs
    Tuple _ { constraints, publicInputs } =
      runCircuitBuilder circuit (emptyCircuitBuilderState :: CircuitBuilderState ConstraintSystem)
    proverResult =
      let
        proverState = emptyProverState { publicInputs = publicInputs }
      in
        runProver (assignPublicInputs inputs *> circuit) proverState
  case proverResult of
    Tuple (Left e) _ ->
      pure $ withHelp (not shouldSucceed) $
        if shouldSucceed then "Circuit failed with valid input: " <> show e
        else "Circuit correctly rejected invalid input"
    Tuple (Right _) { assignments } ->
      let
        _lookup v = case Map.lookup v assignments of
          Nothing -> throwError $ MissingVariable v
          Just res -> pure res
        eres = runAsProver (evalR1CSCircuit _lookup (R1CSCircuit constraints)) assignments
      in
        pure $ case eres of
          Right true -> withHelp shouldSucceed $
            if shouldSucceed then "Assertion circuit satisfied with valid input"
            else "Assertion circuit should have failed with invalid input"
          Right false -> withHelp false "Constraints not satisfied"
          Left e -> withHelp false ("Failed to evaluate circuit: " <> show e)

assertSpec :: Spec Unit
assertSpec = describe "Assertion Circuit Specs" do

  it "assertNonZero Circuit is Valid" $ quickCheck $
    let
      f :: FieldElem Fr -> Boolean
      f (FieldElem a) = a /= zero
    in
      mkAssertionSpec arbitrary assertNonZeroCircuit f

  it "assertEqual Circuit is Valid" $ quickCheck $
    let
      f :: Tuple (FieldElem Fr) (FieldElem Fr) -> Boolean
      f (Tuple (FieldElem a) (FieldElem b)) = a == b
    in
      mkAssertionSpec arbitrary assertEqualCircuit f

unpackCircuit
  :: forall m n k
   . CircuitM Fr ConstraintSystem m n
  => Reflectable k Int
  => Proxy k
  -> m (Vector k (CVar Fr (Bool Variable)))
unpackCircuit pk = do
  publicInputs @Fr (Proxy @(FieldElem Fr)) >>= \value ->
    unpack (reflectType pk) value >>= \bits ->
      pure $ unsafePartial $ fromJust $ toVector pk bits

packUnpackCircuit
  :: forall m n
   . CircuitM Fr ConstraintSystem m n
  => Int
  -> m (CVar Fr Variable)
packUnpackCircuit nBits = do
  publicInputs @Fr (Proxy @(FieldElem Fr)) >>= \value ->
    unpack nBits value >>= \bits ->
      pure $ pack bits

bitSizes :: Array Int
bitSizes = [ 8, 16, 32, 64, 256 ]

smallFieldElem :: Int -> Gen (FieldElem Fr)
smallFieldElem bitCount = do
  if bitCount <= 31 then do
    -- For small bit counts, generate directly
    n <- chooseInt 0 $ (2 `pow` bitCount) - 1
    pure $ FieldElem $ fromBigInt $ BigInt.fromInt n
  else do
    -- For larger bit counts, generate in chunks
    let chunks = (bitCount + 31) / 32
    values <- sequence $ Array.replicate chunks $
      chooseInt 0 ((2 `pow` 32) - 1)
    let
      combined = foldl
        ( \acc (Tuple i val) ->
            acc `BigInt.or` (BigInt.fromInt val `BigInt.shl` BigInt.fromInt (i * 32))
        )
        zero
        (Array.mapWithIndex Tuple values)
      mask = (BigInt.fromInt 1 `BigInt.shl` BigInt.fromInt bitCount) - BigInt.fromInt 1
    pure $ FieldElem $ fromBigInt $ combined `BigInt.and` mask

bitsSpec :: Spec Unit
bitsSpec = describe "Bits Circuit Specs" do
  it "unpack Circuit is Valid" $ do
    let
      f :: forall k. Reflectable k Int => Proxy k -> FieldElem Fr -> Vector k Boolean
      f pk (FieldElem v) =
        let
          bitCount = reflectType pk
          toBit i = (toBigInt v `BigInt.and` (BigInt.fromInt 1 `BigInt.shl` BigInt.fromInt i)) /= zero
          bits = map toBit (Array.range 0 (bitCount - 1))
        in
          unsafePartial $ fromJust $ toVector pk bits
    liftEffect $
      for_ bitSizes \n -> quickCheckGen do
        reifyType n \pk ->
          mkCircuitSpec (smallFieldElem n) (unpackCircuit pk) (f pk)

  it "pack/unpack round trip is Valid"
    $ liftEffect
    $
      for_ bitSizes \n -> quickCheckGen do
        mkCircuitSpec (smallFieldElem n) (packUnpackCircuit n) identity