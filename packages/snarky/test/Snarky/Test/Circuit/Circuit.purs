module Snarky.Test.Circuit.Circuit (spec) where

import Prelude

import Data.Array (filter, foldMap, foldl, (..))
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray, fromArray)
import Data.Foldable (for_, sum)
import Data.Identity (Identity(..))
import Data.Int (pow)
import Data.Maybe (Maybe(..), fromJust)
import Data.Monoid.Conj (Conj(..))
import Data.Monoid.Disj (Disj(..))
import Data.Newtype (un)
import Data.Reflectable (class Reflectable, reflectType, reifyType)
import Data.Traversable (sequence)
import Data.Tuple (Tuple(..), uncurry)
import Data.Tuple.Nested (Tuple3, uncurry3)
import Effect.Aff (Aff)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafeCrashWith, unsafePartial)
import Snarky.Circuit.CVar (CVar)
import Snarky.Circuit.Compile (compile, makeAssertionSpec, makeCircuitSpec)
import Snarky.Circuit.Constraint (R1CS, evalR1CSConstraint)
import Snarky.Circuit.DSL (class CircuitM, publicInputs)
import Snarky.Circuit.DSL.Assert (assertEqual, assertNonZero)
import Snarky.Circuit.DSL.Bits (pack, unpack)
import Snarky.Circuit.DSL.Boolean (all_, and_, any_, ifThenElse_, not_, or_, xor_)
import Snarky.Circuit.DSL.Field (div_, eq_, inv_, mul_, square_, sum_)
import Snarky.Circuit.Types (class ConstrainedType, Bool, FieldElem(..), Variable)
import Snarky.Curves.BN254 as BN254
import Snarky.Curves.Class (fromBigInt, toBigInt)
import Snarky.Data.Vector (Vector, toVector, unVector)
import Snarky.Data.Vector as Vector
import Test.QuickCheck (class Arbitrary, arbitrary)
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
  :: forall t n
   . CircuitM Fr ConstraintSystem t n
  => t n (CVar Fr Variable)
mulCircuit = do
  publicInputs @Fr (Proxy @Inputs2) >>= \(Tuple a b) ->
    mul_ a b

squareCircuit
  :: forall t n
   . CircuitM Fr ConstraintSystem t n
  => t n (CVar Fr Variable)
squareCircuit =
  publicInputs @Fr (Proxy @(FieldElem Fr)) >>= \a ->
    square_ a

eqCircuit
  :: forall t n
   . CircuitM Fr ConstraintSystem t n
  => t n (CVar Fr (Bool Variable))
eqCircuit = do
  publicInputs @Fr (Proxy @Inputs2) >>= \(Tuple a b) ->
    eq_ a b

invCircuit
  :: forall t n
   . CircuitM Fr ConstraintSystem t n
  => t n (CVar Fr Variable)
invCircuit =
  publicInputs @Fr (Proxy @(FieldElem Fr)) >>= \a ->
    inv_ a

divCircuit
  :: forall t n
   . CircuitM Fr ConstraintSystem t n
  => t n (CVar Fr Variable)
divCircuit =
  publicInputs @Fr (Proxy @Inputs2) >>= \(Tuple a b) ->
    div_ a b

notCircuit
  :: forall t n
   . CircuitM Fr ConstraintSystem t n
  => t n (CVar Fr (Bool Variable))
notCircuit = do
  publicInputs @Fr (Proxy @Boolean) >>= \a ->
    pure $ not_ a

type BoolInputs2 =
  Tuple
    Boolean
    Boolean

andCircuit
  :: forall t n
   . CircuitM Fr ConstraintSystem t n
  => t n (CVar Fr (Bool Variable))
andCircuit = do
  publicInputs @Fr (Proxy @BoolInputs2) >>= \(Tuple a b) ->
    and_ a b

orCircuit
  :: forall t n
   . CircuitM Fr ConstraintSystem t n
  => t n (CVar Fr (Bool Variable))
orCircuit = do
  publicInputs @Fr (Proxy @BoolInputs2) >>= \(Tuple a b) ->
    or_ a b

xorCircuit
  :: forall t n
   . CircuitM Fr ConstraintSystem t n
  => t n (CVar Fr (Bool Variable))
xorCircuit = do
  publicInputs @Fr (Proxy @BoolInputs2) >>= \(Tuple a b) ->
    xor_ a b

type IfThenElseInputs =
  Tuple3 Boolean (FieldElem Fr) (FieldElem Fr)

ifThenElseCircuit
  :: forall t n
   . CircuitM Fr ConstraintSystem t n
  => t n (CVar Fr Variable)
ifThenElseCircuit =
  publicInputs @Fr (Proxy @IfThenElseInputs) >>= \(Tuple b (Tuple t e)) ->
    ifThenElse_ b t e

intSizes :: NonEmptyArray Int
intSizes = case fromArray $ filter (\x -> x `mod` 8 == 0) (8 .. 256) of
  Nothing -> unsafeCrashWith "intSizes: impossible"
  Just x -> x

allCircuit
  :: forall t m n
   . CircuitM Fr ConstraintSystem t m
  => Reflectable n Int
  => Proxy n
  -> t m (CVar Fr (Bool Variable))
allCircuit _ =
  publicInputs @Fr (Proxy @(Vector n Boolean)) >>= \bs ->
    all_ (unVector bs)

anyCircuit
  :: forall t m n
   . CircuitM Fr ConstraintSystem t m
  => Reflectable n Int
  => Proxy n
  -> t m (CVar Fr (Bool Variable))
anyCircuit _ =
  publicInputs @Fr (Proxy @(Vector n Boolean)) >>= \bs ->
    any_ (unVector bs)

sumCircuit
  :: forall t m n
   . CircuitM Fr ConstraintSystem t m
  => Reflectable n Int
  => Proxy n
  -> t m (CVar Fr Variable)
sumCircuit _ =
  publicInputs @Fr (Proxy @(Vector n (FieldElem Fr))) >>= \bs ->
    pure $ sum_ (unVector bs)

assertNonZeroCircuit
  :: forall t n
   . CircuitM Fr ConstraintSystem t n
  => t n Unit
assertNonZeroCircuit = do
  publicInputs @Fr (Proxy @(FieldElem Fr)) >>= \a ->
    assertNonZero a

assertEqualCircuit
  :: forall t n
   . CircuitM Fr ConstraintSystem t n
  => t n Unit
assertEqualCircuit = do
  publicInputs @Fr (Proxy @Inputs2) >>= \(Tuple a b) ->
    assertEqual a b

circuitSpec
  :: forall a avar b bvar
   . ConstrainedType Fr a ConstraintSystem avar
  => ConstrainedType Fr b ConstraintSystem bvar
  => Eq b
  => Arbitrary a
  => (forall t. CircuitM Fr ConstraintSystem t Identity => t Identity bvar)
  -> (a -> b)
  -> Aff Unit
circuitSpec circuit f =
  circuitSpec' circuit f arbitrary

circuitSpec'
  :: forall a avar b bvar
   . ConstrainedType Fr a ConstraintSystem avar
  => ConstrainedType Fr b ConstraintSystem bvar
  => Eq b
  => (forall t. CircuitM Fr ConstraintSystem t Identity => t Identity bvar)
  -> (a -> b)
  -> Gen a
  -> Aff Unit
circuitSpec' circuit f g =
  let
    { constraints, solver } = un Identity $ compile (Proxy @a) circuit
    spc = un Identity <<<
      makeCircuitSpec { constraints, solver, evalConstraint: evalR1CSConstraint, f }
  in
    quickCheck $
      g <#> spc

assertionSpec
  :: forall a avar
   . ConstrainedType Fr a ConstraintSystem avar
  => Arbitrary a
  => (forall t. CircuitM Fr ConstraintSystem t Identity => t Identity Unit)
  -> (a -> Boolean)
  -> Aff Unit
assertionSpec circuit isValid =
  assertionSpec' circuit isValid arbitrary

assertionSpec'
  :: forall a avar
   . ConstrainedType Fr a ConstraintSystem avar
  => (forall t. CircuitM Fr ConstraintSystem t Identity => t Identity Unit)
  -> (a -> Boolean)
  -> Gen a
  -> Aff Unit
assertionSpec' circuit isValid g =
  let
    { constraints, solver } = un Identity $ compile (Proxy @a) circuit
    spc = un Identity <<<
      makeAssertionSpec { constraints, solver, evalConstraint: evalR1CSConstraint, isValid }
  in
    quickCheck $
      g <#> spc

fieldSpec :: Spec Unit
fieldSpec = describe "Field Circuit Specs" do

  it "mul Circuit is Valid" $
    let
      f (Tuple (FieldElem a) (FieldElem b)) = FieldElem @Fr (a * b)
    in
      circuitSpec mulCircuit f
  it "square Circuit is Valid" $
    let
      f (FieldElem a) = FieldElem @Fr (a * a)
    in
      circuitSpec squareCircuit f

  it "eq Circuit is Valid" $
    let
      f :: Tuple (FieldElem Fr) (FieldElem Fr) -> Boolean
      f = uncurry (==)
    in
      circuitSpec eqCircuit f

  it "inv Circuit is Valid" $
    let
      f (FieldElem a) =
        if a == zero then FieldElem zero
        else FieldElem @Fr (recip a)
    in
      circuitSpec invCircuit f

  it "div Circuit is Valid" $
    let
      f (Tuple (FieldElem a) (FieldElem b)) =
        if b == zero then FieldElem zero
        else FieldElem @Fr (a / b)
    in
      circuitSpec divCircuit f

  it "sum Circuit is Valid" $
    let
      f :: forall n. Vector n (FieldElem Fr) -> FieldElem Fr
      f as = FieldElem $ sum (un FieldElem <$> as)
    in
      for_ intSizes \n -> do
        reifyType n \pn ->
          circuitSpec' (sumCircuit pn) f (Vector.generator pn arbitrary)

boolSpec :: Spec Unit
boolSpec = describe "Boolean Circuit Specs" do

  it "not Circuit is Valid" $
    let

      f :: Boolean -> Boolean
      f = not
    in
      circuitSpec notCircuit f

  it "and Circuit is Valid" $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f = uncurry (&&)
    in
      circuitSpec andCircuit f

  it "or Circuit is Valid" $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f = uncurry (||)
    in
      circuitSpec orCircuit f

  it "xor Circuit is Valid" $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f (Tuple a b) = (a && not b) || (not a && b)
    in
      circuitSpec xorCircuit f

  it "ifThenElse Circuit is Valid" $
    let
      f :: Tuple3 Boolean (FieldElem Fr) (FieldElem Fr) -> FieldElem Fr
      f = uncurry3 \b t e ->
        if b then t else e
    in
      circuitSpec ifThenElseCircuit f

  it "all Circuit is Valid" $
    let
      f :: forall n. Vector n Boolean -> Boolean
      f = un Conj <<< foldMap Conj <<< unVector
    in
      for_ intSizes \n ->
        reifyType n \pn ->
          circuitSpec' (allCircuit pn) f (Vector.generator pn arbitrary)

  it "any Circuit is Valid" $
    let
      f :: forall n. Vector n Boolean -> Boolean
      f = un Disj <<< foldMap Disj <<< unVector
    in
      for_ intSizes \n ->
        reifyType n \pn ->
          circuitSpec' (anyCircuit pn) f (Vector.generator pn arbitrary)

assertSpec :: Spec Unit
assertSpec = describe "Assertion Circuit Specs" do

  it "assertNonZero Circuit is Valid" $
    let
      isValid :: FieldElem Fr -> Boolean
      isValid (FieldElem a) = a /= zero
    in
      assertionSpec assertNonZeroCircuit isValid

  it "assertEqual Circuit is Valid" $
    let
      isValid :: Tuple (FieldElem Fr) (FieldElem Fr) -> Boolean
      isValid (Tuple (FieldElem a) (FieldElem b)) = a == b
    in
      assertionSpec assertEqualCircuit isValid

unpackCircuit
  :: forall t n k
   . CircuitM Fr ConstraintSystem t n
  => Reflectable k Int
  => Proxy k
  -> t n (Vector k (CVar Fr (Bool Variable)))
unpackCircuit pk = do
  publicInputs @Fr (Proxy @(FieldElem Fr)) >>= \value ->
    unpack (reflectType pk) value >>= \bits ->
      pure $ unsafePartial $ fromJust $ toVector pk bits

packUnpackCircuit
  :: forall t n
   . CircuitM Fr ConstraintSystem t n
  => Int
  -> t n (CVar Fr Variable)
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
    for_ bitSizes \n ->
      reifyType n \pn ->
        circuitSpec' (unpackCircuit pn) (f pn) (smallFieldElem n)

  it "pack/unpack round trip is Valid" $
    for_ bitSizes \n ->
      let
        f = identity
      in
        circuitSpec' (packUnpackCircuit n) f (smallFieldElem n)