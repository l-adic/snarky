module Snarky.Test.Circuit.Circuit
  ( spec
  ) where

import Prelude

import Data.Array (foldMap, foldl)
import Data.Array as Array
import Data.Foldable (for_, sum)
import Data.Identity (Identity(..))
import Data.Int (pow)
import Data.Maybe (fromJust)
import Data.Monoid.Conj (Conj(..))
import Data.Monoid.Disj (Disj(..))
import Data.Newtype (un)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Traversable (sequence)
import Data.Tuple (Tuple(..), uncurry)
import Data.Tuple.Nested (Tuple3, uncurry3)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Snarky.Circuit.CVar (CVar)
import Snarky.Circuit.Compile (Solver, compile, makeAssertionSpec, makeCircuitSpec, makeSolver)
import Snarky.Circuit.Constraint (R1CS, evalR1CSConstraint)
import Snarky.Circuit.DSL (class CircuitM)
import Snarky.Circuit.DSL.Assert (assertEqual, assertNonZero)
import Snarky.Circuit.DSL.Bits (pack, unpack)
import Snarky.Circuit.DSL.Boolean (all_, and_, any_, ifThenElse_, not_, or_, xor_)
import Snarky.Circuit.DSL.Field (div_, eq_, inv_, mul_, square_, sum_)
import Snarky.Circuit.Types (class ConstrainedType, Bool, FieldElem(..), Variable)
import Snarky.Curves.BN254 as BN254
import Snarky.Curves.Class (fromBigInt, toBigInt)
import Snarky.Data.Vector (Vector, toVector, unVector)
import Snarky.Data.Vector as Vector
import Test.QuickCheck (class Arbitrary, arbitrary, quickCheck')
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

type FieldInput = FieldElem Fr

type FieldInputs2 =
  Tuple
    (FieldElem Fr)
    (FieldElem Fr)

type FieldInputs10 =
  Vector 10 (FieldElem Fr)

type BoolInputs2 =
  Tuple
    Boolean
    Boolean

type BoolInputs10 =
  Vector 10 Boolean

type IfThenElseInputs =
  Tuple3 Boolean (FieldElem Fr) (FieldElem Fr)

type UnpackOutputs16 =
  Vector 16 Boolean

circuitSpec
  :: forall a avar b bvar
   . ConstrainedType Fr a ConstraintSystem avar
  => ConstrainedType Fr b ConstraintSystem bvar
  => Eq b
  => Arbitrary a
  => Array ConstraintSystem
  -> Solver Fr a b
  -> (a -> b)
  -> Aff Unit
circuitSpec constraints solver f =
  circuitSpec' constraints solver f arbitrary

circuitSpec'
  :: forall a avar b bvar
   . ConstrainedType Fr a ConstraintSystem avar
  => ConstrainedType Fr b ConstraintSystem bvar
  => Eq b
  => Array ConstraintSystem
  -> Solver Fr a b
  -> (a -> b)
  -> Gen a
  -> Aff Unit
circuitSpec' constraints solver f g = liftEffect $
  let
    spc = un Identity <<<
      makeCircuitSpec { constraints, solver, evalConstraint: evalR1CSConstraint, f }
  in
    quickCheck' 2 $
      g <#> spc

assertionSpec
  :: forall a avar
   . ConstrainedType Fr a ConstraintSystem avar
  => Arbitrary a
  => Array ConstraintSystem
  -> Solver Fr a Unit
  -> (a -> Boolean)
  -> Aff Unit
assertionSpec constraints solver isValid =
  assertionSpec' constraints solver isValid arbitrary

assertionSpec'
  :: forall a avar
   . ConstrainedType Fr a ConstraintSystem avar
  => Array ConstraintSystem
  -> Solver Fr a Unit
  -> (a -> Boolean)
  -> Gen a
  -> Aff Unit
assertionSpec' constraints solver isValid g =
  let
    spc = un Identity <<<
      makeAssertionSpec { constraints, solver, evalConstraint: evalR1CSConstraint, isValid }
  in
    quickCheck $
      g <#> spc

fieldSpec :: Spec Unit
fieldSpec = describe "Field Circuit Specs" do

  it "mul Circuit is Valid" $
    let
      f (Tuple (FieldElem a) (FieldElem b)) = FieldElem (a * b)
      solver = makeSolver (Proxy @ConstraintSystem) (uncurry mul_)
      { constraints } = un Identity $
        compile
          (Proxy @FieldInputs2)
          (Proxy @FieldInput)
          (uncurry mul_)
    in
      circuitSpec constraints solver f

  it "square Circuit is Valid" $
    let
      f (FieldElem a) = FieldElem (a * a)
      solver = makeSolver (Proxy @ConstraintSystem) square_
      { constraints } = un Identity $
        compile
          (Proxy @FieldInput)
          (Proxy @FieldInput)
          square_
    in
      circuitSpec constraints solver f

  it "eq Circuit is Valid" $
    let
      f :: Tuple (FieldElem Fr) (FieldElem Fr) -> Boolean
      f = uncurry (==)
      solver = makeSolver (Proxy @ConstraintSystem) (uncurry eq_)
      { constraints } = un Identity $
        compile
          (Proxy @FieldInputs2)
          (Proxy @Boolean)
          (uncurry eq_)
    in
      circuitSpec constraints solver f

  it "inv Circuit is Valid" $
    let
      f (FieldElem a) =
        if a == zero then FieldElem zero
        else FieldElem @Fr (recip a)
      solver = makeSolver (Proxy @ConstraintSystem) inv_
      { constraints } = un Identity $
        compile
          (Proxy @FieldInput)
          (Proxy @FieldInput)
          inv_
    in
      circuitSpec constraints solver f

  it "div Circuit is Valid" $
    let
      f (Tuple (FieldElem a) (FieldElem b)) =
        if b == zero then FieldElem zero
        else FieldElem @Fr (a / b)
      solver = makeSolver (Proxy @ConstraintSystem) (uncurry div_)
      { constraints } = un Identity $
        compile
          (Proxy @FieldInputs2)
          (Proxy @FieldInput)
          (uncurry div_)
    in
      circuitSpec constraints solver f

  it "sum Circuit is Valid" $
    let
      f :: Vector 10 (FieldElem Fr) -> FieldElem Fr
      f as = FieldElem $ sum (un FieldElem <$> as)
      solver = makeSolver (Proxy @ConstraintSystem) (pure <<< sum_ <<< unVector)
      { constraints } = un Identity $
        compile
          (Proxy @FieldInputs10)
          (Proxy @FieldInput)
          (pure <<< sum_ <<< unVector)
    in
      circuitSpec' constraints solver f (Vector.generator (Proxy @10) arbitrary)

boolSpec :: Spec Unit
boolSpec = describe "Boolean Circuit Specs" do

  it "not Circuit is Valid" $
    let

      f :: Boolean -> Boolean
      f = not
      solver = makeSolver (Proxy @ConstraintSystem) (pure <<< not_)
      { constraints } = un Identity $
        compile
          (Proxy @Boolean)
          (Proxy @Boolean)
          (pure <<< not_)
    in
      circuitSpec constraints solver f

  it "and Circuit is Valid" $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f = uncurry (&&)
      solver = makeSolver (Proxy @ConstraintSystem) (uncurry and_)
      { constraints } = un Identity $
        compile
          (Proxy @BoolInputs2)
          (Proxy @Boolean)
          (uncurry and_)
    in
      circuitSpec constraints solver f

  it "or Circuit is Valid" $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f = uncurry (||)
      solver = makeSolver (Proxy @ConstraintSystem) (uncurry or_)
      { constraints } = un Identity $
        compile
          (Proxy @BoolInputs2)
          (Proxy @Boolean)
          (uncurry or_)
    in
      circuitSpec constraints solver f

  it "xor Circuit is Valid" $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f (Tuple a b) = (a && not b) || (not a && b)
      solver = makeSolver (Proxy @ConstraintSystem) (uncurry xor_)
      { constraints } = un Identity $
        compile
          (Proxy @BoolInputs2)
          (Proxy @Boolean)
          (uncurry xor_)
    in
      circuitSpec constraints solver f

  it "ifThenElse Circuit is Valid" $
    let
      f :: Tuple3 Boolean (FieldElem Fr) (FieldElem Fr) -> FieldElem Fr
      f = uncurry3 \b t e ->
        if b then t else e
      solver = makeSolver (Proxy @ConstraintSystem) (uncurry3 ifThenElse_)
      { constraints } = un Identity $
        compile
          (Proxy @IfThenElseInputs)
          (Proxy @FieldInput)
          (uncurry3 ifThenElse_)
    in
      circuitSpec constraints solver f

  it "all Circuit is Valid" $
    let
      f :: forall n. Vector n Boolean -> Boolean
      f = un Conj <<< foldMap Conj <<< unVector
      solver = makeSolver (Proxy @ConstraintSystem) (all_ <<< unVector)
      { constraints } = un Identity $
        compile
          (Proxy @BoolInputs10)
          (Proxy @Boolean)
          (all_ <<< unVector)
    in
      circuitSpec' constraints solver f (Vector.generator (Proxy @10) arbitrary)

  it "any Circuit is Valid" $
    let
      f :: forall n. Vector n Boolean -> Boolean
      f = un Disj <<< foldMap Disj <<< unVector
      solver = makeSolver (Proxy @ConstraintSystem) (any_ <<< unVector)
      { constraints } = un Identity $
        compile
          (Proxy @BoolInputs10)
          (Proxy @Boolean)
          (any_ <<< unVector)
    in
      circuitSpec' constraints solver f (Vector.generator (Proxy @10) arbitrary)

assertSpec :: Spec Unit
assertSpec = describe "Assertion Circuit Specs" do

  it "assertNonZero Circuit is Valid" $
    let
      isValid :: FieldElem Fr -> Boolean
      isValid (FieldElem a) = a /= zero
      solver = makeSolver (Proxy @ConstraintSystem) assertNonZero
      { constraints } = un Identity $
        compile
          (Proxy @FieldInput)
          (Proxy @Unit)
          assertNonZero
    in
      assertionSpec constraints solver isValid

  it "assertEqual Circuit is Valid" $
    let
      isValid :: Tuple (FieldElem Fr) (FieldElem Fr) -> Boolean
      isValid (Tuple (FieldElem a) (FieldElem b)) = a == b
      solver = makeSolver (Proxy @ConstraintSystem) (uncurry assertEqual)
      { constraints } = un Identity $
        compile
          (Proxy @FieldInputs2)
          (Proxy @Unit)
          (uncurry assertEqual)
    in
      assertionSpec constraints solver isValid

unpackCircuit
  :: forall t n k
   . CircuitM Fr ConstraintSystem t n
  => Reflectable k Int
  => Proxy k
  -> CVar Fr Variable
  -> t n (Vector k (CVar Fr (Bool Variable)))
unpackCircuit pk value = do
  unpack (reflectType pk) value >>= \bits ->
    pure $ unsafePartial $ fromJust $ toVector pk bits

packUnpackCircuit
  :: forall t n
   . CircuitM Fr ConstraintSystem t n
  => Int
  -> CVar Fr Variable
  -> t n (CVar Fr Variable)
packUnpackCircuit nBits value = do
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
  it "unpack Circuit is Valid" $
    let
      f :: forall k. Reflectable k Int => Proxy k -> FieldElem Fr -> Vector k Boolean
      f pk (FieldElem v) =
        let
          bitCount = reflectType pk
          toBit i = (toBigInt v `BigInt.and` (BigInt.fromInt 1 `BigInt.shl` BigInt.fromInt i)) /= zero
          bits = map toBit (Array.range 0 (bitCount - 1))
        in
          unsafePartial $ fromJust $ toVector pk bits
      solver = makeSolver (Proxy @ConstraintSystem) (unpackCircuit (Proxy @16))
      { constraints } = un Identity $
        compile
          (Proxy @FieldInput)
          (Proxy @UnpackOutputs16)
          (unpackCircuit (Proxy @16))
    in
      circuitSpec' constraints solver (f (Proxy @16)) (smallFieldElem 16)

  it "pack/unpack round trip is Valid" $
    for_ bitSizes \n ->
      let
        f = identity
        solver = makeSolver (Proxy @ConstraintSystem) (packUnpackCircuit n)
        { constraints } = un Identity $
          compile
            (Proxy @FieldInput)
            (Proxy @(FieldElem Fr))
            (packUnpackCircuit n)
      in
        circuitSpec' constraints solver f (smallFieldElem n)