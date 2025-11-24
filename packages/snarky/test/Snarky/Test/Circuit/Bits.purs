module Test.Snarky.Circuit.Bits (spec) where

import Prelude

import Control.Monad.Gen as Gen
import Data.Array (foldl)
import Data.Array as Array
import Data.Int (pow)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Traversable (sequence)
import Data.Tuple (Tuple(..))
import JS.BigInt as BigInt
import Snarky.Circuit.Compile (compilePure, makeSolver)
import Snarky.Circuit.Constraint (R1CS, evalR1CSConstraint)
import Snarky.Circuit.DSL (class CircuitM, FVar, pack_, unpack_, F(..), Snarky)
import Snarky.Circuit.TestUtils (circuitSpecPure', satisfied)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromBigInt, toBigInt)
import Snarky.Data.Fin (getFinite)
import Snarky.Data.Vector (Vector, generate)
import Test.QuickCheck (class Arbitrary)
import Test.QuickCheck.Gen (Gen, chooseInt)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

smallFieldElem :: forall f. PrimeField f => Int -> Gen (F f)
smallFieldElem bitCount = do
  if bitCount <= 31 then do
    -- For small bit counts, generate directly
    n <- chooseInt 0 $ (2 `pow` bitCount) - 1
    pure $ F $ fromBigInt $ BigInt.fromInt n
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
    pure $ F $ fromBigInt $ combined `BigInt.and` mask

packUnpackCircuit
  :: forall t m n f
   . CircuitM f (R1CS f) t m
  => FieldSizeInBits f n
  => FVar f
  -> Snarky t m (FVar f)
packUnpackCircuit value = do
  unpack_ value >>= \bits ->
    pure $ pack_ bits

bitSizes :: Int -> Gen Int
bitSizes mx = Gen.chooseInt 1 mx

spec :: forall f n. FieldSizeInBits f n => Arbitrary f => Proxy f -> Spec Unit
spec _ = describe "Bits Circuit Specs" do
  it "unpack Circuit is Valid" $
    let

      f :: forall k. Reflectable k Int => F f -> Vector k Boolean
      f (F v) =
        let
          toBit i = (toBigInt v `BigInt.and` (BigInt.fromInt 1 `BigInt.shl` BigInt.fromInt i)) /= zero
        in
          generate (toBit <<< getFinite)
      solver = makeSolver (Proxy @(R1CS f)) unpack_
      { constraints } =
        compilePure
          (Proxy @(F f))
          (Proxy @(Vector n Boolean))
          unpack_
    in
      circuitSpecPure' constraints evalR1CSConstraint solver (satisfied f) (bitSizes (reflectType $ Proxy @n) >>= smallFieldElem)

  it "pack/unpack round trip is Valid" $
    let
      f = identity
      solver = makeSolver (Proxy @(R1CS f)) (packUnpackCircuit)
      { constraints } =
        compilePure
          (Proxy @(F f))
          (Proxy @(F f))
          (packUnpackCircuit)
    in
      circuitSpecPure' constraints evalR1CSConstraint solver (satisfied f) (bitSizes (reflectType $ Proxy @n) >>= smallFieldElem)