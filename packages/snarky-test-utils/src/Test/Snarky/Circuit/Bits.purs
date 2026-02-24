module Test.Snarky.Circuit.Bits (spec) where

import Prelude

import Control.Monad.Gen as Gen
import Data.Array (foldl)
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Fin (getFinite)
import Data.Identity (Identity)
import Data.Int (pow)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Traversable (sequence)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, generate)
import JS.BigInt as BigInt
import Snarky.Backend.Builder (class CompileCircuit)
import Snarky.Backend.Prover (class SolveCircuit)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, Snarky, pack_, unpack_)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromBigInt, toBigInt)
import Test.QuickCheck.Gen (Gen, chooseInt)
import Test.Snarky.Circuit.Utils (TestConfig, circuitTest', satisfied)
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
  :: forall t m n f c
   . CircuitM f c t m
  => FieldSizeInBits f n
  => FVar f
  -> Snarky c t m (FVar f)
packUnpackCircuit value = do
  unpack_ value (Proxy @n) >>= \bits ->
    pure $ pack_ bits

bitSizes :: Int -> Gen Int
bitSizes mx = Gen.chooseInt 1 mx

spec
  :: forall f n c c' r
   . CompileCircuit f c c' r
  => SolveCircuit f c'
  => FieldSizeInBits f n
  => TestConfig f c r
  -> Spec Unit
spec cfg = describe "Bits Circuit Specs" do
  it "unpack Circuit is Valid" $ void $
    let
      f :: forall k. Reflectable k Int => F f -> Vector k Boolean
      f (F v) =
        let
          toBit i = (toBigInt v `BigInt.and` (BigInt.fromInt 1 `BigInt.shl` BigInt.fromInt i)) /= zero
        in
          generate (toBit <<< getFinite)

      circuit :: forall t. CircuitM f c' t Identity => FVar f -> Snarky c' t Identity (Vector n (BoolVar f))
      circuit = \v -> unpack_ v (Proxy @n)
    in
      circuitTest' @f 100
        cfg
        (NEA.singleton { testFunction: satisfied f, gen: bitSizes (reflectType $ Proxy @n) >>= smallFieldElem })
        circuit

  it "pack/unpack round trip is Valid" $ void $
    let
      circuit :: forall t. CircuitM f c' t Identity => FVar f -> Snarky c' t Identity (FVar f)
      circuit = packUnpackCircuit
    in
      circuitTest' @f 100
        cfg
        (NEA.singleton { testFunction: satisfied identity, gen: bitSizes (reflectType $ Proxy @n) >>= smallFieldElem })
        circuit
