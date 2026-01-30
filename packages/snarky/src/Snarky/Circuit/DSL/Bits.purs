module Snarky.Circuit.DSL.Bits where

import Prelude

import Data.Fin (getFinite)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Reflectable (class Reflectable)
import Data.Traversable (foldl)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, generateA)
import Data.Vector as Vector
import JS.BigInt as BigInt
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.DSL.Monad (class CircuitM, Snarky, addConstraint, exists, readCVar)
import Snarky.Circuit.Types (Bool(..), BoolVar, FVar)
import Snarky.Constraint.Basic (r1cs)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromBigInt, pow, toBigInt)

-- NB: LSB first
unpack_
  :: forall f c t m n
   . CircuitM f c t m
  => FieldSizeInBits f n
  => FVar f
  -> Snarky c t m (Vector n (BoolVar f))
unpack_ v = do
  bits :: Vector n (BoolVar f) <- generateA \i -> exists do
    vVal <- readCVar v
    let
      bit =
        if (toBigInt vVal `BigInt.and` (BigInt.fromInt 1 `BigInt.shl` BigInt.fromInt (getFinite i))) == BigInt.fromInt 0 then zero
        else one :: f
    pure $ bit == one

  let
    two = fromBigInt (BigInt.fromInt 2) :: f
    packingSum = foldl
      ( \acc (Tuple i bit) ->
          let
            coeff = pow two (BigInt.fromInt $ getFinite i)
          in
            acc `CVar.add_` CVar.scale_ coeff (coerce bit :: FVar f)
      )
      (const_ zero)
      (mapWithIndex Tuple bits)

  addConstraint $ r1cs { left: packingSum, right: const_ one, output: v }
  pure bits

pack_
  :: forall f n
   . PrimeField f
  => Reflectable n Int
  => Vector n (BoolVar f)
  -> FVar f
pack_ bits =
  let
    two = fromBigInt (BigInt.fromInt 2) :: f
  in
    foldl
      ( \acc (Tuple i bit) ->
          let
            coeff = pow two (BigInt.fromInt $ getFinite i)
          in
            acc `CVar.add_` CVar.scale_ coeff (coerce bit :: FVar f)
      )
      (const_ zero)
      (mapWithIndex Tuple bits)

unpackPure :: forall f @n. FieldSizeInBits f n => f -> Vector n Boolean
unpackPure x = Vector.generate \i ->
  if (toBigInt x `BigInt.and` (BigInt.fromInt 1 `BigInt.shl` BigInt.fromInt (getFinite i))) == BigInt.fromInt 0 then false
  else true

packPure :: forall f n. PrimeField f => Reflectable n Int => Vector n Boolean -> f
packPure bs = foldlWithIndex
  ( \i acc bit ->
      let
        coeff = pow two (BigInt.fromInt $ getFinite i)
      in
        acc + coeff * (if bit then one else zero)
  )
  zero
  bs
  where
  two = one + one
