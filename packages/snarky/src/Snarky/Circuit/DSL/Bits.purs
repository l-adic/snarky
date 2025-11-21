module Snarky.Circuit.DSL.Bits where

import Prelude

import Data.FunctorWithIndex (mapWithIndex)
import Data.Reflectable (class Reflectable)
import Data.Traversable (foldl)
import Data.Tuple (Tuple(..))
import JS.BigInt as BigInt
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar, const_)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Constraint.Class (class R1CSSystem, r1cs)
import Snarky.Circuit.DSL.Monad (class CircuitM, addConstraint, exists, readCVar)
import Snarky.Circuit.Types (Bool(..), Variable(..))
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromBigInt, pow, toBigInt)
import Snarky.Data.Fin (getFinite)
import Snarky.Data.Vector (Vector, generateA)

-- NB: LSB first
unpack
  :: forall f c t m n
   . CircuitM f c t m
  => PrimeField f
  => FieldSizeInBits f n
  => CVar f Variable
  -> t m (Vector n (CVar f (Bool Variable)))
unpack v = do
  bits :: Vector n (CVar f (Bool Variable)) <- generateA \i -> exists @f @c do
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
            acc `CVar.add_` CVar.scale_ coeff (coerce bit :: CVar f Variable)
      )
      (const_ zero)
      (mapWithIndex Tuple bits)

  addConstraint $ r1cs { left: packingSum, right: const_ one, output: v }
  pure bits

pack
  :: forall f n
   . PrimeField f
  => Reflectable n Int
  => Vector n (CVar f (Bool Variable))
  -> CVar f Variable
pack bits =
  let
    two = fromBigInt (BigInt.fromInt 2) :: f
  in
    foldl
      ( \acc (Tuple i bit) ->
          let
            coeff = pow two (BigInt.fromInt $ getFinite i)
          in
            acc `CVar.add_` CVar.scale_ coeff (coerce bit :: CVar f Variable)
      )
      (const_ zero)
      (mapWithIndex Tuple bits)