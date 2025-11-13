module Snarky.Circuit.DSL.Bits where

import Prelude

import Data.Array (foldl)
import Data.Array as Array
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import JS.BigInt as BigInt
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar, const_)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Constraint.Class (r1cs)
import Snarky.Circuit.DSL (class CircuitM, addConstraint, exists, readCVar)
import Snarky.Circuit.Types (Bool(..), Variable(..))
import Snarky.Curves.Class (class PrimeField, fromBigInt, pow, toBigInt)

unpack
  :: forall f c m n
   . CircuitM f c m n
  => PrimeField f
  => Int
  -> CVar f Variable
  -> m (Array (CVar f (Bool Variable)))
unpack nBits v = do
  bits :: Array (CVar f (Bool Variable)) <- for (Array.range 0 (nBits - 1)) \i -> exists do
    vVal <- readCVar v
    -- Extract i-th bit (LSB first)
    let
      bit =
        if (toBigInt vVal `BigInt.and` (BigInt.fromInt 1 `BigInt.shl` BigInt.fromInt i)) == BigInt.fromInt 0 then zero
        else one :: f
    pure $ bit == one

  let
    two = fromBigInt (BigInt.fromInt 2) :: f
    packingSum = foldl
      ( \acc (Tuple i bit) ->
          let
            coeff = pow two (BigInt.fromInt i)
          in
            acc `CVar.add_` CVar.scale_ coeff (coerce bit :: CVar f Variable)
      )
      (const_ zero)
      (Array.mapWithIndex Tuple bits)

  addConstraint $ r1cs { left: packingSum, right: const_ one, output: v }
  pure bits

pack
  :: forall f
   . PrimeField f
  => Array (CVar f (Bool Variable))
  -> CVar f Variable
pack bits =
  let
    two = fromBigInt (BigInt.fromInt 2) :: f
  in
    foldl
      ( \acc (Tuple i bit) ->
          let
            coeff = pow two (BigInt.fromInt i)
          in
            acc `CVar.add_` CVar.scale_ coeff (coerce bit :: CVar f Variable)
      )
      (const_ zero)
      (Array.mapWithIndex Tuple bits)