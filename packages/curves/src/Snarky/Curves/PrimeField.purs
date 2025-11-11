module Snarky.Curves.Types (class PrimeField, fromBigInt, toBigInt, modulus, pow) where

import Prelude

import JS.BigInt (BigInt)

class PrimeField :: Type -> Constraint
class (Eq f, Show f, Field f) <= PrimeField f where
  fromBigInt :: BigInt -> f
  toBigInt :: f -> BigInt
  modulus :: BigInt
  pow :: f -> BigInt -> f