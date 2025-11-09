module Snarky.Circuit.Types (class PrimeField, fromBigInt, modulus) where

import Prelude

import JS.BigInt (BigInt)

class PrimeField :: Type -> Constraint
class (Eq f, Show f, Field f) <= PrimeField f where
  fromBigInt :: BigInt -> f
  modulus :: BigInt