module Snarky.Curves.Class
  ( class PrimeField
  , fromBigInt
  , toBigInt
  , modulus
  , pow
  , class FrModule
  , scalarMul
  , inverse
  , class WeierstrassCurve
  , curveParams
  , toAffine
  , class FieldSizeInBits
  , fromInt
  ) where

import Prelude

import Data.Maybe (Maybe)
import Data.Reflectable (class Reflectable)
import JS.BigInt (BigInt)
import JS.BigInt as JS.BigInt
import Test.QuickCheck (class Arbitrary)
import Type.Proxy (Proxy)

class PrimeField :: Type -> Constraint
class (Eq f, Ord f, Show f, Field f, Arbitrary f) <= PrimeField f where
  fromBigInt :: BigInt -> f
  toBigInt :: f -> BigInt
  modulus :: BigInt
  pow :: f -> BigInt -> f

fromInt :: forall f. PrimeField f => Int -> f
fromInt x = fromBigInt $ JS.BigInt.fromInt x

class FrModule :: Type -> Type -> Constraint
class (PrimeField f, Monoid g) <= FrModule f g | g -> f where
  scalarMul :: f -> g -> g
  inverse :: g -> g

class WeierstrassCurve :: Type -> Type -> Constraint
class PrimeField f <= WeierstrassCurve f g | g -> f where
  curveParams :: Proxy g -> { a :: f, b :: f }
  toAffine :: g -> Maybe { x :: f, y :: f }

class FieldSizeInBits :: Type -> Int -> Constraint
class (PrimeField f, Reflectable n Int) <= FieldSizeInBits f (n :: Int) | f -> n