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
  ) where

import Prelude

import Data.Maybe (Maybe)
import JS.BigInt (BigInt)
import Type.Proxy (Proxy)

class PrimeField :: Type -> Constraint
class (Eq f, Show f, Field f) <= PrimeField f where
  fromBigInt :: BigInt -> f
  toBigInt :: f -> BigInt
  modulus :: BigInt
  pow :: f -> BigInt -> f

class FrModule :: Type -> Type -> Constraint
class (PrimeField f, Monoid g) <= FrModule f g | g -> f where
  scalarMul :: f -> g -> g
  inverse :: g -> g

class WeierstrassCurve :: Type -> Type -> Constraint
class PrimeField f <= WeierstrassCurve f g | g -> f where
  curveParams :: Proxy g -> { a :: f, b :: f }
  toAffine :: g -> Maybe { x :: f, y :: f }