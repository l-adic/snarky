module Snarky.Curves.Pallas
  ( ScalarField
  ) where

import Prelude

import JS.BigInt (BigInt)
import Snarky.Curves.Types (class PrimeField)
import Test.QuickCheck (class Arbitrary, arbitrary)

foreign import data ScalarField :: Type
foreign import _zero :: Unit -> ScalarField
foreign import _one :: Unit -> ScalarField
foreign import _add :: ScalarField -> ScalarField -> ScalarField
foreign import _mul :: ScalarField -> ScalarField -> ScalarField

instance Semiring ScalarField where
  add = _add
  mul = _mul
  zero = _zero unit
  one = _one unit

foreign import _sub :: ScalarField -> ScalarField -> ScalarField

instance Ring ScalarField where
  sub = _sub

instance CommutativeRing ScalarField

foreign import _div :: ScalarField -> ScalarField -> ScalarField

instance EuclideanRing ScalarField where
  degree _ = 1
  div = _div
  mod _ _ = zero

foreign import _invert :: ScalarField -> ScalarField

instance DivisionRing ScalarField where
  recip = _invert

foreign import _eq :: ScalarField -> ScalarField -> Boolean

instance Eq ScalarField where
  eq = _eq

foreign import _toString :: ScalarField -> String

instance Show ScalarField where
  show = _toString

foreign import _rand :: Int -> ScalarField
foreign import _fromBigInt :: BigInt -> ScalarField
foreign import _toBigInt :: ScalarField -> BigInt
foreign import _modulus :: Unit -> BigInt
foreign import _pow :: ScalarField -> BigInt -> ScalarField

instance Arbitrary ScalarField where
  arbitrary = _rand <$> arbitrary

instance PrimeField ScalarField where
  fromBigInt = _fromBigInt
  toBigInt = _toBigInt
  modulus = _modulus unit
  pow = _pow
