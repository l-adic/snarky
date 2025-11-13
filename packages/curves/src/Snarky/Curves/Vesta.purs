module Snarky.Curves.Vesta
  ( ScalarField
  , BaseField
  , G
  ) where

import Prelude

import JS.BigInt (BigInt)
import Snarky.Curves.Class (class PrimeField, class WierstraussCurve, class FrModule)
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

-- BaseField type and instances
foreign import data BaseField :: Type
foreign import _baseFieldZero :: Unit -> BaseField
foreign import _baseFieldOne :: Unit -> BaseField
foreign import _baseFieldAdd :: BaseField -> BaseField -> BaseField
foreign import _baseFieldMul :: BaseField -> BaseField -> BaseField
foreign import _baseFieldSub :: BaseField -> BaseField -> BaseField
foreign import _baseFieldDiv :: BaseField -> BaseField -> BaseField
foreign import _baseFieldInvert :: BaseField -> BaseField
foreign import _baseFieldEq :: BaseField -> BaseField -> Boolean
foreign import _baseFieldToString :: BaseField -> String
foreign import _baseFieldFromString :: String -> BaseField
foreign import _baseFieldRand :: Int -> BaseField
foreign import _baseFieldFromBigInt :: BigInt -> BaseField
foreign import _baseFieldToBigInt :: BaseField -> BigInt
foreign import _baseFieldModulus :: Unit -> BigInt
foreign import _baseFieldPow :: BaseField -> BigInt -> BaseField

instance Semiring BaseField where
  add = _baseFieldAdd
  mul = _baseFieldMul
  zero = _baseFieldZero unit
  one = _baseFieldOne unit

instance Ring BaseField where
  sub = _baseFieldSub

instance CommutativeRing BaseField

instance EuclideanRing BaseField where
  degree _ = 1
  div = _baseFieldDiv
  mod _ _ = zero

instance DivisionRing BaseField where
  recip = _baseFieldInvert

instance Eq BaseField where
  eq = _baseFieldEq

instance Show BaseField where
  show = _baseFieldToString

instance Arbitrary BaseField where
  arbitrary = _baseFieldRand <$> arbitrary

instance PrimeField BaseField where
  fromBigInt = _baseFieldFromBigInt
  toBigInt = _baseFieldToBigInt
  modulus = _baseFieldModulus unit
  pow = _baseFieldPow

-- Group Element type
foreign import data G :: Type
foreign import _groupAdd :: G -> G -> G
foreign import _groupIdentity :: Unit -> G
foreign import _groupRand :: Int -> G
foreign import _groupEq :: G -> G -> Boolean
foreign import _groupToString :: G -> String
foreign import _groupNeg :: G -> G
foreign import _groupScale :: ScalarField -> G -> G
foreign import _weierstrassA :: Unit -> BaseField
foreign import _weierstrassB :: Unit -> BaseField

instance Semigroup G where
  append = _groupAdd

instance Monoid G where
  mempty = _groupIdentity unit

instance Eq G where
  eq = _groupEq

instance Show G where
  show = _groupToString

instance Arbitrary G where
  arbitrary = _groupRand <$> arbitrary

instance FrModule ScalarField G where
  scalarMul = _groupScale
  inverse = _groupNeg

instance WierstraussCurve BaseField G where
  curveParams _ =
    { a: _weierstrassA unit
    , b: _weierstrassB unit
    }