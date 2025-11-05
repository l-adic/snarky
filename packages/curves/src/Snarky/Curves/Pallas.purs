module Snarky.Curves.Pallas
  ( ScalarField
  )
  where

import Prelude

import Random.LCG (unSeed)
import Test.QuickCheck (class Arbitrary)
import Test.QuickCheck.Gen (stateful)

foreign import data ScalarField :: Type
foreign import zero :: Unit -> ScalarField
foreign import one :: Unit -> ScalarField
foreign import add :: ScalarField -> ScalarField -> ScalarField
foreign import mul :: ScalarField -> ScalarField -> ScalarField

fieldZero :: ScalarField
fieldZero = zero unit

fieldOne :: ScalarField  
fieldOne = one unit

fieldAdd :: ScalarField -> ScalarField -> ScalarField
fieldAdd = add

fieldMul :: ScalarField -> ScalarField -> ScalarField
fieldMul = mul

instance Semiring ScalarField where
  add = fieldAdd
  mul = fieldMul
  zero = fieldZero
  one = fieldOne

foreign import sub :: ScalarField -> ScalarField -> ScalarField

fieldSub :: ScalarField -> ScalarField -> ScalarField
fieldSub = sub

instance Ring ScalarField where
  sub = fieldSub

instance CommutativeRing ScalarField

foreign import div :: ScalarField -> ScalarField -> ScalarField

fieldDiv :: ScalarField -> ScalarField -> ScalarField
fieldDiv = div

instance EuclideanRing ScalarField where
  degree _ = 1
  div = fieldDiv
  mod _ _ = fieldZero

foreign import invert :: ScalarField -> ScalarField

fieldInvert :: ScalarField -> ScalarField
fieldInvert = invert

instance DivisionRing ScalarField where
  recip = fieldInvert

foreign import eq :: ScalarField -> ScalarField -> Boolean

fieldEq :: ScalarField -> ScalarField -> Boolean
fieldEq = eq

instance Eq ScalarField where
  eq = fieldEq

foreign import toString :: ScalarField -> String

fieldToString :: ScalarField -> String
fieldToString = toString

instance Show ScalarField where
  show = fieldToString

foreign import rand :: Int -> ScalarField

instance Arbitrary ScalarField where
  arbitrary = stateful \{newSeed} -> 
    pure $ rand $ unSeed newSeed