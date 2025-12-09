module Snarky.Curves.Vesta
  ( ScalarField
  , BaseField
  , G
  ) where

import Prelude

import Data.Array as Array
import Data.Function.Uncurried (Fn3, runFn3)
import Data.Maybe (Maybe(..), fromJust)
import Partial.Unsafe (unsafePartial)
import Snarky.Curves.Class (class FrModule, class WeierstrassCurve)
import Snarky.Curves.Pallas as Pallas
import Test.QuickCheck (class Arbitrary, arbitrary)

type ScalarField = Pallas.BaseField

type BaseField = Pallas.ScalarField

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

instance WeierstrassCurve BaseField G where
  curveParams _ =
    { a: _weierstrassA unit
    , b: _weierstrassB unit
    }
  toAffine x = f <$> runFn3 _toAffine Just Nothing x
    where
    f as =
      { x: unsafePartial $ fromJust $ as Array.!! 0
      , y: unsafePartial $ fromJust $ as Array.!! 1
      }

foreign import _toAffine
  :: forall a
   . Fn3
       (a -> Maybe a)
       (Maybe a)
       G
       (Maybe a)