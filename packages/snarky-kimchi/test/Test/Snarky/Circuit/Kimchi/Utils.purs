module Test.Snarky.Circuit.Kimchi.Utils where

import Prelude

import Data.Reflectable (class Reflectable)
import Prim.Int (class Add)
import Snarky.Circuit.DSL.Bits (packPure)
import Snarky.Circuit.Types (F(..))
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Data.Vector as Vector
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen)
import Type.Proxy (Proxy(..))

gen128BitElem :: forall f n _l. FieldSizeInBits f n => Reflectable _l Int => Add 128 _l n => Gen (F f)
gen128BitElem = do
  v <- Vector.generator (Proxy @128) arbitrary
  let v' = v `Vector.append` (Vector.generate $ const false)
  pure $ F $ packPure v'