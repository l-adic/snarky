module Test.Snarky.Circuit (spec) where

import Prelude

import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.Constraint (class BasicSystem)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Test.Snarky.Circuit.Assert as AssertTest
import Test.Snarky.Circuit.Bits as BitsTest
import Test.Snarky.Circuit.Boolean as BoolTest
import Test.Snarky.Circuit.Factors as Factors
import Test.Snarky.Circuit.Field as FieldTest
import Test.Snarky.Circuit.CheckedType as CheckedTypeTest
import Test.Spec (Spec)
import Type.Proxy (Proxy)

spec
  :: forall f c n
   . PrimeField f
  => BasicSystem f c
  => FieldSizeInBits f n
  => Proxy f
  -> Proxy c
  -> ( forall m
        . Applicative m
       => (Variable -> m f)
       -> c
       -> m Boolean
     )
  -> Spec Unit
spec pf pc eval = do
  FieldTest.spec pf pc eval
  BoolTest.spec pf pc eval
  AssertTest.spec pf pc eval
  BitsTest.spec pf pc eval
  CheckedTypeTest.spec pf
  Factors.spec pf pc eval