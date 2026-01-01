module Test.Snarky.Circuit (spec) where

import Prelude

import Snarky.Backend.Builder (class Finalizer, CircuitBuilderState, CircuitBuilderT)
import Snarky.Backend.Prover (ProverT)
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.DSL.Monad (class ConstraintM)
import Snarky.Constraint.Basic (class BasicSystem)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Test.Snarky.Circuit.Assert as AssertTest
import Test.Snarky.Circuit.Bits as BitsTest
import Test.Snarky.Circuit.Boolean as BoolTest
import Test.Snarky.Circuit.CheckedType as CheckedTypeTest
import Test.Snarky.Circuit.Factors as Factors
import Test.Snarky.Circuit.Field as FieldTest
import Test.Spec (Spec)
import Type.Proxy (Proxy)

spec
  :: forall f c c' r n
   . PrimeField f
  => BasicSystem f c'
  => ConstraintM (CircuitBuilderT c r) c'
  => Finalizer c r
  => ConstraintM (ProverT f) c'
  => FieldSizeInBits f n
  => Proxy f
  -> Proxy c'
  -> ( forall m
        . Applicative m
       => (Variable -> m f)
       -> c
       -> m Boolean
     )
  -> CircuitBuilderState c r
  -> Spec Unit
spec pf pc eval cbs = do
  CheckedTypeTest.spec pf
  FieldTest.spec pf pc eval cbs
  BoolTest.spec pf pc eval cbs
  AssertTest.spec pf pc eval cbs
  BitsTest.spec pf pc eval cbs
  Factors.spec pf pc eval cbs