module Test.Snarky.Circuit (spec) where

import Prelude

import Snarky.Backend.Builder (class CompileCircuit, CircuitBuilderState)
import Snarky.Backend.Compile (Checker)
import Snarky.Backend.Prover (class SolveCircuit)
import Snarky.Curves.Class (class FieldSizeInBits)
import Test.Snarky.Circuit.Assert as AssertTest
import Test.Snarky.Circuit.Bits as BitsTest
import Test.Snarky.Circuit.Boolean as BoolTest
import Test.Snarky.Circuit.CheckedType as CheckedTypeTest
import Test.Snarky.Circuit.Factors as Factors
import Test.Snarky.Circuit.Field as FieldTest
import Test.Snarky.Circuit.Utils (PostCondition)
import Test.Spec (Spec)
import Type.Proxy (Proxy)

spec
  :: forall f c c' r n
   . CompileCircuit f c c' r
  => SolveCircuit f c'
  => FieldSizeInBits f n
  => Proxy f
  -> Proxy c'
  -> Checker f c
  -> PostCondition f c r
  -> CircuitBuilderState c r
  -> Spec Unit
spec pf pc eval cbs postCondition = do
  CheckedTypeTest.spec pf
  FieldTest.spec pc eval cbs postCondition
  BoolTest.spec pc eval cbs postCondition
  AssertTest.spec pc eval cbs postCondition
  BitsTest.spec pc eval cbs postCondition
  Factors.spec pc eval cbs postCondition