module Test.Snarky.Circuit (spec) where

import Prelude

import Snarky.Backend.Builder (class CompileCircuit)
import Snarky.Backend.Prover (class SolveCircuit)
import Snarky.Curves.Class (class FieldSizeInBits)
import Test.Snarky.Circuit.Assert as AssertTest
import Test.Snarky.Circuit.Bits as BitsTest
import Test.Snarky.Circuit.Boolean as BoolTest
import Test.Snarky.Circuit.CheckedType as CheckedTypeTest
import Test.Snarky.Circuit.Factors as Factors
import Test.Snarky.Circuit.Field as FieldTest
import Test.Snarky.Circuit.Utils (TestConfig)
import Test.Spec (Spec)
import Type.Proxy (Proxy)

spec
  :: forall f c c' r n
   . CompileCircuit f c c' r
  => SolveCircuit f c'
  => FieldSizeInBits f n
  => Proxy f
  -> TestConfig f c r
  -> Spec Unit
spec pf cfg = do
  CheckedTypeTest.spec pf
  FieldTest.spec cfg
  BoolTest.spec cfg
  AssertTest.spec cfg
  BitsTest.spec cfg
  Factors.spec cfg