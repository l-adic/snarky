module Test.Snarky.Circuit.Kimchi.Main where

import Prelude

import Effect (Effect)
import Snarky.Constraint.Kimchi (KimchiConstraint, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.Snarky.Circuit as CircuitTests
import Test.Snarky.Circuit.Kimchi.AddComplete as AddCompleteTests
import Test.Snarky.Circuit.Kimchi.EndoMul as EndoMulTests
import Test.Snarky.Circuit.Kimchi.EndoScalar as EndoScalarTests
import Test.Snarky.Circuit.Kimchi.GenericTest as GenericTests
import Test.Snarky.Circuit.Kimchi.Poseidon as PoseidonTests
import Test.Snarky.Circuit.Kimchi.VarBaseMul as VarBaseMulTests
import Test.Snarky.Constraint.Kimchi.GenericPlonk as GenericPlonkSpec
import Test.Snarky.Types.Shifted as ShiftedTests
import Test.Spec (Spec, describe)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))

main :: Effect Unit
main =
  runSpecAndExitProcess [ consoleReporter ] do
    spec

circuitSpec :: Spec Unit
circuitSpec = do
  describe "Pallas" $
    CircuitTests.spec (Proxy @Pallas.BaseField) (Proxy @(KimchiConstraint Pallas.BaseField)) eval Kimchi.postCondition Kimchi.initialState
  describe "Vesta" $
    CircuitTests.spec (Proxy @Vesta.BaseField) (Proxy @(KimchiConstraint Vesta.BaseField)) eval Kimchi.postCondition Kimchi.initialState

spec :: Spec Unit
spec = do
  circuitSpec
  GenericPlonkSpec.spec
  PoseidonTests.spec
  AddCompleteTests.spec
  GenericTests.spec
  VarBaseMulTests.spec
  EndoMulTests.spec
  EndoScalarTests.spec
  ShiftedTests.spec
