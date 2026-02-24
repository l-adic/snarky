module Test.Snarky.Circuit.Kimchi.Main where

import Prelude

import Effect (Effect)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiGate, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.Snarky.Circuit as CircuitTests
import Test.Snarky.Circuit.Kimchi.AddComplete as AddCompleteTests
import Test.Snarky.Circuit.Kimchi.CircuitJson as CircuitJsonTests
import Test.Snarky.Circuit.Kimchi.Debugger as DebuggerTests
import Test.Snarky.Circuit.Kimchi.EndoMul as EndoMulTests
import Test.Snarky.Circuit.Kimchi.EndoScalar as EndoScalarTests
import Test.Snarky.Circuit.Kimchi.GenericTest as GenericTests
import Test.Snarky.Circuit.Kimchi.GroupMap as GroupMapTests
import Test.Snarky.Circuit.Kimchi.Poseidon as PoseidonTests
import Test.Snarky.Circuit.Kimchi.VarBaseMul as VarBaseMulTests
import Test.Snarky.Circuit.Utils (TestConfig)
import Test.Snarky.Constraint.Kimchi.GenericPlonk as GenericPlonkSpec
import Test.Snarky.Types.Shifted as ShiftedTests
import Test.Spec (Spec, describe)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))

-- | Kimchi test configuration, shared by all Kimchi circuit tests.
kimchiTestConfig :: forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)
kimchiTestConfig = { checker: eval, postCondition: Kimchi.postCondition, initState: Kimchi.initialState }

main :: Effect Unit
main =
  runSpecAndExitProcess [ consoleReporter ] do
    spec

circuitSpec :: Spec Unit
circuitSpec = do
  describe "Pallas" $
    CircuitTests.spec (Proxy @Pallas.BaseField) kimchiTestConfig
  describe "Vesta" $
    CircuitTests.spec (Proxy @Vesta.BaseField) kimchiTestConfig

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
  GroupMapTests.spec
  CircuitJsonTests.spec
  DebuggerTests.spec
