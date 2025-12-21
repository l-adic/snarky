module Test.Snarky.Circuit.Kimchi.Main where

import Prelude

import Effect (Effect)
import Snarky.Constraint.Kimchi (KimchiConstraint, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Vesta as Vesta
import Test.Snarky.Circuit as CircuitTests
import Test.Snarky.Circuit.Kimchi.Poseidon as PoseidonTests
import Test.Snarky.Constraint.Kimchi.GenericPlonk as GenericPlonkSpec
import Test.Spec (Spec)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))
import Test.Snarky.Circuit.Kimchi.AddComplete as AddCompleteTests

main :: Effect Unit
main =
  runSpecAndExitProcess [ consoleReporter ] do
    spec

spec :: Spec Unit
spec = do
  GenericPlonkSpec.spec (Proxy @Vesta.ScalarField)
  CircuitTests.spec (Proxy @Vesta.BaseField) (Proxy @(KimchiConstraint Vesta.BaseField)) eval Kimchi.initialState
  PoseidonTests.spec
  AddCompleteTests.spec (Proxy @Vesta.G) (Proxy @(KimchiConstraint Vesta.BaseField))  
  AddCompleteTests.spec2