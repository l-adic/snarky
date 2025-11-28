module Test.Snarky.Circuit.Kimchi.Main where

import Prelude

import Effect (Effect)
import Snarky.Constraint.Kimchi (KimchiConstraint, eval)
import Snarky.Curves.Vesta as Vesta
import Test.Snarky.Circuit as CircuitTests
import Test.Snarky.Constraint.Kimchi.GenericPlonk as GenericPlonkSpec
import Test.Spec (Spec)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))

main :: Effect Unit
main =
  runSpecAndExitProcess [ consoleReporter ] do
    spec

spec :: Spec Unit
spec = do
  GenericPlonkSpec.spec (Proxy @Vesta.ScalarField)
  CircuitTests.spec (Proxy @Vesta.BaseField) (Proxy @(KimchiConstraint Vesta.BaseField)) eval