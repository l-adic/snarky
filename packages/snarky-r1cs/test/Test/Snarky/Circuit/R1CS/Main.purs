module Test.Snarky.Circuit.R1CS.Main where

import Prelude

import Effect (Effect)
import Snarky.Constraint.R1CS (R1CS, eval)
import Snarky.Curves.Vesta as Vesta
import Test.Snarky.Circuit as CircuitTests
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
  CircuitTests.spec (Proxy @Vesta.BaseField) (Proxy @(R1CS Vesta.BaseField)) eval