module Test.Snarky.Groth16.Main where

import Prelude

import Effect (Effect)
import Snarky.Curves.BN254 as BN254
import Test.Snarky.Circuit.Groth16 as Circuit
import Test.Snarky.Constraint.Groth16 as Constraint
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))

main :: Effect Unit
main =
  runSpecAndExitProcess [ consoleReporter ] do
    Circuit.spec
    Constraint.spec (Proxy @BN254.ScalarField)