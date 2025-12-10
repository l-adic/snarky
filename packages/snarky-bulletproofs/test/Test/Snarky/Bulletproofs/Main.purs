module Test.Snarky.Bulletproofs.Main where

import Prelude

import Effect (Effect)
import Snarky.Curves.Vesta as Vesta
import Test.Snarky.Circuit.Bulletproofs as Circuit
import Test.Snarky.Constraint.Bulletproofs as Constraint
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))

main :: Effect Unit
main =
  runSpecAndExitProcess [ consoleReporter ] do
    Circuit.spec
    Constraint.spec (Proxy @Vesta.ScalarField)