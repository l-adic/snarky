module Test.Snarky.Circuit.Main where

import Prelude

import Effect (Effect)
import Snarky.Test.Circuit.CVar as CVarTests
import Snarky.Test.Circuit.Circuit as CircuitTests
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  CVarTests.spec
  CircuitTests.spec