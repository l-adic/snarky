module Test.Pickles.Main where

import Prelude

import Effect (Effect)
import Test.Pickles.E2E as E2E
import Test.Pickles.Linearization as Linearization
import Test.Pickles.Permutation as Permutation
import Test.Pickles.ScalarChallenge as ScalarChallenge
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

main :: Effect Unit
main =
  runSpecAndExitProcess [ consoleReporter ] do
    E2E.spec
    Linearization.spec
    Permutation.spec
    ScalarChallenge.spec
