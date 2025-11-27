module Test.Snarky.Circuit.Kimchi.Main where

import Prelude

import Effect (Effect)
import Snarky.Curves.Vesta as Vesta
import Test.Snarky.Circuit.Constraint.Kimchi.GenericPlonk as GenericPlonkSpec
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
