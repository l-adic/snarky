module Test.Main where

import Prelude

import Effect (Effect)
import Effect.Aff (launchAff_)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner (runSpec)

import Test.Pallas as PallasTest
import Test.Vesta as VestaTest
import Test.BN254 as BN254Test

main :: Effect Unit
main = launchAff_ $ runSpec [ consoleReporter ] do
  PallasTest.spec
  VestaTest.spec
  BN254Test.spec