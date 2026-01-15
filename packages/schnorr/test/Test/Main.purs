module Test.Schnorr.Main where

import Prelude

import Effect (Effect)
import Test.Data.Schnorr as DataSchnorr
import Test.Snarky.Circuit.Schnorr as CircuitSchnorr
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  DataSchnorr.spec
  CircuitSchnorr.spec
