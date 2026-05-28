module Test.Schnorr.Main where

import Prelude

import Effect (Effect)
import Snarky.Constraint.Kimchi (eval)
import Snarky.Constraint.Kimchi as Kimchi
import Test.Data.Schnorr as DataSchnorr
import Test.Data.Schnorr.Derive as DataSchnorrDerive
import Test.Snarky.Circuit.Schnorr as CircuitSchnorr
import Test.Snarky.Circuit.Schnorr.Verify as CircuitSchnorrVerify
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  DataSchnorr.spec
  DataSchnorrDerive.spec
  CircuitSchnorr.spec unit
  CircuitSchnorrVerify.spec
