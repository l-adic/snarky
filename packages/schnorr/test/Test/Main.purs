module Test.Schnorr.Main where

import Prelude

import Effect (Effect)
import Snarky.Constraint.Kimchi (KimchiGate, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Pallas as Pallas
import Test.Data.Schnorr as DataSchnorr
import Test.Data.Schnorr.Derive as DataSchnorrDerive
import Test.Data.Schnorr.VerifyFixtures as DataSchnorrVerifyFixtures
import Test.Snarky.Circuit.Schnorr as CircuitSchnorr
import Test.Snarky.Circuit.Schnorr.Verify as CircuitSchnorrVerify
import Test.Snarky.Circuit.Utils (TestConfig)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

-- | Kimchi test config for the Pallas base field (the Schnorr verifier's
-- | native field), shared by the in-circuit verifier roundtrip test.
kimchiTestConfig
  :: TestConfig Pallas.BaseField (KimchiGate Pallas.BaseField)
       (AuxState Pallas.BaseField)
kimchiTestConfig =
  { checker: eval
  , postCondition: Kimchi.postCondition
  , initState: Kimchi.initialState
  }

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  DataSchnorr.spec
  DataSchnorrDerive.spec
  DataSchnorrVerifyFixtures.spec
  CircuitSchnorr.spec kimchiTestConfig
  CircuitSchnorrVerify.spec
