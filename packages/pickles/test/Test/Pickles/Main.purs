module Test.Pickles.Main where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Pickles.Trace as Trace
import Pickles.Types (StepField)
import Snarky.Curves.Class (fromBigInt)
import JS.BigInt as BigInt
import Test.Spec (SpecT, describe, it)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess')
import Test.Spec.Runner.Node.Config as Cfg

-- | Placeholder pickles test suite.
-- |
-- | The legacy schnorr-based test scaffolding has been removed. The new
-- | testing strategy is to reproduce, byte-for-byte, the trace of the OCaml
-- | `Simple_chain` test (mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml).
-- | The full Simple_chain analog lands in a follow-up commit.
-- |
-- | This placeholder also exercises Pickles.Trace so we can verify the
-- | env-var-gated trace logger writes a file when PICKLES_TRACE_FILE is set.
spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles" do
  it "Pickles.Trace smoke: emits a few lines when PICKLES_TRACE_FILE is set" \_ -> do
    liftEffect do
      Trace.string "smoke.message" "hello from PureScript"
      Trace.int "smoke.int" 42
      Trace.bool "smoke.bool.t" true
      Trace.bool "smoke.bool.f" false
      Trace.field "smoke.field.zero" (fromBigInt (BigInt.fromInt 0) :: StepField)
      Trace.field "smoke.field.one" (fromBigInt (BigInt.fromInt 1) :: StepField)
      Trace.field "smoke.field.large"
        (fromBigInt
          (case BigInt.fromString "1234567890123456789" of
            Just n -> n
            Nothing -> BigInt.fromInt 0) :: StepField)

main :: Effect Unit
main = runSpecAndExitProcess'
  { defaultConfig: Cfg.defaultConfig, parseCLIOptions: true }
  [ consoleReporter ]
  spec
