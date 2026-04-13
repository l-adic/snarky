module Test.Pickles.Main where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess')
import Test.Spec.Runner.Node.Config as Cfg

-- | Placeholder pickles test suite.
-- |
-- | The legacy schnorr-based test scaffolding has been removed. The new
-- | testing strategy is to reproduce, byte-for-byte, the trace of the OCaml
-- | `Simple_chain` test (mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml).
-- | The deterministic-RNG patch + trace logger + Simple_chain analog land in
-- | follow-up commits.
spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles" do
  it "placeholder — see Test.Pickles.Prove.SimpleChain (TODO)" \_ ->
    pure unit

main :: Effect Unit
main = runSpecAndExitProcess'
  { defaultConfig: Cfg.defaultConfig, parseCLIOptions: true }
  [ consoleReporter ]
  spec
