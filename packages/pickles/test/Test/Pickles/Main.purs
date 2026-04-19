module Test.Pickles.Main where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Test.Pickles.Prove.NoRecursionReturn as NoRecursionReturn
import Test.Pickles.Prove.SimpleChain as SimpleChain
import Test.Spec (SpecT)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess')
import Test.Spec.Runner.Node.Config as Cfg

-- | Pickles test suite.
-- |
-- | The legacy schnorr-based test scaffolding has been removed. The new
-- | testing strategy is to reproduce, byte-for-byte, the trace of the OCaml
-- | `Simple_chain` test (mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml)
-- | as captured by `mina/.../dump_simple_chain.exe` and saved at
-- | `packages/pickles/test/fixtures/simple_chain_base_case.trace`. The
-- | PureScript-side analog at Test.Pickles.Prove.SimpleChain emits a
-- | matching trace via Pickles.Trace; the two trace files are then diffed
-- | to verify pickles correctness end-to-end.
spec :: SpecT Aff Unit Aff Unit
spec = do
  SimpleChain.spec
  NoRecursionReturn.spec

main :: Effect Unit
main = runSpecAndExitProcess'
  { defaultConfig: Cfg.defaultConfig, parseCLIOptions: true }
  [ consoleReporter ]
  spec
