module Test.Pickles.Main where

import Prelude

import Colog (LoggerT, Message, richMessageStdout, usingLoggerT)
import Effect (Effect)
import Effect.Aff (Aff)
import Test.Pickles.Prove.Chunks2 as Chunks2
import Test.Pickles.Prove.Chunks4 as Chunks4
import Test.Pickles.Prove.Codecs as Codecs
import Test.Pickles.Prove.CompileValidation as CompileValidation
import Test.Pickles.Prove.HeterogeneousPrevs as HeterogeneousPrevs
import Test.Pickles.Prove.NoRecursionReturn as NoRecursionReturn
import Test.Pickles.Prove.PaddedWideSlots as PaddedWideSlots
import Test.Pickles.Prove.SideLoadedMain as SideLoadedMain
import Test.Pickles.Prove.SimpleChain as SimpleChain
import Test.Pickles.Prove.SimpleChainN2 as SimpleChainN2
import Test.Pickles.Prove.TreeProofReturn as TreeProofReturn
import Test.Pickles.Prove.TwoPhaseChain as TwoPhaseChain
import Test.Pickles.SharedSrs (buildSharedSrs)
import Test.Pickles.Sideload.DigestEqNrrSpec as SideloadDigestEqNrr
import Test.Pickles.Sideload.LeanInputsSpec as SideloadLeanInputs
import Test.Pickles.Sideload.RoundTripMainChildSpec as SideloadRoundTripMainChild
import Test.Pickles.Sideload.RoundTripNrrSpec as SideloadRoundTripNrr
import Test.Pickles.Sideload.VerifyFixturesSpec as SideloadVerifyFixtures
import Test.Pickles.Sideload.VerifyNrrSpec as SideloadVerifyNrr
import Test.Spec (SpecT, beforeAll, hoistSpec)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess')
import Test.Spec.Runner.Node.Config as Cfg

-- | The pickles suite. Every spec here runs a full prove flow — step
-- | compile, step prove, wrap compile, wrap prove, iterated for the
-- | chained cases — and asserts that the proofs it produces verify.
-- |
-- | `beforeAll buildSharedSrs` builds one SRS for all of them, so the
-- | Lagrange bases attached to it are populated once per run rather
-- | than once per test.
spec :: SpecT (LoggerT Message Aff) Unit Aff Unit
spec = beforeAll buildSharedSrs do
  CompileValidation.spec
  NoRecursionReturn.spec
  Codecs.spec
  SimpleChain.spec
  SimpleChainN2.spec
  PaddedWideSlots.spec
  Chunks2.spec
  Chunks4.spec
  SideLoadedMain.spec
  TreeProofReturn.spec
  HeterogeneousPrevs.spec
  TwoPhaseChain.spec
  SideloadRoundTripNrr.spec
  SideloadRoundTripMainChild.spec
  SideloadDigestEqNrr.spec
  SideloadVerifyNrr.spec
  SideloadVerifyFixtures.spec
  SideloadLeanInputs.spec

main :: Effect Unit
main = runSpecAndExitProcess'
  { defaultConfig: Cfg.defaultConfig, parseCLIOptions: true }
  [ consoleReporter ]
  -- The suite runs in `LoggerT Message Aff`; this is the one place it
  -- is lowered to `Aff`, by supplying the console logger.
  (hoistSpec identity (\_ -> usingLoggerT richMessageStdout) spec)
