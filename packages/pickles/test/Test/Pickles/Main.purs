module Test.Pickles.Main where

import Prelude

import Data.Identity (Identity(..))
import Data.Newtype (un)
import Effect (Effect)
import Effect.Aff (Aff)
import Test.Pickles.CombinedPolyComm as CombinedPolyComm
import Test.Pickles.Commitments as Commitments
import Test.Pickles.E2E as E2E
import Test.Pickles.FtComm as FtComm
import Test.Pickles.IPA as IPA
import Test.Pickles.Linearization as Linearization
import Test.Pickles.MultiscaleKnown as MultiscaleKnown
import Test.Pickles.Permutation as Permutation
import Test.Pickles.PublicInputCommitment as PublicInputCommitment
import Test.Pickles.Step as Step
import Test.Pickles.Step.FinalizeOtherProof as FinalizeOtherProofE2E
import Test.Pickles.Step.FqSpongeTranscript as FqSpongeTranscript
import Test.Pickles.StepE2E as StepE2E
import Test.Spec (mapSpec)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess')
import Test.Spec.Runner.Node.Config as Cfg

main :: Effect Unit
main = runSpecAndExitProcess'
  { defaultConfig: Cfg.defaultConfig, parseCLIOptions: true }
  [ consoleReporter ]
  do
    E2E.spec
    FtComm.spec
    CombinedPolyComm.spec
    FinalizeOtherProofE2E.realDataSpec
    FqSpongeTranscript.spec
    FqSpongeTranscript.realDataSpec
    PublicInputCommitment.spec
    mapSpec nat do
      MultiscaleKnown.spec
      Commitments.spec
      IPA.spec
      Linearization.spec
      Permutation.spec
      Step.spec
      StepE2E.spec
  where
  nat :: Identity ~> Aff
  nat x = pure $ un Identity x
