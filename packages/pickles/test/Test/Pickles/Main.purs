module Test.Pickles.Main where

import Prelude

import Data.Identity (Identity(..))
import Data.Newtype (un)
import Effect (Effect)
import Effect.Aff (Aff)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiGate, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState)
import Test.Pickles.CombinedPolyComm as CombinedPolyComm
import Test.Pickles.Commitments as Commitments
import Test.Pickles.FFIValidation as FFIValidation
import Test.Pickles.FtComm as FtComm
import Test.Pickles.IPA as IPA
import Test.Pickles.Linearization as Linearization
import Test.Pickles.MultiscaleKnown as MultiscaleKnown
import Test.Pickles.Permutation as Permutation
import Test.Pickles.PublicInputCommitment as PublicInputCommitment
import Test.Pickles.Step as Step
import Test.Pickles.Step.Circuit as StepCircuit
import Test.Pickles.Step.FinalizeOtherProof as FinalizeOtherProofE2E
import Test.Pickles.Step.FqSpongeTranscript as FqSpongeTranscript
import Test.Pickles.Step.SubCircuits as StepSubCircuits
import Test.Pickles.StepE2E as StepE2E
import Test.Pickles.TestContext (createInductiveTestContext)
import Test.Pickles.Wrap.FinalizeOtherProof as WrapFinalizeOtherProof
import Test.Pickles.Wrap.SubCircuits as WrapSubCircuits
import Test.Pickles.WrapE2E as WrapE2E
import Test.Snarky.Circuit.Utils (TestConfig)
import Test.Spec (beforeAll, mapSpec)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess')
import Test.Spec.Runner.Node.Config as Cfg

kimchiTestConfig :: forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)
kimchiTestConfig = { checker: eval, postCondition: Kimchi.postCondition, initState: Kimchi.initialState }

main :: Effect Unit
main = runSpecAndExitProcess'
  { defaultConfig: Cfg.defaultConfig, parseCLIOptions: true }
  [ consoleReporter ]
  do
    beforeAll createInductiveTestContext do
      FFIValidation.spec
      StepSubCircuits.spec kimchiTestConfig
      WrapSubCircuits.spec kimchiTestConfig
      WrapE2E.spec kimchiTestConfig
      FtComm.spec kimchiTestConfig
      CombinedPolyComm.spec kimchiTestConfig
      FinalizeOtherProofE2E.realDataSpec kimchiTestConfig
      WrapFinalizeOtherProof.realDataSpec kimchiTestConfig
      StepCircuit.realDataSpec kimchiTestConfig
      FqSpongeTranscript.spec kimchiTestConfig
      PublicInputCommitment.spec kimchiTestConfig
    mapSpec nat do
      MultiscaleKnown.spec kimchiTestConfig
      Commitments.spec kimchiTestConfig
      IPA.spec kimchiTestConfig
      Linearization.spec kimchiTestConfig
      Permutation.spec kimchiTestConfig
      Step.spec kimchiTestConfig
      StepE2E.spec kimchiTestConfig
  where
  nat :: Identity ~> Aff
  nat x = pure $ un Identity x
