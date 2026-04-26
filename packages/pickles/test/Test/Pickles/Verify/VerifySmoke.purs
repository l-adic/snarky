-- | Smoke test for the top-level `Pickles.verify` pipeline on
-- | shapes that still go through their producers (Simple_chain b0/b1
-- | and Tree_proof_return b0). The NRR case moved to
-- | `Test.Pickles.Prove.CompileSmoke` once the `compile` API landed.
-- |
-- | Exercises all three verifier stages end-to-end:
-- |   1. `expandDeferredForVerify` (already byte-identity-checked in
-- |      `Test.Pickles.Verify.ExpandDeferredEq`)
-- |   2. IPA step accumulator check via `vestaSrsBPolyCommitment`
-- |   3. kimchi `batch_verify` on the wrap proof
-- |
-- | Each test also asserts that the verifier's reconstructed wrap
-- | public-input array byte-matches the prover's `wrapResult.publicInputs`
-- | — otherwise stage 3 would trivially fail.
module Test.Pickles.Verify.VerifySmoke
  ( spec
  ) where

import Prelude

import Data.Int.Bits as Int
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Pickles.Dummy as Dummy
import Pickles.ProofFFI (pallasProverIndexDomainLog2) as ProofFFI
import Pickles.Prove.Verify (CompiledProof(..), mkVerifier, verify, wrapPublicInput)
import Pickles.Types (StepField)
import Pickles.Verify.Types (toPlonkMinimal)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.DSL (F(..))
import Test.Pickles.Prove.SimpleChain.B0Producer (produceSimpleChainB0)
import Test.Pickles.Prove.SimpleChain.B1Producer (produceSimpleChainB1)
import Test.Pickles.Prove.TreeProofReturn.B0Producer (produceTreeProofReturnB0)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.verify (out-of-circuit)" do
  it "Simple_chain b0 end-to-end: verify returns true" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField
    artifacts <- produceSimpleChainB0
      { vestaSrs, lagrangeSrs: pallasSrs, pallasProofCrs: pallasSrs }

    let
      verifier = mkVerifier
        { wrapVK: artifacts.wrapCR.verifierIndex
        , vestaSrs
        , stepDomainLog2:
            ProofFFI.pallasProverIndexDomainLog2 artifacts.stepCR.proverIndex
        }

      -- Simple_chain rule is Input-mode: statement = app input = F zero
      -- (the base-case `self`). outputVal = Unit, auxVal = Unit. mpv = 1.
      compiledProof :: CompiledProof 1 (F StepField) Unit Unit
      compiledProof = CompiledProof
        { statement: F zero
        , publicOutput: unit
        , auxiliaryOutput: unit
        , wrapProof: artifacts.wrapResult.proof
        , rawPlonk: toPlonkMinimal artifacts.wrapDv.plonk
        , rawBulletproofChallenges: artifacts.wrapDv.bulletproofPrechallenges
        , branchData: artifacts.wrapDv.branchData
        , spongeDigestBeforeEvaluations: artifacts.wrapDv.spongeDigestBeforeEvaluations
        , prevEvals: artifacts.wrapDvInput.allEvals
        , pEval0Chunks: artifacts.wrapDvInput.pEval0Chunks
        -- Base case: prev (= dummy wrap) carries `Dummy.Ipa.Step.challenges`
        -- as its `deferred_values.bulletproof_challenges`, expanded via
        -- `Ipa.Step.compute_challenges` = `dummyIpaChallenges.stepExpanded`.
        , oldBulletproofChallenges:
            Dummy.dummyIpaChallenges.stepExpanded :< Vector.nil
        , challengePolynomialCommitment: artifacts.stepProofSg
        , messagesForNextStepProofDigest: artifacts.messagesForNextStepProofDigest
        , messagesForNextWrapProofDigest: artifacts.messagesForNextWrapProofDigest
        , msgWrapChallenges:
            artifacts.msgForNextWrapRealChals :< Vector.nil
        , outerStepChalPolyComms:
            artifacts.b0ChalPolyComm :< Vector.nil
        }

    wrapPublicInput verifier compiledProof `shouldEqual` artifacts.wrapResult.publicInputs
    verify verifier [ compiledProof ] `shouldEqual` true

  it "Simple_chain b1 (inductive) end-to-end: verify returns true" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField
    artifacts <- produceSimpleChainB1
      { vestaSrs, lagrangeSrs: pallasSrs, pallasProofCrs: pallasSrs }

    let
      verifier = mkVerifier
        { wrapVK: artifacts.b0.wrapCR.verifierIndex
        , vestaSrs
        , stepDomainLog2:
            ProofFFI.pallasProverIndexDomainLog2 artifacts.b0.stepCR.proverIndex
        }

      -- b1 proves self = 1; prev = 0 (= b0's statement).
      -- oldBulletproofChallenges now carries b0's REAL wrap bp-chals
      -- (from `wrapDv.bulletproofPrechallenges` expanded via step endo),
      -- not a dummy — the first inductive case exercising stage 2's
      -- accumulator check with non-dummy data.
      compiledProof :: CompiledProof 1 (F StepField) Unit Unit
      compiledProof = CompiledProof
        { statement: F one
        , publicOutput: unit
        , auxiliaryOutput: unit
        , wrapProof: artifacts.wrapResult.proof
        , rawPlonk: toPlonkMinimal artifacts.wrapDv.plonk
        , rawBulletproofChallenges: artifacts.wrapDv.bulletproofPrechallenges
        , branchData: artifacts.wrapDv.branchData
        , spongeDigestBeforeEvaluations: artifacts.wrapDv.spongeDigestBeforeEvaluations
        , prevEvals: artifacts.wrapDvInput.allEvals
        , pEval0Chunks: artifacts.wrapDvInput.pEval0Chunks
        , oldBulletproofChallenges: artifacts.wrapDvInput.prevChallenges
        , challengePolynomialCommitment: artifacts.stepProofSg
        , messagesForNextStepProofDigest: artifacts.messagesForNextStepProofDigest
        , messagesForNextWrapProofDigest: artifacts.messagesForNextWrapProofDigest
        , msgWrapChallenges:
            artifacts.msgForNextWrapRealChals :< Vector.nil
        , outerStepChalPolyComms:
            artifacts.b1ChalPolyComm :< Vector.nil
        }

    wrapPublicInput verifier compiledProof `shouldEqual` artifacts.wrapResult.publicInputs
    verify verifier [ compiledProof ] `shouldEqual` true

  it "Tree_proof_return b0 end-to-end: verify returns true" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField
    artifacts <- produceTreeProofReturnB0
      { vestaSrs, lagrangeSrs: pallasSrs, pallasProofCrs: pallasSrs }

    let
      verifier = mkVerifier
        { wrapVK: artifacts.wrapCR.verifierIndex
        , vestaSrs
        , stepDomainLog2:
            ProofFFI.pallasProverIndexDomainLog2 artifacts.stepCR.proverIndex
        }

      -- Tree_proof_return is Output-mode, mpv=2.
      -- Statement = outputVal = F StepField (the rule's self).
      -- Slot 0 old bp chals = NRR's expanded step chals; slot 1 = dummy.
      compiledProof :: CompiledProof 2 (F StepField) (F StepField) Unit
      compiledProof = CompiledProof
        { msgWrapChallenges: artifacts.msgWrapChallenges
        , statement: F zero -- base case: self = 0
        , publicOutput: F zero
        , auxiliaryOutput: unit
        , wrapProof: artifacts.wrapResult.proof
        , rawPlonk: toPlonkMinimal artifacts.wrapDv.plonk
        , rawBulletproofChallenges: artifacts.wrapDv.bulletproofPrechallenges
        , branchData: artifacts.wrapDv.branchData
        , spongeDigestBeforeEvaluations: artifacts.wrapDv.spongeDigestBeforeEvaluations
        , prevEvals: artifacts.wrapDvInput.allEvals
        , pEval0Chunks: artifacts.wrapDvInput.pEval0Chunks
        , oldBulletproofChallenges: artifacts.wrapDvInput.prevChallenges
        , challengePolynomialCommitment: artifacts.stepProofSg
        , messagesForNextStepProofDigest: artifacts.messagesForNextStepProofDigest
        , messagesForNextWrapProofDigest: artifacts.messagesForNextWrapProofDigest
        , outerStepChalPolyComms: artifacts.outerStepChalPolyComms
        }

    wrapPublicInput verifier compiledProof `shouldEqual` artifacts.wrapResult.publicInputs
    verify verifier [ compiledProof ] `shouldEqual` true
