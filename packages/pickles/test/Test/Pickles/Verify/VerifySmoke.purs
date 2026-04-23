-- | Smoke test for the top-level `Pickles.verify` pipeline.
-- |
-- | Runs the NRR b0 proof flow via `produceNoRecursionReturn`, constructs
-- | a `Pickles.CompiledProof` from the artifacts, builds a `Verifier`
-- | from the wrap VK + Vesta SRS + step domain, and asserts
-- | `Pickles.verify [proof]` returns `true`.
-- |
-- | This exercises all three verifier stages end-to-end:
-- |   1. `expandDeferredForVerify` (already byte-identity-checked in
-- |      `Test.Pickles.Verify.ExpandDeferredEq`)
-- |   2. IPA step accumulator check via `vestaSrsBPolyCommitment`
-- |   3. kimchi `batch_verify` on the wrap proof
-- |
-- | The test also asserts that the verifier's reconstructed wrap
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
import Test.Pickles.Prove.NoRecursionReturn.Producer (produceNoRecursionReturn)
import Test.Pickles.Prove.SimpleChain.B0Producer (produceSimpleChainB0)
import Test.Pickles.Prove.SimpleChain.B1Producer (produceSimpleChainB1)
import Test.Pickles.Prove.TreeProofReturn.B0Producer (produceTreeProofReturnB0)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.verify (out-of-circuit)" do
  it "NRR b0 end-to-end: verify returns true" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField
    artifacts <- produceNoRecursionReturn
      { vestaSrs, lagrangeSrs: pallasSrs, pallasProofCrs: pallasSrs }

    let
      verifier = mkVerifier
        { wrapVK: artifacts.wrapCR.verifierIndex
        , vestaSrs
        , stepDomainLog2:
            ProofFFI.pallasProverIndexDomainLog2 artifacts.stepCR.proverIndex
        }

      -- NRR's Output-mode statement = `publicOutputs[0]` = the rule's
      -- returned `const_ zero` = zero.
      nrrOutput :: F StepField
      nrrOutput = Vector.head artifacts.stepResult.publicOutputs

      -- Build CompiledProof. NRR is Output mode: stmtVal = outputVal = F StepField;
      -- mpv = 0; auxVal = Unit.
      compiledProof :: CompiledProof 0 (F StepField) (F StepField) Unit
      compiledProof = CompiledProof
        { statement: nrrOutput
        , publicOutput: nrrOutput
        , auxiliaryOutput: unit
        , wrapProof: artifacts.wrapResult.proof
        , rawPlonk: toPlonkMinimal artifacts.wrapDv.plonk
        , rawBulletproofChallenges: artifacts.wrapDv.bulletproofPrechallenges
        , branchData: artifacts.wrapDv.branchData
        , spongeDigestBeforeEvaluations: artifacts.wrapDv.spongeDigestBeforeEvaluations
        , prevEvals: artifacts.wrapDvInput.allEvals
        , pEval0Chunks: artifacts.wrapDvInput.pEval0Chunks
        , oldBulletproofChallenges: Vector.nil
        , challengePolynomialCommitment: artifacts.stepProofSg
        , messagesForNextStepProofDigest: artifacts.messagesForNextStepProofDigest
        , messagesForNextWrapProofDigest: artifacts.messagesForNextWrapProofDigest
        }

    -- Precondition: verifier-reconstructed PI matches prover-assembled PI.
    -- If this diverges, stage 3 will trivially fail; we want to surface
    -- the divergence with a precise error rather than a vague
    -- `verify = false`.
    wrapPublicInput verifier compiledProof `shouldEqual` artifacts.wrapResult.publicInputs

    -- End-to-end verification.
    verify verifier [ compiledProof ] `shouldEqual` true

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
        { statement: F zero -- base case: self = 0
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
        }

    wrapPublicInput verifier compiledProof `shouldEqual` artifacts.wrapResult.publicInputs
    verify verifier [ compiledProof ] `shouldEqual` true
