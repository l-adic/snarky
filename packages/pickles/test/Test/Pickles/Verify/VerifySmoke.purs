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
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Pickles (CompiledProof(..), mkVerifier, verify, wrapPublicInput)
import Pickles.ProofFFI (pallasProverIndexDomainLog2) as ProofFFI
import Pickles.Types (StepField)
import Pickles.Verify.Types (toPlonkMinimal)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.DSL (F)
import Test.Pickles.Prove.NoRecursionReturn.Producer (produceNoRecursionReturn)
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
