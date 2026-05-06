-- | Phase 5.4: end-to-end verify of an OCaml-produced NRR wrap proof.
-- |
-- | Loads the OCaml NRR fixture (vk + kimchi proof + statement +
-- | wrapping), assembles a `CompiledProof`, builds a `Verifier` via
-- | `mkVerifier`, and runs `verifyOne`. Asserts the result is `true`.
-- |
-- | This is the strongest cross-stack compatibility result: it proves
-- | that PS's verifier accepts an OCaml-produced wrap proof against
-- | an OCaml-produced VK, given correctly decoded deferred-values +
-- | message digests + AllEvals.
module Test.Pickles.Sideload.VerifyNrrSpec
  ( spec
  ) where

import Prelude

import Effect.Aff (Aff)
import Pickles.Prove.Verify (CompiledProof(..), mkVerifier, verifyOne)
import Test.Pickles.Sideload.Loader (loadNrrFixture)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Sideload.NRR verify" do
  it "verifyOne accepts the OCaml-produced NRR wrap proof" \_ -> do
    fixture <- loadNrrFixture "packages/pickles/test/fixtures/sideload/nrr"

    let
      verifier = mkVerifier
        { wrapVK: fixture.vk
        , vestaSrs: fixture.vestaSrs
        , stepDomainLog2: fixture.stepDomainLog2
        }

      compiledProof
        :: CompiledProof 0 _ Unit Unit
      compiledProof = CompiledProof
        { statement: fixture.statement
        , publicOutput: unit
        , auxiliaryOutput: unit
        , wrapProof: fixture.wireProof
        , rawPlonk: fixture.rawPlonk
        , rawBulletproofChallenges: fixture.rawBulletproofChallenges
        , branchData: fixture.branchData
        , spongeDigestBeforeEvaluations: fixture.spongeDigestBeforeEvaluations
        , prevEvals: fixture.prevEvals
        , pEval0Chunks: fixture.pEval0Chunks
        , challengePolynomialCommitment: fixture.challengePolynomialCommitment
        , messagesForNextStepProofDigest: fixture.messagesForNextStepProofDigest
        , messagesForNextWrapProofDigest: fixture.messagesForNextWrapProofDigest
        , widthData: fixture.widthData
        , stepDomainLog2: fixture.stepDomainLog2
        -- `wrapDv` is only consulted by self-consistency tests; verifyOne
        -- doesn't read it. We don't have it from the OCaml fixture.
        , wrapDv: unsafeUndefined
        }

    verifyOne verifier compiledProof `shouldEqual` true

foreign import unsafeUndefined :: forall a. a
