-- | End-to-end verify of an OCaml-produced NRR wrap proof.
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

import Data.Reflectable (reflectType)
import Data.Vector as Vector
import Effect.Aff (Aff)
import Pickles.Constants (zkRows)
import Pickles.Linearization (pallas) as Linearization
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.ProofFFI (permutationVanishingPolynomial)
import Pickles.Prove.Pure.Verify (expandDeferredForVerify)
import Pickles.Prove.Verify (CompiledProof(..), mkVerifier, verifyOne)
import Pickles.Types (StepField, StepIPARounds)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (F(..))
import Snarky.Circuit.Kimchi.EndoScalar (toFieldPure)
import Snarky.Curves.Class (EndoScalar(..), endoScalar)
import Test.Pickles.Sideload.Loader (loadNrrFixture)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))

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

      -- Compute `wrapDv` by running the same `expandDeferredForVerify`
      -- the verifier's stage 1 runs internally. The field is unused by
      -- `verifyOne` (it reconstructs deferred values from the skeleton
      -- itself), but `CompiledProof` carries it for the prover-side
      -- self-consistency test in `Test.Pickles.Verify.ExpandDeferredEq`,
      -- which compares the prover's `wrapComputeDeferredValues` output
      -- against `expandDeferredForVerify` of the same skeleton.
      --
      -- That ExpandDeferredEq check requires a PROVER-COMPUTED
      -- `wrapDv` (different code path from the verifier's
      -- expansion) — OCaml fixtures only ship the skeleton, so we
      -- can't run that consistency check here. The end-to-end
      -- `verifyOne` assertion below is the meaningful cross-stack
      -- check: if it returns `true`, PS's `expandDeferredForVerify`
      -- agrees with OCaml's expansion to within whatever the kimchi
      -- batch-verify pins down.
      stepEndo = case (endoScalar :: EndoScalar StepField) of EndoScalar e -> e
      zetaField = coerce (toFieldPure fixture.rawPlonk.zeta (F stepEndo)) :: StepField
      vanishesOnZkAtZeta = permutationVanishingPolynomial
        { domainLog2: fixture.stepDomainLog2
        , zkRows
        , pt: zetaField
        }

      wrapDv = expandDeferredForVerify
        { rawPlonk: fixture.rawPlonk
        , rawBulletproofChallenges: fixture.rawBulletproofChallenges
        , branchData: fixture.branchData
        , spongeDigestBeforeEvaluations: fixture.spongeDigestBeforeEvaluations
        , allEvals: fixture.prevEvals
        , pEval0Chunks: fixture.pEval0Chunks
        -- NRR has `mpv = 0` → `oldBulletproofChallenges` is `Vector 0`
        -- (empty). The challenge-digest sub-sponge absorbs nothing.
        , oldBulletproofChallenges: Vector.nil
        , domainLog2: fixture.stepDomainLog2
        , zkRows
        , srsLengthLog2: reflectType (Proxy :: Proxy StepIPARounds)
        , generator: domainGenerator fixture.stepDomainLog2 :: StepField
        , shifts: domainShifts fixture.stepDomainLog2
        , vanishesOnZk: vanishesOnZkAtZeta
        , omegaForLagrange: \_ -> one
        , endo: stepEndo
        , linearizationPoly: Linearization.pallas
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
        , wrapDv
        }

    verifyOne verifier compiledProof `shouldEqual` true
