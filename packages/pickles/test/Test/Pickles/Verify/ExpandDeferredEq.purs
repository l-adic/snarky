-- | Self-consistency tests for `Pickles.Prove.Pure.Verify.expandDeferredForVerify`.
-- |
-- | For a given `WrapDeferredValuesInput n` the prover runs
-- | `wrapComputeDeferredValues` (calls `pallasProofOracles` on the step proof)
-- | and the verifier runs `expandDeferredForVerify` (replays the sponge from
-- | the wrap statement's carried `sponge_digest_before_evaluations`). Both
-- | paths must produce the same `WrapDeferredValuesOutput` on the fields
-- | consumed by `assembleWrapMainInput`: `plonk, combinedInnerProduct, xi,
-- | bulletproofPrechallenges, b, branchData, spongeDigestBeforeEvaluations`.
-- |
-- | Two cases cover the two structural shapes:
-- |
-- | * **NRR (n=0)** — `oldBulletproofChallenges = Vector.nil`, so the
-- |   `challengesDigest` sub-sponge absorbs nothing and yields the
-- |   zero-state squeeze. A degenerate but necessary coverage case.
-- | * **Simple_chain b0 (n=1)** — one prev-proof bp-challenge vector gets
-- |   absorbed into the sub-sponge, exercising the `Vector.iter × Vector.iter`
-- |   absorb path in OCaml `wrap_deferred_values.ml:128-137`.
module Test.Pickles.Verify.ExpandDeferredEq
  ( spec
  ) where

import Prelude

import Data.Int.Bits as Int
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PlonkChecks (AllEvals)
import Pickles.Prove.Pure.Verify (ExpandDeferredInput, expandDeferredForVerify)
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesInput, WrapDeferredValuesOutput)
import Pickles.Types (StepField, StepIPARounds)
import Pickles.Verify.Types (BranchData, PlonkMinimal, ScalarChallenge)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.DSL (F)
import Test.Pickles.Prove.NoRecursionReturn.Producer (produceNoRecursionReturn)
import Test.Pickles.Prove.SimpleChain.B0Producer (produceSimpleChainB0)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.Pure.Verify" do
  it "expandDeferredForVerify matches wrapComputeDeferredValues (NRR b0, n=0)" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField
    artifacts <- produceNoRecursionReturn
      { vestaSrs, lagrangeSrs: pallasSrs, pallasProofCrs: pallasSrs }
    assertExpandDeferredMatches @0
      { dvInput: artifacts.wrapDvInput
      , dvProver: artifacts.wrapDv
      , oldBulletproofChallenges: Vector.nil
      }

  it "expandDeferredForVerify matches wrapComputeDeferredValues (Simple_chain b0, n=1)" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField
    artifacts <- produceSimpleChainB0
      { vestaSrs, lagrangeSrs: pallasSrs, pallasProofCrs: pallasSrs }
    -- Simple_chain b0: prev proof is the dummy wrap, its step-side IPA
    -- challenges are dummyIpaChallenges.stepExpanded (already expanded
    -- to step-field elements).
    assertExpandDeferredMatches @1
      { dvInput: artifacts.wrapDvInput
      , dvProver: artifacts.wrapDv
      , oldBulletproofChallenges: artifacts.wrapDvInput.prevChallenges
      }

-- | Build an `ExpandDeferredInput n` from the same facts the prover saw,
-- | run `expandDeferredForVerify`, and assert field-by-field equality
-- | against the prover's `WrapDeferredValuesOutput`.
assertExpandDeferredMatches
  :: forall @n
   . { dvInput :: WrapDeferredValuesInput n
     , dvProver :: WrapDeferredValuesOutput
     , oldBulletproofChallenges :: Vector n (Vector StepIPARounds StepField)
     }
  -> Aff Unit
assertExpandDeferredMatches { dvInput, dvProver, oldBulletproofChallenges } = do
  let
    verifyIn :: ExpandDeferredInput n
    verifyIn =
      { rawPlonk:
          { alpha: dvProver.plonk.alpha
          , beta: dvProver.plonk.beta
          , gamma: dvProver.plonk.gamma
          , zeta: dvProver.plonk.zeta
          } :: PlonkMinimal (F StepField)
      , rawBulletproofChallenges:
          dvProver.bulletproofPrechallenges
            :: Vector StepIPARounds (ScalarChallenge (F StepField))
      , branchData: dvProver.branchData :: BranchData StepField Boolean
      , spongeDigestBeforeEvaluations: dvProver.spongeDigestBeforeEvaluations
      , allEvals: dvInput.allEvals :: AllEvals StepField
      , pEval0Chunks: dvInput.pEval0Chunks
      , oldBulletproofChallenges
      , domainLog2: dvInput.domainLog2
      , zkRows: dvInput.zkRows
      , srsLengthLog2: dvInput.srsLengthLog2
      , generator: dvInput.generator
      , shifts: dvInput.shifts
      , vanishesOnZk: dvInput.vanishesOnZk
      , omegaForLagrange: dvInput.omegaForLagrange
      , endo: dvInput.endo
      , linearizationPoly: dvInput.linearizationPoly :: LinearizationPoly StepField
      }

    dvVerify = expandDeferredForVerify verifyIn

  dvVerify `shouldEqual` dvProver
