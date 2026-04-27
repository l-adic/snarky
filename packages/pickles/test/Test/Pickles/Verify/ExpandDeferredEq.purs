-- | Self-consistency tests for `Pickles.Prove.Pure.Verify.expandDeferredForVerify`.
-- |
-- | At the chain terminus, the out-of-circuit verifier (`Pickles.Prove.Verify`)
-- | has to discharge the deferred IPA accumulator check that an inner step
-- | circuit would otherwise have done. To do that it reconstructs the full
-- | `Wrap_deferred_values.t` from the wrap proof's stored *minimal skeleton*
-- | (`rawPlonk` + `spongeDigestBeforeEvaluations` + raw `bulletproofPrechallenges`)
-- | via `expandDeferredForVerify`. That reconstruction must agree on every
-- | field with what the prover originally computed via
-- | `wrapComputeDeferredValues` — otherwise the verifier discharges the
-- | wrong deferred work and silently passes invalid proofs (or rejects
-- | valid ones).
-- |
-- | This test asserts that equality on real prover artifacts:
-- | `compiledProof.wrapDv` (prover's output) `shouldEqual`
-- | `expandDeferredForVerify (skeleton-derived input)`.
-- |
-- | Two cases cover the two structural shapes:
-- |
-- | * **NRR (n=0)** — `oldBulletproofChallenges = Vector.nil`, so the
-- |   `challengesDigest` sub-sponge absorbs nothing and yields the
-- |   zero-state squeeze. Degenerate but necessary coverage.
-- | * **Simple_chain b0 (n=1)** — one prev-proof bp-challenge vector gets
-- |   absorbed into the sub-sponge, exercising the `Vector.iter × Vector.iter`
-- |   absorb path in OCaml `wrap_deferred_values.ml:128-137`.
module Test.Pickles.Verify.ExpandDeferredEq
  ( spec
  ) where

import Prelude

import Control.Monad.Except (runExceptT)
import Data.Either (Either(..))
import Data.Int.Bits as Int
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PlonkChecks (AllEvals)
import Pickles.Prove.Compile (CompiledProof(..), PrevSlot(..), SlotWrapKey(..), compile)
import Pickles.Prove.Pure.Verify (ExpandDeferredInput, expandDeferredForVerify)
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesOutput)
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil)
import Pickles.Types (StatementIO(..), StepField, StepIPARounds)
import Pickles.Verify.Types (BranchData, PlonkMinimal, ScalarChallenge)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.DSL (F(..))
import Test.Pickles.Prove.NoRecursionReturn (nrrRule)
import Test.Pickles.Prove.SimpleChain (simpleChainRule)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.Pure.Verify" do
  it "expandDeferredForVerify matches wrapComputeDeferredValues (NRR b0, n=0)" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField

    nrr <- liftEffect $ compile @PrevsSpecNil @Unit @(F StepField) @Unit @Effect
      { srs: { vestaSrs, pallasSrs }
      , perSlotImportedVKs: unit
      , debug: false
      , wrapDomainOverride: Nothing
      }
      nrrRule

    eCp <- liftEffect $ runExceptT $ nrr.prover.step { appInput: unit, prevs: unit }
    cp <- case eCp of
      Left e -> liftEffect $ Exc.throw ("nrr prover.step: " <> show e)
      Right p -> pure p

    let CompiledProof r = cp
    assertExpandDeferredMatches @0
      { dvProver: r.wrapDv
      , dvInput: r.wrapDvInput
      , oldBulletproofChallenges: Vector.nil
      }

  it "expandDeferredForVerify matches wrapComputeDeferredValues (Simple_chain b0, n=1)" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField

    { prover } <- liftEffect $ compile
      @(PrevsSpecCons 1 (StatementIO (F StepField) Unit) PrevsSpecNil)
      @(F StepField)
      @Unit
      @(F StepField)
      @Effect
      { srs: { vestaSrs, pallasSrs }
      , perSlotImportedVKs: Tuple Self unit
      , debug: false
      , wrapDomainOverride: Nothing
      }
      simpleChainRule

    let
      basePrev = BasePrev
        { dummyStatement: StatementIO { input: F (negate one), output: unit } }
    eCp <- liftEffect $ runExceptT $ prover.step
      { appInput: F zero, prevs: Tuple basePrev unit }
    cp <- case eCp of
      Left e -> liftEffect $ Exc.throw ("simple_chain prover.step: " <> show e)
      Right p -> pure p

    let CompiledProof r = cp
    -- Simple_chain b0: prev proof is the dummy wrap, its step-side IPA
    -- challenges are dummyIpaChallenges.stepExpanded (already expanded
    -- to step-field elements). The compile-API surfaces these as part
    -- of `wrapDvInput.prevChallenges`.
    assertExpandDeferredMatches @1
      { dvProver: r.wrapDv
      , dvInput: r.wrapDvInput
      , oldBulletproofChallenges: r.wrapDvInput.prevChallenges
      }

-- | Build an `ExpandDeferredInput n` from the same facts the prover saw,
-- | run `expandDeferredForVerify`, and assert field-by-field equality
-- | against the prover's `WrapDeferredValuesOutput`.
assertExpandDeferredMatches
  :: forall @n
   . { dvProver :: WrapDeferredValuesOutput
     , dvInput ::
         { allEvals :: AllEvals StepField
         , pEval0Chunks :: Array StepField
         , domainLog2 :: Int
         , zkRows :: Int
         , srsLengthLog2 :: Int
         , generator :: StepField
         , shifts :: Vector 7 StepField
         , vanishesOnZk :: StepField
         , omegaForLagrange :: { zkRows :: Boolean, offset :: Int } -> StepField
         , endo :: StepField
         , linearizationPoly :: LinearizationPoly StepField
         | _
         }
     , oldBulletproofChallenges :: Vector n (Vector StepIPARounds StepField)
     }
  -> Aff Unit
assertExpandDeferredMatches { dvProver, dvInput, oldBulletproofChallenges } = do
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
