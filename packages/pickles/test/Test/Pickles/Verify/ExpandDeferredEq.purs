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
import Data.Exists (runExists)
import Data.Int.Bits as Int
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (Tuple1, tuple1, (/\))
import Data.Vector (Vector)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PlonkChecks (AllEvals)
import Pickles.Prove.Compile
  ( BranchProver(..)
  , CompiledProof(..)
  , CompiledProofWidthData(..)
  , PrevSlot(..)
  , RulesCons
  , RulesNil
  , SlotWrapKey(..)
  , compileMulti
  , mkRuleEntry
  )
import Pickles.Prove.Pure.Verify (ExpandDeferredInput, expandDeferredForVerify)
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesInput, WrapDeferredValuesOutput)
import Pickles.Step.Slots (Compiled, Slot)
import Pickles.Step.Types (Field)
import Pickles.Types (StatementIO(..), StepIPARounds)
import Pickles.Verify.Types (BranchData, PlonkMinimal, ScalarChallenge)
import Pickles.Wrap.Slots (NoSlots, Slots1)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.DSL (F(..))
import Test.Pickles.Prove.NoRecursionReturn (nrrRule)
import Test.Pickles.Prove.SimpleChain (simpleChainRule)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

type NrrRules =
  RulesCons 0 Unit Unit Unit
    RulesNil

type SimpleChainRules =
  RulesCons 1
    (Tuple1 (StatementIO (F Field) Unit))
    (Tuple1 (Slot Compiled 1 (StatementIO (F Field) Unit)))
    (Tuple1 SlotWrapKey)
    RulesNil

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.Pure.Verify" do
  it "expandDeferredForVerify matches wrapComputeDeferredValues (NRR b0, n=0)" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @Field

    nrrEntry <- liftEffect $ mkRuleEntry @0 @(F Field) @Unit nrrRule unit

    nrr <- liftEffect $ compileMulti
      @NrrRules
      @(F Field)
      @Unit
      @NoSlots
      { srs: { vestaSrs, pallasSrs }, debug: false, wrapDomainOverride: Nothing }
      (tuple1 nrrEntry)

    let BranchProver nrrProver = fst nrr.provers
    eCp <- liftEffect $ runExceptT $ nrrProver
      { appInput: unit, prevs: unit, sideloadedVKs: unit }
    cp <- case eCp of
      Left e -> liftEffect $ Exc.throw ("nrr prover.step: " <> show e)
      Right p -> pure p

    -- The width-sized fields (including wrapDvInput) are hidden behind
    -- `r.widthData`'s existential. `runExists` recovers the typed
    -- values inside a polymorphic continuation.
    let CompiledProof r = cp
    runExists
      ( \(CompiledProofWidthData wd) ->
          assertExpandDeferredMatches
            { dvProver: r.wrapDv
            , dvInput: wd.wrapDvInput
            , oldBulletproofChallenges: wd.oldBulletproofChallenges
            }
      )
      r.widthData

  it "expandDeferredForVerify matches wrapComputeDeferredValues (Simple_chain b0, n=1)" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @Field

    chainEntry <- liftEffect $ mkRuleEntry @1 @Unit @(F Field) simpleChainRule (tuple1 Self)

    chain <- liftEffect $ compileMulti
      @SimpleChainRules
      @Unit
      @(F Field)
      @(Slots1 1)
      { srs: { vestaSrs, pallasSrs }, debug: false, wrapDomainOverride: Nothing }
      (tuple1 chainEntry)

    let
      BranchProver chainProver = fst chain.provers
      basePrev = BasePrev
        { dummyStatement: StatementIO { input: F (negate one), output: unit } }
    eCp <- liftEffect $ runExceptT $ chainProver
      { appInput: F zero, prevs: tuple1 basePrev, sideloadedVKs: unit /\ unit }
    cp <- case eCp of
      Left e -> liftEffect $ Exc.throw ("simple_chain prover.step: " <> show e)
      Right p -> pure p

    let CompiledProof r = cp
    -- Simple_chain b0: prev proof is the dummy wrap, its step-side IPA
    -- challenges are `dummyIpaChallenges.stepExpanded`. The compile-API
    -- surfaces these as part of `wrapDvInput.prevChallenges`.
    runExists
      ( \(CompiledProofWidthData wd) ->
          assertExpandDeferredMatches
            { dvProver: r.wrapDv
            , dvInput: wd.wrapDvInput
            , oldBulletproofChallenges: wd.wrapDvInput.prevChallenges
            }
      )
      r.widthData

-- | Build an `ExpandDeferredInput n` from the same facts the prover saw,
-- | run `expandDeferredForVerify`, and assert field-by-field equality
-- | against the prover's `WrapDeferredValuesOutput`.
assertExpandDeferredMatches
  :: forall @n
   . { dvProver :: WrapDeferredValuesOutput
     , dvInput :: WrapDeferredValuesInput n
     , oldBulletproofChallenges :: Vector n (Vector StepIPARounds Field)
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
          } :: PlonkMinimal (F Field)
      , rawBulletproofChallenges:
          dvProver.bulletproofPrechallenges
            :: Vector StepIPARounds (ScalarChallenge (F Field))
      , branchData: dvProver.branchData :: BranchData Field Boolean
      , spongeDigestBeforeEvaluations: dvProver.spongeDigestBeforeEvaluations
      , allEvals: dvInput.allEvals :: AllEvals Field
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
      , linearizationPoly: dvInput.linearizationPoly :: LinearizationPoly Field
      }

    dvVerify = expandDeferredForVerify verifyIn

  dvVerify `shouldEqual` dvProver
