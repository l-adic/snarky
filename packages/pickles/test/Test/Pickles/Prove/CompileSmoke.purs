-- | Smoke tests for `Pickles.Prove.Compile.compile`.
-- |
-- | Three end-to-end cases exercising the compile API across the
-- | spec shapes that have a `CompilableSpec` instance:
-- |
-- |   * NRR (`PrevsSpecNil`) — base-case Output-mode rule, no prevs.
-- |   * Simple_chain b0 (`PrevsSpecCons 1 …`, BasePrev branch).
-- |   * Simple_chain b1 inductive (`PrevsSpecCons 1 …`, InductivePrev
-- |     threading `b0` as `prev` for `b1`).
-- |
-- | Each test compiles the rule, runs `prover.step`, and asserts the
-- | resulting `CompiledProof` validates via `verify`. The 5-iteration
-- | extension of Simple_chain (b0..b4) lives in
-- | `Test.Pickles.Prove.SimpleChain`.
module Test.Pickles.Prove.CompileSmoke
  ( spec
  ) where

import Prelude

import Control.Monad.Except (runExceptT)
import Data.Either (Either(..))
import Data.Int.Bits as Int
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Data.Newtype (un)
import Pickles.Prove.Compile (PrevSlot(..), SlotWrapKey(..), Tag(..), compile, verify)
import Pickles.Prove.Step (StepRule)
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil)
import Pickles.Types (StatementIO(..), StepField)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.DSL (F(..), FVar, const_)
import Test.Pickles.Prove.SimpleChain (simpleChainRule)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | The NRR inductive rule — Output mode, N=0, returns `F zero`.
nrrRule :: StepRule 0 Unit Unit Unit (F StepField) (FVar StepField) Unit Unit
nrrRule _ = pure
  { prevPublicInputs: Vector.nil
  , proofMustVerify: Vector.nil
  , publicOutput: const_ zero
  }

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.Compile" do
  it "compile + prover.step: NRR end-to-end verify returns true" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField

    { prover, tag } <- liftEffect $ compile @PrevsSpecNil @Unit @(F StepField) @Unit @Effect
      { srs: { vestaSrs, pallasSrs }
      , perSlotImportedVKs: unit
      , debug: false
      }
      nrrRule

    eResult <- liftEffect $ runExceptT $ prover.step { appInput: unit, prevs: unit }
    case eResult of
      Left e -> liftEffect $ Exc.throw ("prover.step: " <> show e)
      Right compiledProof ->
        verify (un Tag tag).verifier [ compiledProof ] `shouldEqual` true

  it "compile + prover.step: Simple_chain b0 end-to-end verify returns true" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField

    { prover, tag } <- liftEffect $ compile
      @(PrevsSpecCons 1 (StatementIO (F StepField) Unit) PrevsSpecNil)
      @(F StepField)
      @Unit
      @(F StepField)
      @Effect
      { srs: { vestaSrs, pallasSrs }
      , perSlotImportedVKs: Tuple Self unit
      , debug: false
      }
      (simpleChainRule)

    -- b0: base case — no real prev proof, supply BasePrev with the
    -- dummy input Simple_chain convention uses (self = -1).
    eResult <- liftEffect $ runExceptT $ prover.step
      { appInput: F zero
      , prevs:
          Tuple
            (BasePrev { dummyStatement: StatementIO { input: F (negate one), output: unit } })
            unit
      }
    case eResult of
      Left e -> liftEffect $ Exc.throw ("prover.step: " <> show e)
      Right compiledProof ->
        verify (un Tag tag).verifier [ compiledProof ] `shouldEqual` true

  it "compile + prover.step: Simple_chain b1 inductive end-to-end verify returns true" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField

    { prover, tag } <- liftEffect $ compile
      @(PrevsSpecCons 1 (StatementIO (F StepField) Unit) PrevsSpecNil)
      @(F StepField)
      @Unit
      @(F StepField)
      @Effect
      { srs: { vestaSrs, pallasSrs }
      , perSlotImportedVKs: Tuple Self unit
      , debug: false
      }
      (simpleChainRule)

    -- b0: base case — produces the prev proof we'll feed into b1.
    eResultB0 <- liftEffect $ runExceptT $ prover.step
      { appInput: F zero
      , prevs:
          Tuple
            (BasePrev { dummyStatement: StatementIO { input: F (negate one), output: unit } })
            unit
      }
    compiledProofB0 <- case eResultB0 of
      Left e -> liftEffect $ Exc.throw ("prover.step b0: " <> show e)
      Right p -> pure p

    -- b1: inductive — feed b0 as InductivePrev. Self-recursive, so the
    -- prev's tag is the same tag this `compile` returned.
    eResultB1 <- liftEffect $ runExceptT $ prover.step
      { appInput: F one
      , prevs: Tuple (InductivePrev compiledProofB0 tag) unit
      }
    case eResultB1 of
      Left e -> liftEffect $ Exc.throw ("prover.step b1: " <> show e)
      Right compiledProofB1 ->
        verify (un Tag tag).verifier [ compiledProofB1 ] `shouldEqual` true
