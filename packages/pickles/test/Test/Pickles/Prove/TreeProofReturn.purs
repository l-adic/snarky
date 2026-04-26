-- | PureScript-side analog of OCaml's `Tree_proof_return` test
-- | (`mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:315-429`).
-- |
-- | Tree_proof_return is the heterogeneous-prevs target:
-- |
-- |   prevs = [No_recursion_return.tag; self]
-- |   max_proofs_verified = N2
-- |   per-slot widths      = [0, 2]
-- |   override_wrap_domain = N1  → wrap_domains.h = 2^14
-- |   public_input         = Output Field
-- |
-- | Compile-API driven via `compile` + `prover.step`. Iterates the
-- | full chain b0..b4 (matching SimpleChain's iteration depth):
-- |
-- |   * b0    — slot 0 = `InductivePrev nrrCp` (real NRR proof);
-- |             slot 1 = `BasePrev { output = -1 }` (dummy self).
-- |             Output = 0.
-- |   * b_k+1 — slot 0 = same NRR proof reused; slot 1 = `InductivePrev
-- |             b_k tree.tag` (the previous round's Tree proof).
-- |             Output = k+1.
-- |
-- | The rule's `proofMustVerify` for slot 1 is gated on
-- | `prevOut == -1`, so b0 skips real verification of the dummy self
-- | prev while b1+ verify the previous Tree proof. The full chain is
-- | handed to `verify` for kimchi-level batch verification.
module Test.Pickles.Prove.TreeProofReturn
  ( spec
  , treeProofReturnRule
  ) where

import Prelude

import Control.Monad.Except (runExceptT)
import Control.Monad.Trans.Class (lift) as MT
import Data.Either (Either(..))
import Data.Int.Bits as Int
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Pickles.Prove.Compile
  ( CompiledProof
  , PrevSlot(..)
  , SlotWrapKey(..)
  , Tag(..)
  , compile
  , verify
  )
import Pickles.Prove.Step (StepRule)
import Pickles.Step.Advice (getPrevAppStates)
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil)
import Pickles.Types (StatementIO(..), StepField)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, const_, exists, if_, not_, true_)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

type TreeProofReturnPrevsSpec =
  PrevsSpecCons 0 (StatementIO Unit (F StepField))
    (PrevsSpecCons 2 (StatementIO Unit (F StepField)) PrevsSpecNil)

treeProofReturnRule
  :: StepRule 2
       ( Tuple (StatementIO Unit (F StepField))
           (Tuple (StatementIO Unit (F StepField)) Unit)
       )
       Unit
       Unit
       (F StepField)
       (FVar StepField)
       (F StepField)
       (FVar StepField)
treeProofReturnRule _ = do
  nrrInput <- exists $ MT.lift do
    Tuple (StatementIO { output: nrrOut }) _ <- getPrevAppStates unit
    pure nrrOut
  prevInput <- exists $ MT.lift do
    Tuple _ (Tuple (StatementIO { output: prevOut }) _) <- getPrevAppStates unit
    pure prevOut
  isBaseCase <- exists $ MT.lift do
    Tuple _ (Tuple (StatementIO { output: prevOut }) _) <- getPrevAppStates unit
    pure (prevOut == F (negate one))
  let proofMustVerifySlot1 = not_ isBaseCase
  selfVal <- if_ isBaseCase (const_ zero) (CVar.add_ (const_ one) prevInput)
  pure
    { prevPublicInputs: nrrInput :< prevInput :< Vector.nil
    , proofMustVerify: true_ :< proofMustVerifySlot1 :< Vector.nil
    , publicOutput: selfVal
    }

nrrRule :: StepRule 0 Unit Unit Unit (F StepField) (FVar StepField) Unit Unit
nrrRule _ = pure
  { prevPublicInputs: Vector.nil
  , proofMustVerify: Vector.nil
  , publicOutput: const_ zero
  }

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.TreeProofReturn" do
  it "5-iteration heterogeneous chain (b0..b4): NRR external slot + self-recursive slot, end-to-end verify" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField

    nrr <- liftEffect $ compile @PrevsSpecNil @Unit @(F StepField) @Unit @Effect
      { srs: { vestaSrs, pallasSrs }
      , perSlotImportedVKs: unit
      , debug: false
      , wrapDomainOverride: Nothing
      }
      nrrRule
    eNrrCp <- liftEffect $ runExceptT $ nrr.prover.step
      { appInput: unit, prevs: unit }
    nrrCp <- case eNrrCp of
      Left e -> liftEffect $ Exc.throw ("nrr prover.step: " <> show e)
      Right p -> pure p

    tree <- liftEffect $ compile
      @TreeProofReturnPrevsSpec
      @Unit
      @(F StepField)
      @(F StepField)
      @Effect
      { srs: { vestaSrs, pallasSrs }
      , perSlotImportedVKs:
          Tuple (External nrr.vks) (Tuple (SelfWithStepDomain 15) unit)
      , debug: false
      , wrapDomainOverride: Just 14
      }
      treeProofReturnRule

    let
      -- Slot 1 (Self) prev for round k+1: b_k's CompiledProof as
      -- `InductivePrev`. Slot 0 (NRR external) reuses the same NRR
      -- proof every round — NRR has no prevs so its proof is fixed.
      runStep
        :: PrevSlot Unit 2 (StatementIO Unit (F StepField)) (F StepField)
        -> Aff (CompiledProof 2 (StatementIO Unit (F StepField)) (F StepField) Unit)
      runStep selfPrev = do
        eRes <- liftEffect $ runExceptT $ tree.prover.step
          { appInput: unit
          , prevs:
              Tuple (InductivePrev nrrCp nrr.tag)
                (Tuple selfPrev unit)
          }
        case eRes of
          Left e -> liftEffect $ Exc.throw ("tree prover.step: " <> show e)
          Right p -> pure p

      -- BasePrev's `dummyStatement.output = -1` is the marker the rule
      -- destructures to gate `proofMustVerify` for slot 1.
      basePrevSelf = BasePrev
        { dummyStatement: StatementIO { input: unit, output: F (negate one) :: F StepField }
        }

    b0 <- runStep basePrevSelf
    b1 <- runStep (InductivePrev b0 tree.tag)
    b2 <- runStep (InductivePrev b1 tree.tag)
    b3 <- runStep (InductivePrev b2 tree.tag)
    b4 <- runStep (InductivePrev b3 tree.tag)

    verify (un Tag tree.tag).verifier [ b0, b1, b2, b3, b4 ] `shouldEqual` true
