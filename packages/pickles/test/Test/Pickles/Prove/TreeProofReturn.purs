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
-- | Compile-API driven via `compile` + `prover.step`. Tree b0 base
-- | case: slot 0 = `InductivePrev nrrCp nrr.tag` (real NRR proof);
-- | slot 1 = `BasePrev { dummyStatement = StatementIO { input: unit,
-- | output: -1 } }` (dummy self).
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
  ( PrevSlot(..)
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
  it "Tree_proof_return base case (b0): NRR slot + dummy self slot, end-to-end verify" \_ -> do
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
      , debug: true
      , wrapDomainOverride: Just 14
      }
      treeProofReturnRule

    let
      basePrevSelf = BasePrev
        { dummyStatement: StatementIO { input: unit, output: F (negate one) :: F StepField }
        }
    eTreeCp <- liftEffect $ runExceptT $ tree.prover.step
      { appInput: unit
      , prevs: Tuple (InductivePrev nrrCp nrr.tag) (Tuple basePrevSelf unit)
      }
    treeCp <- case eTreeCp of
      Left e -> liftEffect $ Exc.throw ("tree prover.step: " <> show e)
      Right p -> pure p

    verify (un Tag tree.tag).verifier [ treeCp ] `shouldEqual` true
