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
-- | Compile-API driven via `compileMulti` + `BranchProver` closures:
-- | one 1-rule compile for NRR, one 1-rule compile for the Tree rule
-- | (with the NRR compile's VKs threaded through `External` for slot 0).
-- | Iterates the full chain b0..b4 (matching SimpleChain's iteration
-- | depth):
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
import Data.Tuple (Tuple(..), fst)
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Pickles.Prove.Compile (CompiledProof(..), PrevSlot(..), SlotWrapKey(..))
import Pickles.Prove.CompileMulti
  ( BranchProver(..)
  , RulesCons
  , RulesNil
  , compileMulti
  , mkRuleEntry
  )
import Pickles.Prove.Step (StepRule)
import Pickles.Prove.Verify (verify)
import Pickles.Step.Advice (getPrevAppStates)
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil)
import Pickles.Types (StatementIO(..), StepField)
import Pickles.Wrap.Slots (NoSlots, Slots2)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, const_, exists, if_, not_, true_)
import Snarky.Curves.Class (fromInt)
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

-- | NRR's 1-rule carrier (same shape as the standalone NRR test). NRR
-- | output is a Field, so the StepRule's outputVal is `F StepField`.
type NrrRules =
  RulesCons 0 Unit PrevsSpecNil Unit
    RulesNil

-- | Tree_proof_return's 1-rule carrier. Two prev slots: an NRR external
-- | (mpv=0) and a self-recursive (mpv=2).
type TreeRules =
  RulesCons 2
    ( Tuple (StatementIO Unit (F StepField))
        (Tuple (StatementIO Unit (F StepField)) Unit)
    )
    TreeProofReturnPrevsSpec
    (Tuple SlotWrapKey (Tuple SlotWrapKey Unit))
    RulesNil

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.TreeProofReturn" do
  it "5-iteration heterogeneous chain (b0..b4): NRR external slot + self-recursive slot, end-to-end verify" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField

    -- ===== NRR side: 1-rule compileMulti at mpvMax=0. =====
    nrrEntry <- liftEffect $ mkRuleEntry
      @PrevsSpecNil
      @0 -- mpv
      @0 -- mpvMax
      @0 -- mpvPad
      @1 -- nd = topBranches (single branch)
      @1 -- outputSize = 0*32+1+0 = 1
      @Unit
      @Unit
      @Unit
      @(F StepField)
      @(FVar StepField)
      @Unit
      @Unit
      @Unit
      nrrRule
      unit

    let nrrRules = Tuple nrrEntry unit

    nrr <- liftEffect $ compileMulti
      @NrrRules
      @Unit
      @(F StepField)
      @Unit
      @0
      @NoSlots
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      }
      nrrRules

    let BranchProver nrrProver = fst nrr.provers
    eNrrCp <- liftEffect $ runExceptT $ nrrProver { appInput: unit, prevs: unit }
    nrrCp <- case eNrrCp of
      Left e -> liftEffect $ Exc.throw ("nrrProver: " <> show e)
      Right p -> pure p

    -- The Tree rule's `External` slot needs the imported NRR's
    -- `ProverVKs` shape — extracted from `nrr.vks` (multi shape) by
    -- pulling the single branch's `StepCompileResult` out of the
    -- 1-tuple `perBranchStep`.
    let
      nrrProverVKs =
        { stepCompileResult: fst nrr.vks.perBranchStep
        , wrapCompileResult: nrr.vks.wrap
        , wrapDomainLog2: nrr.vks.wrapDomainLog2
        }

    -- ===== Tree side: 1-rule compileMulti at mpvMax=2 with override. =====
    treeEntry <- liftEffect $ mkRuleEntry
      @TreeProofReturnPrevsSpec
      @2 -- mpv
      @2 -- mpvMax
      @0 -- mpvPad
      @1 -- nd = topBranches (single branch)
      @67 -- outputSize = 2*32+1+2 = 67
      @( Tuple (StatementIO Unit (F StepField))
           (Tuple (StatementIO Unit (F StepField)) Unit)
       )
      @Unit
      @Unit
      @(F StepField)
      @(FVar StepField)
      @(F StepField)
      @(FVar StepField)
      @(Tuple SlotWrapKey (Tuple SlotWrapKey Unit))
      treeProofReturnRule
      (Tuple (External nrrProverVKs) (Tuple Self unit))

    let treeRules = Tuple treeEntry unit

    tree <- liftEffect $ compileMulti
      @TreeRules
      @Unit
      @(F StepField)
      @(F StepField)
      @2
      @(Slots2 0 2)
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Just 14
      }
      treeRules

    let BranchProver treeProver = fst tree.provers

    let
      runStep
        :: PrevSlot Unit 2 (StatementIO Unit (F StepField)) (F StepField)
        -> Aff (CompiledProof 2 (StatementIO Unit (F StepField)) (F StepField) Unit)
      runStep selfPrev = do
        eRes <- liftEffect $ runExceptT $ treeProver
          { appInput: unit
          , prevs:
              Tuple (InductivePrev nrrCp nrr.tag)
                (Tuple selfPrev unit)
          }
        case eRes of
          Left e -> liftEffect $ Exc.throw ("treeProver: " <> show e)
          Right p -> pure p

      basePrevSelf = BasePrev
        { dummyStatement: StatementIO { input: unit, output: F (negate one) :: F StepField }
        }

    b0 <- runStep basePrevSelf
    b1 <- runStep (InductivePrev b0 tree.tag)
    b2 <- runStep (InductivePrev b1 tree.tag)
    b3 <- runStep (InductivePrev b2 tree.tag)
    b4 <- runStep (InductivePrev b3 tree.tag)

    verify tree.verifier [ b0, b1, b2, b3, b4 ] `shouldEqual` true

    -- The rule body computes `selfVal = if isBaseCase then 0 else
    -- 1 + prevInput`, exposed as `publicOutput`. Base case b0 takes
    -- `BasePrev { output = -1 }` which trips `isBaseCase` → output 0.
    -- Each subsequent b_k+1 reads b_k's output and increments,
    -- producing 0..4 as the running counter.
    let outputOf (CompiledProof p) = p.publicOutput
    map outputOf [ b0, b1, b2, b3, b4 ] `shouldEqual`
      [ F zero, F one, F (fromInt 2), F (fromInt 3), F (fromInt 4) ]
