-- | PureScript-side analog of OCaml's `Tree_proof_return` test
-- | (`mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:315-429`).
-- |
-- | Tree_proof_return is the heterogeneous-prevs target:
-- |
-- |   prevs = [No_recursion_return.tag; self]
-- |   max_proofs_verified = N2
-- |   per-slot widths      = [0, 2]
-- |   override_wrap_domain = N1  → wrap_domains.h = 2^14
-- |   public_input         = Output StepField
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

import Colog (LoggerT, Message, logInfo, withSpan)
import Control.Monad.Except (runExceptT)
import Control.Monad.Trans.Class (lift) as MT
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (Tuple2, tuple1, tuple2, (/\))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Node.Process (lookupEnv)
import Pickles (BranchProver(..), Compiled, CompiledProof(..), NoSlots, PrevSlot(..), RulesCons, RulesNil, Slot, SlotWrapKey(..), Slots2, StatementIO(..), StepField, StepRule, compileMulti, getPrevAppStates, mkRuleEntry, verify)
import Pickles.ProofCache (mkProofCache)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, const_, exists, if_, not_, true_)
import Snarky.Curves.Class (fromInt)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

type TreeProofReturnPrevsSpec =
  Tuple2
    (Slot Compiled 0 1 (StatementIO Unit (F StepField)))
    (Slot Compiled 2 1 (StatementIO Unit (F StepField)))

treeProofReturnRule
  :: StepRule 2
       (Tuple2 (StatementIO Unit (F StepField)) (StatementIO Unit (F StepField)))
       Unit
       Unit
       (F StepField)
       (FVar StepField)
       (F StepField)
       (FVar StepField)
treeProofReturnRule _ = do
  nrrInput <- exists $ MT.lift do
    StatementIO { output: nrrOut } /\ _ <- getPrevAppStates unit
    pure nrrOut
  prevInput <- exists $ MT.lift do
    _ /\ StatementIO { output: prevOut } /\ _ <- getPrevAppStates unit
    pure prevOut
  isBaseCase <- exists $ MT.lift do
    _ /\ StatementIO { output: prevOut } /\ _ <- getPrevAppStates unit
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
-- | output is a StepField, so the StepRule's outputVal is `F StepField`.
type NrrRules =
  RulesCons 0 Unit Unit Unit
    RulesNil

-- | Tree_proof_return's 1-rule carrier. Two prev slots: an NRR external
-- | (mpv=0) and a self-recursive (mpv=2).
type TreeRules =
  RulesCons 2
    (Tuple2 (StatementIO Unit (F StepField)) (StatementIO Unit (F StepField)))
    TreeProofReturnPrevsSpec
    (Tuple2 SlotWrapKey SlotWrapKey)
    RulesNil

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.TreeProofReturn" do
  it "5-iteration heterogeneous chain (b0..b4): NRR external slot + self-recursive slot, end-to-end verify" \{ pallasSrs, vestaSrs } -> do
    cache <- liftEffect $ lookupEnv "PICKLES_PROOF_CACHE_DIR" <#> map \dir -> mkProofCache (dir <> "/TreeProofReturn.json")

    -- ===== NRR side: 1-rule compileMulti at mpvMax=0. =====
    nrrEntry <- liftEffect $ mkRuleEntry @0 @(F StepField) @Unit @1 @1 nrrRule unit

    let nrrRules = tuple1 nrrEntry

    logInfo "[TreeProofReturn] compiling nrr…"
    nrr <- withSpan "[TreeProofReturn] compile nrr" $ liftEffect $ compileMulti
      @NrrRules
      @(F StepField)
      @Unit
      @NoSlots
      @1
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      , proofCache: cache
      }
      nrrRules

    let BranchProver nrrProver = fst nrr.provers
    -- NRR has no prev slots → spec-derived `vkCarrier = Unit`.
    logInfo "[TreeProofReturn] proving nrr"
    eNrrCp <- withSpan "[TreeProofReturn] prove nrr" $ liftEffect $ runExceptT $ nrrProver
      { appInput: unit, prevs: unit, sideloadedVKs: unit }
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
        , stepNumChunks: nrr.vks.stepChunks
        }

    -- ===== Tree side: 1-rule compileMulti at mpvMax=2 with override. =====
    treeEntry <- liftEffect $ mkRuleEntry @2 @(F StepField) @(F StepField) @1 @1
      treeProofReturnRule
      (tuple2 (External nrrProverVKs) Self)

    let treeRules = tuple1 treeEntry

    logInfo "[TreeProofReturn] compiling tree…"
    tree <- withSpan "[TreeProofReturn] compile tree" $ liftEffect $ compileMulti
      @TreeRules
      @(F StepField)
      @(F StepField)
      @(Slots2 0 2)
      @1
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Just 14
      , proofCache: cache
      }
      treeRules

    let BranchProver treeProver = fst tree.provers

    let
      runStep
        :: PrevSlot Unit 2 (StatementIO Unit (F StepField)) (F StepField)
        -> Aff (CompiledProof 2 (StatementIO Unit (F StepField)) (F StepField))
      runStep selfPrev = do
        eRes <- liftEffect $ runExceptT $ treeProver
          { appInput: unit
          , prevs:
              tuple2 (InductivePrev nrrCp nrr.tag) selfPrev
          , sideloadedVKs: tuple2 unit unit
          }
        case eRes of
          Left e -> liftEffect $ Exc.throw ("treeProver: " <> show e)
          Right p -> pure p

      basePrevSelf = BasePrev
        { dummyStatement: StatementIO { input: unit, output: F (negate one) :: F StepField }
        }

    logInfo "[TreeProofReturn] proving [step0, wrap0]"
    b0 <- withSpan "[TreeProofReturn] prove b0" $ liftAff $ runStep basePrevSelf
    logInfo "[TreeProofReturn] proving [step1, wrap1]"
    b1 <- withSpan "[TreeProofReturn] prove b1" $ liftAff $ runStep (InductivePrev b0 tree.tag)
    logInfo "[TreeProofReturn] proving [step2, wrap2]"
    b2 <- withSpan "[TreeProofReturn] prove b2" $ liftAff $ runStep (InductivePrev b1 tree.tag)
    logInfo "[TreeProofReturn] proving [step3, wrap3]"
    b3 <- withSpan "[TreeProofReturn] prove b3" $ liftAff $ runStep (InductivePrev b2 tree.tag)
    logInfo "[TreeProofReturn] proving [step4, wrap4]"
    b4 <- withSpan "[TreeProofReturn] prove b4" $ liftAff $ runStep (InductivePrev b3 tree.tag)

    logInfo "[TreeProofReturn] verifying 5-proof chain…"
    verify tree.verifier [ b0, b1, b2, b3, b4 ] `shouldEqual` true
    logInfo "[TreeProofReturn] verification complete"

    -- The rule body computes `selfVal = if isBaseCase then 0 else
    -- 1 + prevInput`, exposed as `publicOutput`. Base case b0 takes
    -- `BasePrev { output = -1 }` which trips `isBaseCase` → output 0.
    -- Each subsequent b_k+1 reads b_k's output and increments,
    -- producing 0..4 as the running counter.
    let outputOf (CompiledProof p) = p.publicOutput
    map outputOf [ b0, b1, b2, b3, b4 ] `shouldEqual`
      [ F zero, F one, F (fromInt 2), F (fromInt 3), F (fromInt 4) ]
