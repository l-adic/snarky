-- | The heterogeneous-prevs case: one rule with two prev slots, an
-- | `External` slot holding a proof of the separately compiled
-- | `nrrRule` (width 0) and a `Self` slot (width 2), compiled with the
-- | wrap domain overridden to 2^14.
-- |
-- | Slot 1's `proofMustVerify` is gated on the prev's output being -1,
-- | so b0 runs against a dummy self-prev while b1..b4 verify the
-- | previous tree proof. The chain must produce outputs 0..4 and verify
-- | in a single batch, so it fails if the two slots' verification keys
-- | are crossed, if the domain override is dropped, or if the base case
-- | stops being gated.
module Test.Pickles.Prove.TreeProofReturn
  ( spec
  , treeProofReturnRule
  ) where

import Prelude

import Colog (LoggerT, Message, logInfo, withSpan)
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
import Pickles (BranchProver(..), CompiledProof(..), PrevSlot(..), RulesCons, RulesNil, Slot, SlotProveVk(..), SlotWrapKey(..), StatementIO(..), StepField, StepRule, compileMulti, mkRuleEntry, toVerifiable, verifyBatch)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Kimchi.ProofCache (mkProofCache)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, const_, exists, if_, not_, true_)
import Snarky.Curves.Class (fromInt)
import Test.Pickles.SerializeRoundTrip (mkWidthDummies, roundTripAndVerify)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

type TreeProofReturnPrevsSpec =
  Tuple2
    (Slot 0 (StatementIO Unit (F StepField)))
    (Slot 2 (StatementIO Unit (F StepField)))

treeProofReturnRule
  :: StepRule 2
       (Tuple2 (StatementIO Unit (F StepField)) (StatementIO Unit (F StepField)))
       Unit
       Unit
       (F StepField)
       (FVar StepField)
       (F StepField)
       (FVar StepField)
treeProofReturnRule getPrevStates _ = do
  nrrInput <- exists $ getPrevStates <#> \(StatementIO { output: nrrOut } /\ _) -> nrrOut
  prevInput <- exists $ getPrevStates <#> \(_ /\ StatementIO { output: prevOut } /\ _) -> prevOut
  isBaseCase <- exists $ getPrevStates <#> \(_ /\ StatementIO { output: prevOut } /\ _) -> prevOut == F (negate one)
  let proofMustVerifySlot1 = not_ isBaseCase
  selfVal <- if_ isBaseCase (const_ zero) (CVar.add_ (const_ one) prevInput)
  pure
    { prevPublicInputs: nrrInput :< prevInput :< Vector.nil
    , proofMustVerify: true_ :< proofMustVerifySlot1 :< Vector.nil
    , publicOutput: selfVal
    }

nrrRule :: StepRule 0 Unit Unit Unit (F StepField) (FVar StepField) Unit Unit
nrrRule _ _ = pure
  { prevPublicInputs: Vector.nil
  , proofMustVerify: Vector.nil
  , publicOutput: const_ zero
  }

-- | Carrier for the single `nrrRule`, at width 0.
type NrrRules =
  RulesCons 0 Unit Unit
    RulesNil

-- | Carrier for the single `treeProofReturnRule`, at width 2.
type TreeRules =
  RulesCons 2
    (Tuple2 (StatementIO Unit (F StepField)) (StatementIO Unit (F StepField)))
    TreeProofReturnPrevsSpec
    RulesNil

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.TreeProofReturn" do
  it "5-iteration heterogeneous chain (b0..b4): NRR external slot + self-recursive slot, end-to-end verify" \{ pallasSrs, vestaSrs, lagrangeCache } -> do
    cache <- liftEffect $ lookupEnv "PICKLES_PROOF_CACHE_DIR" <#> map \dir -> mkProofCache (dir <> "/TreeProofReturn.json")

    nrrEntry <- liftEffect $ mkRuleEntry @0 @(F StepField) @Unit nrrRule Vector.nil

    let nrrRules = tuple1 nrrEntry

    logInfo "[TreeProofReturn] compiling nrr…"
    nrr <- withSpan "[TreeProofReturn] compile nrr" $ liftEffect $ compileMulti
      @NrrRules
      @(F StepField)
      @Unit
      @1
      noAdvice
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      , proofCache: cache
      , lagrangeCache: Just lagrangeCache
      }
      nrrRules

    let BranchProver nrrProver = fst nrr.provers
    logInfo "[TreeProofReturn] proving nrr"
    eNrrCp <- withSpan "[TreeProofReturn] prove nrr" $ liftEffect $ nrrProver noAdvice
      { appInput: unit, prevs: unit, sideloadedVKs: unit }
    nrrCp <- case eNrrCp of
      Left e -> liftEffect $ Exc.throw ("nrrProver: " <> show e)
      Right p -> pure p

    -- The `External` slot takes the imported system's `ProverVKs`,
    -- reassembled here from the multi-branch shape of `nrr.vks`.
    let
      nrrProverVKs =
        { stepCompileResult: fst nrr.vks.perBranchStep
        , wrapCompileResult: nrr.vks.wrap
        , wrapDomainLog2: nrr.vks.wrapDomainLog2
        , stepNumChunks: nrr.vks.stepChunks
        }

    treeEntry <- liftEffect $ mkRuleEntry @2 @(F StepField) @(F StepField)
      treeProofReturnRule
      (External nrrProverVKs :< Self :< Vector.nil)

    let treeRules = tuple1 treeEntry

    logInfo "[TreeProofReturn] compiling tree…"
    tree <- withSpan "[TreeProofReturn] compile tree" $ liftEffect $ compileMulti
      @TreeRules
      @(F StepField)
      @(F StepField)
      @1
      noAdvice
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Just 14
      , proofCache: cache
      , lagrangeCache: Just lagrangeCache
      }
      treeRules

    let BranchProver treeProver = fst tree.provers

    -- Every prev is round-tripped through serialization before it is
    -- consumed, so the chain closes only if that is faithful.
    let dummies = mkWidthDummies pallasSrs vestaSrs

    -- The same NRR proof fills slot 0 of every tree step, so it is
    -- round-tripped and verified once against its own verifier.
    nrrCp' <- roundTripAndVerify dummies nrr.verifier nrrCp

    let
      runStep
        :: PrevSlot Unit 2 (StatementIO Unit (F StepField))
        -> Aff (CompiledProof 2 (StatementIO Unit (F StepField)))
      runStep selfPrev = do
        eRes <- liftEffect $ treeProver noAdvice
          { appInput: unit
          , prevs:
              tuple2 (InductivePrev nrrCp' nrr.tag) selfPrev
          , sideloadedVKs: tuple2 NoSideLoadedVk NoSideLoadedVk
          }
        case eRes of
          Left e -> liftEffect $ Exc.throw ("treeProver: " <> show e)
          Right p -> pure p

      basePrevSelf = BasePrev
        { dummyStatement: StatementIO { input: unit, output: F (negate one) :: F StepField }
        }

    logInfo "[TreeProofReturn] proving [step0, wrap0]"
    b0 <- withSpan "[TreeProofReturn] prove b0" $ liftAff $ runStep basePrevSelf
    b0' <- roundTripAndVerify dummies tree.verifier b0
    logInfo "[TreeProofReturn] proving [step1, wrap1]"
    b1 <- withSpan "[TreeProofReturn] prove b1" $ liftAff $ runStep (InductivePrev b0' tree.tag)
    b1' <- roundTripAndVerify dummies tree.verifier b1
    logInfo "[TreeProofReturn] proving [step2, wrap2]"
    b2 <- withSpan "[TreeProofReturn] prove b2" $ liftAff $ runStep (InductivePrev b1' tree.tag)
    b2' <- roundTripAndVerify dummies tree.verifier b2
    logInfo "[TreeProofReturn] proving [step3, wrap3]"
    b3 <- withSpan "[TreeProofReturn] prove b3" $ liftAff $ runStep (InductivePrev b2' tree.tag)
    b3' <- roundTripAndVerify dummies tree.verifier b3
    logInfo "[TreeProofReturn] proving [step4, wrap4]"
    b4 <- withSpan "[TreeProofReturn] prove b4" $ liftAff $ runStep (InductivePrev b3' tree.tag)

    logInfo "[TreeProofReturn] verifying 5-proof chain…"
    verifyBatch tree.verifier (map toVerifiable [ b0, b1, b2, b3, b4 ]) `shouldEqual` true
    logInfo "[TreeProofReturn] verification complete"

    -- b0's dummy self-prev carries output -1, which trips the base case
    -- to 0; each later round increments its prev's output.
    let outputOf (CompiledProof p) = let StatementIO s = p.statement in s.output
    map outputOf [ b0, b1, b2, b3, b4 ] `shouldEqual`
      [ F zero, F one, F (fromInt 2), F (fromInt 3), F (fromInt 4) ]
