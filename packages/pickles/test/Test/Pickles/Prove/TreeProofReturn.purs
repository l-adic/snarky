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
import Pickles (ApplicationStatement(..), CompiledProof(..), PrevSlot, PrevStatement(..), Slot, SlotWrapKey(..), StepField, StepRule, compileMulti, mkRuleEntry, prevValues, proveBranch, provedPrev, toPrevs, toVerifiable, unprovedPrev, verifyBatch)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, const_, exists, if_, not_, readCVar, true_)
import Snarky.Curves.Class (fromInt)
import Test.Pickles.Outputs (appOutputs)
import Test.Pickles.SerializeRoundTrip (mkWidthDummies, roundTripAndVerify)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

type TreeProofReturnPrevsSpec =
  Tuple2
    (Slot 0 (ApplicationStatement Unit (F StepField)))
    (Slot 2 (ApplicationStatement Unit (F StepField)))

treeProofReturnRule
  :: StepRule TreeProofReturnPrevsSpec
       Unit
       Unit
       (F StepField)
       (FVar StepField)
treeProofReturnRule getPrevStates _ = do
  nrrInput <- exists $ getPrevStates <#> prevValues <#> \(ApplicationStatement { output: nrrOut } /\ _) -> nrrOut
  prevInput <- exists $ getPrevStates <#> prevValues <#> \(_ /\ ApplicationStatement { output: prevOut } /\ _) -> prevOut
  isBaseCase <- exists $ readCVar prevInput <#> (_ == F (negate one))
  let proofMustVerifySlot1 = not_ isBaseCase
  selfVal <- if_ isBaseCase (const_ zero) (CVar.add_ (const_ one) prevInput)
  pure
    { prevs: toPrevs $
        PrevStatement { publicInput: ApplicationStatement { input: unit, output: nrrInput }, proofMustVerify: true_ }
          /\ PrevStatement { publicInput: ApplicationStatement { input: unit, output: prevInput }, proofMustVerify: proofMustVerifySlot1 }
          /\ unit
    , publicOutput: selfVal
    }

nrrRule :: StepRule Unit Unit Unit (F StepField) (FVar StepField)
nrrRule _ _ = pure
  { prevs: toPrevs unit
  , publicOutput: const_ zero
  }

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.TreeProofReturn" do
  it "5-iteration heterogeneous chain (b0..b4): NRR external slot + self-recursive slot, end-to-end verify" \{ pallasSrs, vestaSrs, lagrangeCache } -> do
    outputs <- liftEffect $ appOutputs "TreeProofReturn"

    nrrEntry <- liftEffect $ mkRuleEntry @(F StepField) nrrRule Vector.nil

    let nrrRules = tuple1 nrrEntry

    logInfo "[TreeProofReturn] compiling nrr…"
    nrr <- withSpan "[TreeProofReturn] compile nrr" $ liftEffect $ compileMulti
      @(F StepField)
      @1
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      , proofCache: outputs.proofCache
      , lagrangeCache: Just lagrangeCache
      , dump: outputs.dumpAt "nrr"
      }
      nrrRules

    let nrrProver = proveBranch (fst nrr.provers)
    logInfo "[TreeProofReturn] proving nrr"
    eNrrCp <- withSpan "[TreeProofReturn] prove nrr" $ liftEffect $ nrrProver noAdvice
      { appInput: unit, prevs: unit }
    nrrCp <- case eNrrCp of
      Left e -> liftEffect $ Exc.throw ("nrrProver: " <> show e)
      Right p -> pure p

    treeEntry <- liftEffect $ mkRuleEntry @(F StepField)
      treeProofReturnRule
      (External nrr.tagData :< Self :< Vector.nil)

    let treeRules = tuple1 treeEntry

    logInfo "[TreeProofReturn] compiling tree…"
    tree <- withSpan "[TreeProofReturn] compile tree" $ liftEffect $ compileMulti
      @(F StepField)
      @1
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Just 14
      , proofCache: outputs.proofCache
      , lagrangeCache: Just lagrangeCache
      , dump: outputs.dumpAt "tree"
      }
      treeRules

    let treeProver = proveBranch (fst tree.provers)

    -- Every prev is round-tripped through serialization before it is
    -- consumed, so the chain closes only if that is faithful.
    let dummies = mkWidthDummies pallasSrs

    -- The same NRR proof fills slot 0 of every tree step, so it is
    -- round-tripped and verified once against its own verifier.
    nrrCp' <- roundTripAndVerify dummies nrr.verifier nrrCp

    let
      runStep
        :: PrevSlot Unit 2 (ApplicationStatement Unit (F StepField))
        -> Aff (CompiledProof 2 (ApplicationStatement Unit (F StepField)))
      runStep selfPrev = do
        eRes <- liftEffect $ treeProver noAdvice
          { appInput: unit
          , prevs:
              tuple2 (provedPrev nrrCp') selfPrev
          }
        case eRes of
          Left e -> liftEffect $ Exc.throw ("treeProver: " <> show e)
          Right p -> pure p

      basePrevSelf = unprovedPrev $ ApplicationStatement { input: unit, output: F (negate one) :: F StepField }

    logInfo "[TreeProofReturn] proving [step0, wrap0]"
    b0 <- withSpan "[TreeProofReturn] prove b0" $ liftAff $ runStep basePrevSelf
    b0' <- roundTripAndVerify dummies tree.verifier b0
    logInfo "[TreeProofReturn] proving [step1, wrap1]"
    b1 <- withSpan "[TreeProofReturn] prove b1" $ liftAff $ runStep (provedPrev b0')
    b1' <- roundTripAndVerify dummies tree.verifier b1
    logInfo "[TreeProofReturn] proving [step2, wrap2]"
    b2 <- withSpan "[TreeProofReturn] prove b2" $ liftAff $ runStep (provedPrev b1')
    b2' <- roundTripAndVerify dummies tree.verifier b2
    logInfo "[TreeProofReturn] proving [step3, wrap3]"
    b3 <- withSpan "[TreeProofReturn] prove b3" $ liftAff $ runStep (provedPrev b2')
    b3' <- roundTripAndVerify dummies tree.verifier b3
    logInfo "[TreeProofReturn] proving [step4, wrap4]"
    b4 <- withSpan "[TreeProofReturn] prove b4" $ liftAff $ runStep (provedPrev b3')

    logInfo "[TreeProofReturn] verifying 5-proof chain…"
    verifyBatch tree.verifier (map toVerifiable [ b0, b1, b2, b3, b4 ]) `shouldEqual` true
    logInfo "[TreeProofReturn] verification complete"

    -- b0's dummy self-prev carries output -1, which trips the base case
    -- to 0; each later round increments its prev's output.
    let outputOf (CompiledProof p) = let ApplicationStatement s = p.statement in s.output
    map outputOf [ b0, b1, b2, b3, b4 ] `shouldEqual`
      [ F zero, F one, F (fromInt 2), F (fromInt 3), F (fromInt 4) ]
