-- | The self-recursive chain: one rule asserting `self == prev + 1` at
-- | width 1, proved through five iterations b0..b4. A single
-- | `compileMulti` call yields the `BranchProver` every iteration uses,
-- | and each proof is round-tripped through JSON before being threaded
-- | into the next as `InductivePrev`.
-- |
-- | The chain must verify in one batch and carry the inputs 0..4, and
-- | three tampered variants of b1 must be rejected. It therefore fails
-- | if serialization loses anything, if the chained statements drift,
-- | or if the verifier stops recomputing the message digests.
module Test.Pickles.Prove.SimpleChain
  ( spec
  , simpleChainRule
  ) where

import Prelude

import Colog (LoggerT, Message, logInfo, withSpan)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (Tuple1, tuple1, (/\))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Node.Process (lookupEnv)
import Pickles (BranchProver(..), CompiledProof(..), PrevSlot(..), PrevStatement(..), RulesCons, RulesNil, Slot, SlotProveVk(..), SlotWrapKey(..), StatementIO(..), StepField, StepRule, compileMulti, mkRuleEntry, prevValues, toPrevs, toVerifiable, verify, verifyBatch)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Kimchi.ProofCache (mkProofCache)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, assertAny_, const_, equals_, exists, not_)
import Snarky.Circuit.Types (NoOutput(..))
import Snarky.Curves.Class (fromInt)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Test.Pickles.SerializeRoundTrip (roundTripJSONAndVerify)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | Asserts `self == prev + 1`, or `self == 0` for the base case. The
-- | prev's app state is read through `getPrevStates`, so one compiled
-- | rule serves every iteration: b0 passes a `BasePrev` dummy
-- | statement, b_{k+1} passes `InductivePrev` on b_k.
simpleChainRule
  :: StepRule SimpleChainPrevsSpec
       (F StepField)
       (FVar StepField)
       NoOutput
       NoOutput
simpleChainRule getPrevStates self = do
  prev <- exists $ getPrevStates <#> prevValues <#> \(StatementIO { input } /\ _) -> input
  isBaseCase <- equals_ (const_ zero) self
  let proofMustVerify = not_ isBaseCase
  selfCorrect <- equals_ (CVar.add_ (const_ one) prev) self
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevs: toPrevs $
        PrevStatement { publicInput: StatementIO { input: prev, output: NoOutput }, proofMustVerify }
          /\ unit
    , publicOutput: NoOutput
    }

-- | The rule's one self-recursive prev slot, at width 1.
type SimpleChainPrevsSpec =
  Tuple1 (Slot 1 (StatementIO (F StepField) NoOutput))

-- | Carrier for the single rule.
type SimpleChainRules =
  RulesCons 1
    SimpleChainPrevsSpec
    RulesNil

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.SimpleChain" do
  it "5-iteration step+wrap chain (b0..b4) proves end-to-end" \{ pallasSrs, vestaSrs, lagrangeCache } -> do
    cache <- liftEffect $ lookupEnv "PICKLES_PROOF_CACHE_DIR" <#> map \dir -> mkProofCache (dir <> "/SimpleChain.json")

    chainEntry <- liftEffect $ mkRuleEntry @1 @NoOutput simpleChainRule (Self :< Vector.nil)

    let rules = tuple1 chainEntry

    logInfo "[SimpleChain] compiling…"
    output <- withSpan "[SimpleChain] compile" $ liftEffect $ compileMulti
      @SimpleChainRules
      @NoOutput
      @1
      noAdvice
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      , proofCache: cache
      , lagrangeCache: Just lagrangeCache
      }
      rules

    let BranchProver chainProver = fst output.provers

    -- Every prev is round-tripped through serialization before it is
    -- consumed, so the assertions below also witness that round trip.
    let srs = { pallasSrs, vestaSrs }

    let
      runStep
        :: PrevSlot (F StepField) 1 (StatementIO (F StepField) NoOutput)
        -> F StepField
        -> Aff (CompiledProof 1 (StatementIO (F StepField) NoOutput))
      runStep prevSlot appInput = do
        eRes <- liftEffect $ chainProver noAdvice
          { appInput, prevs: tuple1 prevSlot, sideloadedVKs: tuple1 NoSideLoadedVk }
        case eRes of
          Left e -> liftEffect $ Exc.throw ("chainProver: " <> show e)
          Right p -> pure p

      basePrev = BasePrev
        { dummyStatement: StatementIO { input: F (negate one), output: NoOutput } }

    logInfo "[SimpleChain] proving [step0, wrap0]"
    b0 <- withSpan "[SimpleChain] prove b0" $ liftAff $ runStep basePrev (F zero)
    b0' <- roundTripJSONAndVerify srs output.verifier b0
    logInfo "[SimpleChain] proving [step1, wrap1]"
    b1 <- withSpan "[SimpleChain] prove b1" $ liftAff $ runStep (InductivePrev b0' output.tag) (F one)
    b1' <- roundTripJSONAndVerify srs output.verifier b1
    logInfo "[SimpleChain] proving [step2, wrap2]"
    b2 <- withSpan "[SimpleChain] prove b2" $ liftAff $ runStep (InductivePrev b1' output.tag) (F (fromInt 2 :: StepField))
    b2' <- roundTripJSONAndVerify srs output.verifier b2
    logInfo "[SimpleChain] proving [step3, wrap3]"
    b3 <- withSpan "[SimpleChain] prove b3" $ liftAff $ runStep (InductivePrev b2' output.tag) (F (fromInt 3 :: StepField))
    b3' <- roundTripJSONAndVerify srs output.verifier b3
    logInfo "[SimpleChain] proving [step4, wrap4]"
    b4 <- withSpan "[SimpleChain] prove b4" $ liftAff $ runStep (InductivePrev b3' output.tag) (F (fromInt 4 :: StepField))

    logInfo "[SimpleChain] verifying 5-proof chain…"
    verifyBatch output.verifier (map toVerifiable [ b0, b1, b2, b3, b4 ]) `shouldEqual` true
    logInfo "[SimpleChain] verification complete"

    -- The verifier recomputes both message digests, so b1 presented
    -- with a different application state, a different previous opening
    -- `sg`, or different previous wrap challenges must be rejected.
    let vp1 = toVerifiable b1
    verify output.verifier (vp1 { appState = map (add one) vp1.appState }) `shouldEqual` false
    verify output.verifier
      (vp1 { prevChallengePolynomialCommitments = map (\(AffinePoint pt) -> AffinePoint pt { x = pt.x + one }) vp1.prevChallengePolynomialCommitments })
      `shouldEqual` false
    verify output.verifier
      (vp1 { prevWrapBulletproofChallenges = map (map (add one)) vp1.prevWrapBulletproofChallenges })
      `shouldEqual` false

    -- Each proof's carried app state must be the `appInput` its prove
    -- was given, which the rule pins to 0..4 along the chain.
    let
      stmtInputOf (CompiledProof p) =
        let StatementIO s = p.statement in s.input
    map stmtInputOf [ b0, b1, b2, b3, b4 ] `shouldEqual`
      [ F zero, F one, F (fromInt 2), F (fromInt 3), F (fromInt 4) ]
