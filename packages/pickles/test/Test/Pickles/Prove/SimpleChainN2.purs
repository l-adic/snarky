-- | The merge shape: one self-recursive rule with two self prev slots,
-- | at width 2 with the wrap domain overridden to 2^14. The body
-- | asserts `self = 1 + prev1 + prev2`, short-circuited when
-- | `self = 0`, so b0 bootstraps from two dummies and b1 and b2 each
-- | verify two real proofs of this system.
-- |
-- | The constraint system is pinned separately, by
-- | `step_main_simple_chain_n2_circuit` in the circuit-diffs suite, so
-- | a failure here is in the prover's slot-0 witness assembly rather
-- | than in the circuit.
module Test.Pickles.Prove.SimpleChainN2
  ( spec
  , simpleChainN2Rule
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
import Pickles (BranchProver(..), CompiledProof, PrevSlot(..), PrevStatement(..), RulesCons, RulesNil, Slot, SlotWrapKey(..), StatementIO(..), StepField, StepRule, compileMulti, mkRuleEntry, prevValues, toPrevs, toVerifiable, verifyBatch)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Kimchi.ProofCache (mkProofCache)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, assertAny_, const_, equals_, exists, not_)
import Test.Pickles.SerializeRoundTrip (mkWidthDummies, roundTripAndVerify)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

type Stmt = StatementIO (F StepField) Unit

-- | Asserts `self = 1 + prev1 + prev2`, bypassed when `self = 0`. Both
-- | slots are self prevs and share one `proofMustVerify`.
simpleChainN2Rule
  :: StepRule SimpleChainN2PrevsSpec
       (F StepField)
       (FVar StepField)
       Unit
       Unit
simpleChainN2Rule getPrevStates self = do
  prev1 <- exists $ getPrevStates <#> prevValues <#> \(StatementIO p1 /\ _) -> p1.input
  prev2 <- exists $ getPrevStates <#> prevValues <#> \(_ /\ StatementIO p2 /\ _) -> p2.input
  isBaseCase <- equals_ (const_ zero) self
  let proofMustVerify = not_ isBaseCase
  selfCorrect <- equals_ (CVar.add_ (CVar.add_ (const_ one) prev1) prev2) self
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevs: toPrevs $
        PrevStatement { publicInput: StatementIO { input: prev1, output: unit }, proofMustVerify }
          /\ PrevStatement { publicInput: StatementIO { input: prev2, output: unit }, proofMustVerify }
          /\ unit
    , publicOutput: unit
    }

-- | The rule's two self prev slots, each at width 2.
type SimpleChainN2PrevsSpec =
  Tuple2 (Slot 2 (StatementIO (F StepField) Unit)) (Slot 2 (StatementIO (F StepField) Unit))

-- | Carrier for the single rule.
type SimpleChainN2Rules =
  RulesCons 2
    SimpleChainN2PrevsSpec
    RulesNil

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.SimpleChainN2" do
  it "b0..b2 chain (prevs = [self; self], N2): prove + verify" \{ pallasSrs, vestaSrs, lagrangeCache } -> do
    cache <- liftEffect $ lookupEnv "PICKLES_PROOF_CACHE_DIR" <#> map \dir -> mkProofCache (dir <> "/SimpleChainN2.json")

    let
      cfg =
        { srs: { vestaSrs, pallasSrs }
        , debug: false
        , wrapDomainOverride: Just 14
        , proofCache: cache
        , lagrangeCache: Just lagrangeCache
        }

    entry <- liftEffect $ mkRuleEntry @2 @Unit
      simpleChainN2Rule
      (Self :< Self :< Vector.nil)

    let rules = tuple1 entry

    logInfo "[SimpleChainN2] compiling…"
    out <- withSpan "[SimpleChainN2] compile" $ liftEffect $ compileMulti
      @SimpleChainN2Rules
      @Unit
      @1
      noAdvice
      cfg
      rules

    let BranchProver prover = fst out.provers

    -- Every prev is round-tripped through serialization before it is
    -- consumed, so the chain closes only if that is faithful.
    let dummies = mkWidthDummies pallasSrs vestaSrs

    let
      runStep
        :: F StepField
        -> PrevSlot (F StepField) 2 Stmt
        -> PrevSlot (F StepField) 2 Stmt
        -> Aff (CompiledProof 2 Stmt)
      runStep appInput prev1 prev2 = do
        eRes <- liftEffect $ prover noAdvice
          { appInput
          , prevs: tuple2 prev1 prev2
          }
        case eRes of
          Left e -> liftEffect $ Exc.throw ("SimpleChainN2 prover: " <> show e)
          Right p -> pure p

      -- The base case bypasses the sum, so the dummy statement's input
      -- is arbitrary.
      baseDummy = BasePrev
        { dummyStatement: StatementIO { input: F zero :: F StepField, output: unit }
        }

    logInfo "[SimpleChainN2] proving b0 (self=0, base case)"
    b0 <- withSpan "[SimpleChainN2] prove b0" $ liftAff $ runStep (F zero) baseDummy baseDummy
    b0' <- roundTripAndVerify dummies out.verifier b0
    logInfo "[SimpleChainN2] proving b1 (self=1, verifies [b0, b0])"
    b1 <- withSpan "[SimpleChainN2] prove b1" $ liftAff $ runStep (F one) (InductivePrev b0' out.tag) (InductivePrev b0' out.tag)
    b1' <- roundTripAndVerify dummies out.verifier b1
    logInfo "[SimpleChainN2] proving b2 (self=2, verifies [b1, b0])"
    b2 <- withSpan "[SimpleChainN2] prove b2" $ liftAff $ runStep (F (one + one)) (InductivePrev b1' out.tag) (InductivePrev b0' out.tag)

    logInfo "[SimpleChainN2] verifying 3-proof chain…"
    verifyBatch out.verifier (map toVerifiable [ b0, b1, b2 ]) `shouldEqual` true
    logInfo "[SimpleChainN2] verification complete"
