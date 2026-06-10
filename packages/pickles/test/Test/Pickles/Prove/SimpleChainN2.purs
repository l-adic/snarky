-- | PureScript-side prove test for OCaml's `Simple_chain` at N2
-- | (`mina/src/lib/crypto/pickles/dump_simple_chain_n2/dump_simple_chain_n2.ml`):
-- | a single self-recursive rule with TWO self prev slots
-- | (`prevs = [self; self]`), `max_proofs_verified = N2`,
-- | `override_wrap_domain = N1`.
-- |
-- | Rule body (trivial counter): `self = 1 + prev1 + prev2`, with an
-- | `is_base_case` short-circuit when `self = 0`. The base case b0
-- | bootstraps from two dummy prevs; each subsequent node verifies two
-- | real proofs of THIS system in slots 0 and 1.
-- |
-- | This is the minimal reproduction of the merge / "Self prev in slot 0
-- | at N2" path (the constraint system matches OCaml byte-for-byte — see
-- | `step_main_simple_chain_n2_circuit` in the circuit-diffs suite — so
-- | any divergence here is prover-side, in the slot-0 witness assembly).
module Test.Pickles.Prove.SimpleChainN2
  ( spec
  , simpleChainN2Rule
  ) where

import Prelude

import Colog (LoggerT, Message, logInfo, withSpan)
import Control.Monad.Except (runExceptT)
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
import Pickles (BranchProver(..), Compiled, CompiledProof, PrevSlot(..), RulesCons, RulesNil, Slot, SlotWrapKey(..), Slots2, StatementIO(..), StepField, StepRule, compileMulti, mkRuleEntry, toVerifiable, verifyBatch)
import Snarky.Backend.Kimchi.ProofCache (mkProofCache)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, assertAny_, const_, equals_, exists, not_)
import Test.Pickles.SerializeRoundTrip (mkWidthDummies, roundTripAndVerify)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

type Stmt = StatementIO (F StepField) Unit

-- | Simple_chain N2 rule: `self = 1 + prev1 + prev2` (bypassed when
-- | `self = 0`). Both prev slots are self; both share the same
-- | `proof_must_verify = not is_base_case`.
simpleChainN2Rule
  :: StepRule 2
       (Tuple2 (StatementIO (F StepField) Unit) (StatementIO (F StepField) Unit))
       (F StepField)
       (FVar StepField)
       Unit
       Unit
       (F StepField)
       (FVar StepField)
simpleChainN2Rule getPrevStates self = do
  prev1 <- exists $ getPrevStates <#> \(StatementIO p1 /\ _) -> p1.input
  prev2 <- exists $ getPrevStates <#> \(_ /\ StatementIO p2 /\ _) -> p2.input
  isBaseCase <- equals_ (const_ zero) self
  let proofMustVerify = not_ isBaseCase
  selfCorrect <- equals_ (CVar.add_ (CVar.add_ (const_ one) prev1) prev2) self
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevPublicInputs: prev1 :< prev2 :< Vector.nil
    , proofMustVerify: proofMustVerify :< proofMustVerify :< Vector.nil
    , publicOutput: unit
    }

-- | Single-rule carrier: one rule with two self prev slots (each width 2).
type SimpleChainN2Rules =
  RulesCons 2
    (Tuple2 (StatementIO (F StepField) Unit) (StatementIO (F StepField) Unit))
    (Tuple2 (Slot Compiled 2 1 (StatementIO (F StepField) Unit)) (Slot Compiled 2 1 (StatementIO (F StepField) Unit)))
    (Tuple2 SlotWrapKey SlotWrapKey)
    RulesNil

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.SimpleChainN2" do
  it "b0..b2 chain (prevs = [self; self], N2): prove + verify" \{ pallasSrs, vestaSrs } -> do
    cache <- liftEffect $ lookupEnv "PICKLES_PROOF_CACHE_DIR" <#> map \dir -> mkProofCache (dir <> "/SimpleChainN2.json")

    let
      cfg =
        { srs: { vestaSrs, pallasSrs }
        , debug: false
        -- Matches dump_simple_chain_n2.ml `override_wrap_domain:N1` (2^14).
        , wrapDomainOverride: Just 14
        , proofCache: cache
        }

    entry <- liftEffect $ mkRuleEntry @2 @Unit @(F StepField) @1 @1
      simpleChainN2Rule
      (tuple2 Self Self)

    let rules = tuple1 entry

    logInfo "[SimpleChainN2] compiling…"
    out <- withSpan "[SimpleChainN2] compile" $ liftEffect $ compileMulti
      @SimpleChainN2Rules
      @Unit
      @(F StepField)
      @(Slots2 2 2)
      @1
      cfg
      rules

    let BranchProver prover = fst out.provers

    -- Round-trip every recursive prev through SerializeProof; faithful
    -- reconstruction leaves the chain byte-identical so the assertions hold.
    let dummies = mkWidthDummies pallasSrs vestaSrs

    let
      runStep
        :: F StepField
        -> PrevSlot (F StepField) 2 Stmt
        -> PrevSlot (F StepField) 2 Stmt
        -> Aff (CompiledProof 2 Stmt)
      runStep appInput prev1 prev2 = do
        eRes <- liftEffect $ runExceptT $ prover
          { appInput
          , prevs: tuple2 prev1 prev2
          , sideloadedVKs: tuple2 unit unit
          }
        case eRes of
          Left e -> liftEffect $ Exc.throw ("SimpleChainN2 prover: " <> show e)
          Right p -> pure p

      -- Base case: self = 0, both prev slots dummy (proof_must_verify
      -- false via is_base_case). Dummy statement input is irrelevant
      -- (the `1 + prev1 + prev2 = self` check is bypassed).
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
