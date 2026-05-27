-- | PureScript-side analog of OCaml's `Simple_chain` test
-- | (`mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:128-205`).
-- |
-- | Runs the inductive rule (`prev + 1`) at `max_proofs_verified = N1`
-- | through five iterations (b0..b4) via the `Pickles.Prove.CompileMulti`
-- | API: a single 1-rule `compileMulti` call returns a `BranchProver`
-- | closure that gets invoked once per iteration with the previous
-- | proof threaded as `InductivePrev`. The full chain is then handed
-- | to `verify` for end-to-end Pickles verification (stage 1
-- | deferred-values expand, stage 2 IPA accumulator check, stage 3
-- | kimchi `batch_verify`).
module Test.Pickles.Prove.SimpleChain
  ( spec
  , simpleChainRule
  ) where

import Prelude

import Colog (LoggerT, Message, logInfo, withSpan)
import Control.Monad.Except (runExceptT)
import Control.Monad.Trans.Class (lift) as MT
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
import Pickles (BranchProver(..), Compiled, CompiledProof(..), PrevSlot(..), RulesCons, RulesNil, Slot, SlotWrapKey(..), Slots1, StatementIO(..), StepField, StepRule, compileMulti, getPrevAppStates, mkRuleEntry, toVerifiable, verifyBatch)
import Snarky.Backend.Kimchi.ProofCache (mkProofCache)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, assertAny_, const_, equals_, exists, not_)
import Snarky.Curves.Class (fromInt)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | Simple_chain inductive rule (verbatim from OCaml `dump_simple_chain.ml:62-82`).
-- |
-- | Asserts `self == prev + 1` OR `is_base_case (self == 0)`. Reads
-- | the prev's app-state value via `getPrevAppStates` (= OCaml's
-- | `Req.Prev_input` handler), so the same compiled rule serves
-- | every iteration: b0 supplies `BasePrev { dummyStatement }`,
-- | b_{k+1} supplies `InductivePrev compiledProof_b_k tag` whose
-- | `compiledProof.statement.input` is `b_k`'s self.
simpleChainRule
  :: StepRule 1
       (Tuple1 (StatementIO (F StepField) Unit))
       (F StepField)
       (FVar StepField)
       Unit
       Unit
       (F StepField)
       (FVar StepField)
simpleChainRule self = do
  prev <- exists $ MT.lift do
    stmt /\ _ <- getPrevAppStates unit
    let StatementIO { input } = stmt
    pure input
  isBaseCase <- equals_ (const_ zero) self
  let proofMustVerify = not_ isBaseCase
  selfCorrect <- equals_ (CVar.add_ (const_ one) prev) self
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevPublicInputs: prev :< Vector.nil
    , proofMustVerify: proofMustVerify :< Vector.nil
    , publicOutput: unit
    }

-- | Simple_chain's 1-rule carrier shape. A single self-recursive
-- | rule with mpv=1, one prev slot of width 1.
type SimpleChainRules =
  RulesCons 1
    (Tuple1 (StatementIO (F StepField) Unit))
    (Tuple1 (Slot Compiled 1 1 (StatementIO (F StepField) Unit)))
    (Tuple1 SlotWrapKey)
    RulesNil

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.SimpleChain" do
  it "5-iteration step+wrap chain (b0..b4) proves end-to-end" \{ pallasSrs, vestaSrs } -> do
    cache <- liftEffect $ lookupEnv "PICKLES_PROOF_CACHE_DIR" <#> map \dir -> mkProofCache (dir <> "/SimpleChain.json")

    -- Build the 1-tuple rules carrier for compileMulti. mpvMax = 1
    -- (one prev slot); since this is the only branch, nd = 1.
    -- outputSize = mpvMax*32 + 1 + mpvMax = 32 + 1 + 1 = 34.
    chainEntry <- liftEffect $ mkRuleEntry @1 @Unit @(F StepField) @1 @1 simpleChainRule (tuple1 Self)

    let rules = tuple1 chainEntry

    logInfo "[SimpleChain] compiling…"
    output <- withSpan "[SimpleChain] compile" $ liftEffect $ compileMulti
      @SimpleChainRules
      @Unit
      @(F StepField)
      @(Slots1 1)
      @1
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      , proofCache: cache
      }
      rules

    let BranchProver chainProver = fst output.provers

    let
      runStep
        :: PrevSlot (F StepField) 1 (StatementIO (F StepField) Unit)
        -> F StepField
        -> Aff (CompiledProof 1 (StatementIO (F StepField) Unit))
      runStep prevSlot appInput = do
        eRes <- liftEffect $ runExceptT $ chainProver
          { appInput, prevs: tuple1 prevSlot, sideloadedVKs: tuple1 unit }
        case eRes of
          Left e -> liftEffect $ Exc.throw ("chainProver: " <> show e)
          Right p -> pure p

      basePrev = BasePrev
        { dummyStatement: StatementIO { input: F (negate one), output: unit } }

    logInfo "[SimpleChain] proving [step0, wrap0]"
    b0 <- withSpan "[SimpleChain] prove b0" $ liftAff $ runStep basePrev (F zero)
    logInfo "[SimpleChain] proving [step1, wrap1]"
    b1 <- withSpan "[SimpleChain] prove b1" $ liftAff $ runStep (InductivePrev b0 output.tag) (F one)
    logInfo "[SimpleChain] proving [step2, wrap2]"
    b2 <- withSpan "[SimpleChain] prove b2" $ liftAff $ runStep (InductivePrev b1 output.tag) (F (fromInt 2 :: StepField))
    logInfo "[SimpleChain] proving [step3, wrap3]"
    b3 <- withSpan "[SimpleChain] prove b3" $ liftAff $ runStep (InductivePrev b2 output.tag) (F (fromInt 3 :: StepField))
    logInfo "[SimpleChain] proving [step4, wrap4]"
    b4 <- withSpan "[SimpleChain] prove b4" $ liftAff $ runStep (InductivePrev b3 output.tag) (F (fromInt 4 :: StepField))

    logInfo "[SimpleChain] verifying 5-proof chain…"
    verifyBatch output.verifier (map toVerifiable [ b0, b1, b2, b3, b4 ]) `shouldEqual` true
    logInfo "[SimpleChain] verification complete"

    -- Each iteration's app-state input must equal the value we
    -- supplied as `appInput` to the prover. The rule asserts
    -- `self == prev + 1` (or `self == 0` for base), so the chain's
    -- carried inputs are the natural numbers 0..4.
    let
      stmtInputOf (CompiledProof p) =
        let StatementIO s = p.statement in s.input
    map stmtInputOf [ b0, b1, b2, b3, b4 ] `shouldEqual`
      [ F zero, F one, F (fromInt 2), F (fromInt 3), F (fromInt 4) ]
