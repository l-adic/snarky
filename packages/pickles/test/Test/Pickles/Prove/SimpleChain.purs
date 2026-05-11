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
import Pickles (BranchProver(..), Compiled, CompiledProof(..), compileMulti, getPrevAppStates, mkRuleEntry, PrevSlot(..), RulesCons, RulesNil, Slot, Slots1, SlotWrapKey(..), StatementIO(..), StepField, StepRule, verify)

import Control.Monad.Except (runExceptT)
import Control.Monad.Trans.Class (lift) as MT
import Data.Either (Either(..))
import Data.Int.Bits as Int
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (Tuple1, tuple1, (/\))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, assertAny_, const_, equals_, exists, not_)
import Snarky.Curves.Class (fromInt)
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
    (Tuple1 (Slot Compiled 1 (StatementIO (F StepField) Unit)))
    (Tuple1 SlotWrapKey)
    RulesNil

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.SimpleChain" do
  it "5-iteration step+wrap chain (b0..b4) proves end-to-end" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField

    -- Build the 1-tuple rules carrier for compileMulti. mpvMax = 1
    -- (one prev slot); since this is the only branch, nd = 1.
    -- outputSize = mpvMax*32 + 1 + mpvMax = 32 + 1 + 1 = 34.
    chainEntry <- liftEffect $ mkRuleEntry @1 @Unit @(F StepField) simpleChainRule (tuple1 Self)

    let rules = tuple1 chainEntry

    output <- liftEffect $ compileMulti
      @SimpleChainRules
      @Unit
      @(F StepField)
      @(Slots1 1)
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      }
      rules

    let BranchProver chainProver = fst output.provers

    let
      runStep
        :: PrevSlot (F StepField) 1 (StatementIO (F StepField) Unit) Unit
        -> F StepField
        -> Aff (CompiledProof 1 (StatementIO (F StepField) Unit) Unit Unit)
      runStep prevSlot appInput = do
        eRes <- liftEffect $ runExceptT $ chainProver
          { appInput, prevs: tuple1 prevSlot, sideloadedVKs: tuple1 unit }
        case eRes of
          Left e -> liftEffect $ Exc.throw ("chainProver: " <> show e)
          Right p -> pure p

      basePrev = BasePrev
        { dummyStatement: StatementIO { input: F (negate one), output: unit } }

    b0 <- runStep basePrev (F zero)
    b1 <- runStep (InductivePrev b0 output.tag) (F one)
    b2 <- runStep (InductivePrev b1 output.tag) (F (fromInt 2 :: StepField))
    b3 <- runStep (InductivePrev b2 output.tag) (F (fromInt 3 :: StepField))
    b4 <- runStep (InductivePrev b3 output.tag) (F (fromInt 4 :: StepField))

    verify output.verifier [ b0, b1, b2, b3, b4 ] `shouldEqual` true

    -- Each iteration's app-state input must equal the value we
    -- supplied as `appInput` to the prover. The rule asserts
    -- `self == prev + 1` (or `self == 0` for base), so the chain's
    -- carried inputs are the natural numbers 0..4.
    let
      stmtInputOf (CompiledProof p) =
        let StatementIO s = p.statement in s.input
    map stmtInputOf [ b0, b1, b2, b3, b4 ] `shouldEqual`
      [ F zero, F one, F (fromInt 2), F (fromInt 3), F (fromInt 4) ]
