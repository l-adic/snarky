-- | PureScript-side analog of OCaml's `dump_two_phase_chain.ml` —
-- | minimal multi-branch fixture, two rules sharing one wrap VK.
-- |
-- | The two rules:
-- |
-- |   makeZeroRule  (branch 0):
-- |     prevs = []
-- |     body asserts self = 0
-- |
-- |   incrementRule (branch 1):
-- |     prevs = [self]   -- "self" = ANY branch of this proof system
-- |     body asserts self = prev + 1
-- |
-- | OCaml reference: `mina/src/lib/crypto/pickles/dump_two_phase_chain/dump_two_phase_chain.ml`.
module Test.Pickles.Prove.TwoPhaseChain
  ( spec
  , makeZeroRule
  , incrementRule
  ) where

import Prelude

import Control.Monad.Except (runExceptT)
import Control.Monad.Trans.Class (lift) as MT
import Data.Either (Either(..))
import Data.Functor.Product (Product)
import Data.Int.Bits as Int
import Data.Maybe (Maybe(..))
import Data.Tuple (fst, snd)
import Data.Tuple.Nested (Tuple1, tuple1, tuple2, (/\))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception as Exc
import Pickles (BranchProver(..), Compiled, NoSlots, PrevSlot(..), RulesCons, RulesNil, Slot, SlotWrapKey(..), StatementIO(..), StepField, StepRule, compileMulti, getPrevAppStates, mkRuleEntry, verify)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, assertEqual_, const_, exists, true_)
import Snarky.Curves.Class (fromInt) as Curves
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

--------------------------------------------------------------------------------
-- Rule bodies
--
-- Mirror dump_two_phase_chain.ml's Inductive_rule.t bodies 1:1.
-- Both rules share inputVal = F StepField, outputVal = Unit (Input
-- mode), prevInputVal = F StepField (the proof-system's app-state).
--------------------------------------------------------------------------------

-- | Branch 0: assert public_input = 0. No prevs.
-- |
-- | Mirrors `dump_two_phase_chain.ml`'s `make_zero` rule.
makeZeroRule
  :: StepRule 0 Unit
       (F StepField)
       (FVar StepField)
       Unit
       Unit
       (F StepField)
       (FVar StepField)
makeZeroRule self = do
  assertEqual_ self (const_ zero)
  pure
    { prevPublicInputs: Vector.nil
    , proofMustVerify: Vector.nil
    , publicOutput: unit
    }

-- | Branch 1: read prev (any branch's proof's app-state), assert
-- | public_input = prev + 1.
-- |
-- | Mirrors `dump_two_phase_chain.ml`'s `increment` rule. The
-- | `prevs = [self]` slot resolves to either branch at proof time —
-- | THIS is the multi-branch dispatch this whole apparatus exists to
-- | exercise.
-- |
-- | `valCarrier = Tuple (StatementIO (F StepField) Unit) Unit`
-- | matches the prev shape: one prev slot whose statement is
-- | `StatementIO (F StepField) Unit` (= "an integer counter, no
-- | output").
incrementRule
  :: StepRule 1
       (Tuple1 (StatementIO (F StepField) Unit))
       (F StepField)
       (FVar StepField)
       Unit
       Unit
       (F StepField)
       (FVar StepField)
incrementRule self = do
  prev <- exists $ MT.lift do
    stmt /\ _ <- getPrevAppStates unit
    let StatementIO { input } = stmt
    pure input
  assertEqual_ self (CVar.add_ (const_ one) prev)
  pure
    { prevPublicInputs: prev :< Vector.nil
    -- proof_must_verify = true unconditionally for now. The OCaml
    -- fixture also unconditionally verifies; the dispatch happens at
    -- the wrap layer based on `whichBranch`, not at the rule-body
    -- level.
    , proofMustVerify: true_ :< Vector.nil
    , publicOutput: unit
    }

--------------------------------------------------------------------------------
-- Per-rule `RuleEntry` builders. The branch-0 (mpv=0, no prevs)
-- entry is `Unit`-shaped; branch 1 (mpv=1, one self-prev) carries
-- the increment rule's prev statement plus its self slotVK.
--------------------------------------------------------------------------------

-- | Two-branch `RulesSpec`:
-- |
-- |   * branch 0: makeZero (mpv=0, no prevs)
-- |   * branch 1: increment (mpv=1, one self-prev)
type TwoPhaseChainRules =
  RulesCons 0 Unit Unit Unit
    ( RulesCons 1
        (Tuple1 (StatementIO (F StepField) Unit))
        (Tuple1 (Slot Compiled 1 (StatementIO (F StepField) Unit)))
        (Tuple1 SlotWrapKey)
        RulesNil
    )

--------------------------------------------------------------------------------
-- Test spec
--------------------------------------------------------------------------------

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.TwoPhaseChain" do
  -- Multi-branch chain b0..b3 prove + verify under the shared wrap VK.
  --   * `compileMulti` end-to-end (multi-branch step+wrap compile)
  --   * b0 from branch 0 (make_zero), b1..b3 from branch 1 (increment),
  --     each chained as `InductivePrev`.
  --   * Single `verify` call discharges all four proofs against the
  --     shared verifier — relies on per-proof `stepDomainLog2` so each
  --     proof's deferred-values reconstruction uses its own branch's
  --     step domain (b0=9, b1..b3=14).
  it "b0..b3 chain prove + verify under shared wrap VK" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField

    let
      cfg =
        { srs: { vestaSrs, pallasSrs }
        , debug: false
        , wrapDomainOverride: Nothing
        }

    makeZeroEntry <- liftEffect $ mkRuleEntry @1 @Unit @(F StepField) makeZeroRule unit
    incrementEntry <- liftEffect $ mkRuleEntry @1 @Unit @(F StepField) incrementRule (tuple1 Self)
    let rules = tuple2 makeZeroEntry incrementEntry
    output <- liftEffect $ compileMulti
      @TwoPhaseChainRules
      @Unit
      @(F StepField)
      @(Product (Vector 1) NoSlots)
      cfg
      rules

    let
      BranchProver makeZeroProver = fst output.provers
      BranchProver incrementProver = fst (snd output.provers)
    -- Branch 0 (makeZero) has no prevs → spec-derived `vkCarrier =
    -- Unit`. Branch 1 (increment) has one compiled prev slot →
    -- `vkCarrier = Tuple1 Unit`.
    eRes <- liftEffect $ runExceptT $ makeZeroProver
      { appInput: F zero, prevs: unit, sideloadedVKs: unit }
    b0 <- case eRes of
      Left e -> liftEffect $ Exc.throw ("makeZeroProver: " <> show e)
      Right p -> pure p

    -- b1 = increment(b0); appInput = 0 + 1 = 1. Prev is b0 (branch 0).
    eB1 <- liftEffect $ runExceptT $ incrementProver
      { appInput: F one
      , prevs: tuple1 (InductivePrev b0 output.tag)
      , sideloadedVKs: tuple1 unit
      }
    b1 <- case eB1 of
      Left e -> liftEffect $ Exc.throw ("incrementProver: " <> show e)
      Right p -> pure p
    -- b2 = increment(b1); appInput = 1 + 1 = 2. Same-branch self-prev.
    eB2 <- liftEffect $ runExceptT $ incrementProver
      { appInput: F (Curves.fromInt 2 :: StepField)
      , prevs: tuple1 (InductivePrev b1 output.tag)
      , sideloadedVKs: tuple1 unit
      }
    b2 <- case eB2 of
      Left e -> liftEffect $ Exc.throw ("incrementProver b2: " <> show e)
      Right p -> pure p
    -- b3 = increment(b2); appInput = 2 + 1 = 3.
    eB3 <- liftEffect $ runExceptT $ incrementProver
      { appInput: F (Curves.fromInt 3 :: StepField)
      , prevs: tuple1 (InductivePrev b2 output.tag)
      , sideloadedVKs: tuple1 unit
      }
    b3 <- case eB3 of
      Left e -> liftEffect $ Exc.throw ("incrementProver b3: " <> show e)
      Right p -> pure p

    -- Verify all four proofs (b0 from branch 0, b1..b3 from branch 1)
    -- against the shared multi-branch verifier. Per-proof
    -- `stepDomainLog2` carried by `CompiledProof` lets each proof's
    -- deferred-values reconstruction pick the right branch's step
    -- domain.
    verify output.verifier [ b0, b1, b2, b3 ] `shouldEqual` true
