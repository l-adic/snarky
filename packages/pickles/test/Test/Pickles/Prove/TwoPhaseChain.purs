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
import Data.Tuple.Nested (Tuple1, Tuple2, tuple1, tuple2, (/\))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception as Exc
import Pickles.Prove.Compile
  ( BranchProver(..)
  , PrevSlot(..)
  , RuleEntry
  , RulesCons
  , RulesNil
  , SlotWrapKey(..)
  , compileMulti
  , mkRuleEntry
  )
import Pickles.Prove.Step (StepRule)
import Pickles.Prove.Verify (verify)
import Pickles.Step.Advice (getPrevAppStates)
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil, StepSlot)
import Pickles.Types (StatementIO(..), StepField, StepIPARounds, WrapIPARounds)
import Pickles.Wrap.Slots (NoSlots)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, assertEqual_, const_, exists, true_)
import Snarky.Curves.Class (fromInt) as Curves
import Snarky.Types.Shifted (SplitField, Type2)
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

-- | `makeZeroRule` packaged: mpv=0, no prevs, valCarrier=Unit.
mkMakeZeroEntry
  :: Effect (RuleEntry PrevsSpecNil 0 2 Unit (F StepField) Unit 34 Unit)
mkMakeZeroEntry =
  mkRuleEntry
    @PrevsSpecNil
    @0 -- mpv (rule's own)
    @1 -- mpvMax (TwoPhaseChain wrap circuit's mpvMax)
    @1 -- mpvPad = mpvMax - mpv = 1
    @2 -- nd = topBranches (TwoPhaseChain has 2 branches: makeZero, increment)
    @34 -- outputSize = mpvMax*32 + 1 + mpvMax = 1*32+1+1
    @Unit
    @(F StepField)
    @(FVar StepField)
    @Unit
    @Unit
    @(F StepField)
    @(FVar StepField)
    @Unit
    makeZeroRule
    unit

-- | `incrementRule` packaged: mpv=1, one self-referential prev,
-- | valCarrier carrying the prev's `StatementIO`.
mkIncrementEntry
  :: Effect
       ( RuleEntry
           (PrevsSpecCons 1 (StatementIO (F StepField) Unit) PrevsSpecNil)
           1
           2
           (Tuple1 (StatementIO (F StepField) Unit))
           (F StepField)
           ( Tuple1
               ( StepSlot 1 StepIPARounds WrapIPARounds (F StepField)
                   (Type2 (SplitField (F StepField) Boolean))
                   Boolean
               )
           )
           34
           (Tuple1 SlotWrapKey)
       )
mkIncrementEntry =
  mkRuleEntry
    @(PrevsSpecCons 1 (StatementIO (F StepField) Unit) PrevsSpecNil)
    @1 -- mpv
    @1 -- mpvMax (= mpv, identity)
    @0 -- mpvPad = 0
    @2 -- nd = topBranches (TwoPhaseChain has 2 branches)
    @34
    @(Tuple1 (StatementIO (F StepField) Unit))
    @(F StepField)
    @(FVar StepField)
    @Unit
    @Unit
    @(F StepField)
    @(FVar StepField)
    @(Tuple1 SlotWrapKey)
    incrementRule
    (tuple1 Self)

-- | The full rules carrier `compileMulti` receives — a Tuple chain
-- | of `RuleEntry`s (one per branch, heterogeneously typed).
mkRulesCarrier
  :: Effect
       ( Tuple2
           (RuleEntry PrevsSpecNil 0 2 Unit (F StepField) Unit 34 Unit)
           ( RuleEntry
               (PrevsSpecCons 1 (StatementIO (F StepField) Unit) PrevsSpecNil)
               1
               2
               (Tuple1 (StatementIO (F StepField) Unit))
               (F StepField)
               ( Tuple1
                   ( StepSlot 1 StepIPARounds WrapIPARounds (F StepField)
                       (Type2 (SplitField (F StepField) Boolean))
                       Boolean
                   )
               )
               34
               (Tuple1 SlotWrapKey)
           )
       )
mkRulesCarrier = do
  zero <- mkMakeZeroEntry
  inc <- mkIncrementEntry
  pure (tuple2 zero inc)

-- | Two-branch `RulesSpec`:
-- |
-- |   * branch 0: makeZero (mpv=0, no prevs)
-- |   * branch 1: increment (mpv=1, one self-prev)
type TwoPhaseChainRules =
  RulesCons 0 Unit PrevsSpecNil Unit
    ( RulesCons 1
        (Tuple1 (StatementIO (F StepField) Unit))
        (PrevsSpecCons 1 (StatementIO (F StepField) Unit) PrevsSpecNil)
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

    rules <- liftEffect mkRulesCarrier
    output <- liftEffect $ compileMulti
      @TwoPhaseChainRules
      @(F StepField)
      @Unit
      @(F StepField)
      @1
      @(Product (Vector 1) NoSlots)
      cfg
      rules

    let
      BranchProver makeZeroProver = fst output.provers
      BranchProver incrementProver = fst (snd output.provers)
    eRes <- liftEffect $ runExceptT $ makeZeroProver
      { appInput: F zero, prevs: unit }
    b0 <- case eRes of
      Left e -> liftEffect $ Exc.throw ("makeZeroProver: " <> show e)
      Right p -> pure p

    -- b1 = increment(b0); appInput = 0 + 1 = 1. Prev is b0 (branch 0).
    eB1 <- liftEffect $ runExceptT $ incrementProver
      { appInput: F one
      , prevs: tuple1 (InductivePrev b0 output.tag)
      }
    b1 <- case eB1 of
      Left e -> liftEffect $ Exc.throw ("incrementProver: " <> show e)
      Right p -> pure p
    -- b2 = increment(b1); appInput = 1 + 1 = 2. Same-branch self-prev.
    eB2 <- liftEffect $ runExceptT $ incrementProver
      { appInput: F (Curves.fromInt 2 :: StepField)
      , prevs: tuple1 (InductivePrev b1 output.tag)
      }
    b2 <- case eB2 of
      Left e -> liftEffect $ Exc.throw ("incrementProver b2: " <> show e)
      Right p -> pure p
    -- b3 = increment(b2); appInput = 2 + 1 = 3.
    eB3 <- liftEffect $ runExceptT $ incrementProver
      { appInput: F (Curves.fromInt 3 :: StepField)
      , prevs: tuple1 (InductivePrev b2 output.tag)
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
