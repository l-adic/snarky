-- | PureScript-side analog of OCaml's
-- | `dump_two_phase_chain.ml` — minimal multi-branch fixture, two
-- | rules sharing one wrap VK. **Currently `pending`**: the
-- | underlying `Pickles.Prove.CompileMulti.compileMulti` is a Phase
-- | 2a stub that throws `notImplemented`. This file's purpose at
-- | Phase 2b.1 is to commit the **value-level carrier shape** for the
-- | `RulesSpec`-encoded rules list, so when we fill in
-- | `compileMulti`'s body we have a concrete call site to validate
-- | against `dump_two_phase_chain.exe`'s witness.
-- |
-- | Once Phase 2b lands a working `compileMulti`, switch the
-- | `pending` markers to `it` and iterate via
-- | `tools/two_phase_chain_witness_diff.sh`.
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

import Control.Monad.Trans.Class (lift) as MT
import Data.Tuple (Tuple(..))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Pickles.Prove.Step (StepRule)
import Pickles.Step.Advice (getPrevAppStates)
import Pickles.Types (StatementIO(..), StepField)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F, FVar, assertEqual_, const_, exists, true_)
import Test.Spec (SpecT, describe, pending)

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
       (F StepField) (FVar StepField)
       Unit Unit
       (F StepField) (FVar StepField)
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
       (Tuple (StatementIO (F StepField) Unit) Unit)
       (F StepField) (FVar StepField)
       Unit Unit
       (F StepField) (FVar StepField)
incrementRule self = do
  prev <- exists $ MT.lift do
    Tuple stmt _ <- getPrevAppStates unit
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
-- Phase 2b.1 NOTE: storing the rules in a Tuple-shaped value-level
-- carrier doesn't work directly. PS rejects record fields holding
-- the existing `StepRule`'s rank-2 forall (`forall t m'. … =>
-- input -> Snarky …`) — the same wall PR #126 hit when trying to
-- newtype-wrap StepRule's inner forall. Putting `{ rule:
-- makeZeroRule, … }` in a record doesn't typecheck because PS can't
-- unify the rank-2 stored shape with the eventual call-site shape.
--
-- So the rules carrier shape is deferred to Phase 2b.2 alongside
-- the implementation. The likely answer: a typeclass-based carrier
-- (`class RulesCarrier (rs :: RulesSpec) m | rs -> m where …`) where
-- per-rule data lives inside instance methods rather than in a
-- shared-record value. Each instance is monomorphic (no forall in
-- storage) so PS handles it fine.
--
-- For now, the rule bodies above are committed as the source of
-- truth for what the bodies LOOK LIKE. Phase 2b.2 wires them up.
--------------------------------------------------------------------------------
-- Test spec — pending until Phase 2b lands compileMulti's body
--------------------------------------------------------------------------------

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.TwoPhaseChain" do
  -- Phase 2b.2: implement compileMulti's body, then switch to `it`
  -- and use `tools/two_phase_chain_witness_diff.sh` to validate
  -- byte-identical OCaml ↔ PS witnesses (counter 0 = b0_step).
  pending "b0 (make_zero) — compile + prover.step + witness dump (Phase 2b.2)"
  -- Phase 2b.3+:
  pending "b0 (make_zero) wrap proof — verify under shared wrap VK"
  pending "b1 (increment, prev = b0 from branch 0) — multi-branch dispatch step"
  pending "b1 wrap"
  pending "b2 (increment, prev = b1 from branch 1) — same-branch dispatch step"
  pending "b2 wrap"
