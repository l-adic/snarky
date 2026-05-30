-- | Architecture validation for the pickled transaction app: the base
-- | rule (which wraps `processTransaction` and therefore carries
-- | `AccountMapM`/`MerkleRequestM`/`TransactionM` constraints) registers
-- | as a pickles rule at the concrete app monad `TransferRefM`. That this
-- | type-checks is the whole point of the StepProverT deletion: app
-- | advice resolves on the bare app monad, no orphan, no `mkRuleEntryM`.
-- |
-- | TODO: the full single application program — both branches under one
-- | `compileMulti` (base mpv=0 + merge mpv=2 Self), then prove a base
-- | transaction and a merge of two base proofs, and `verifyBatch`. Wiring
-- | mirrors TwoPhaseChain (2-branch compileMulti) × TreeProofReturn
-- | (mpv=2 Self-recursive prover with BasePrev/InductivePrev).
module Test.Snarky.Example.TransactionSnark
  ( spec
  ) where

import Prelude

import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Pickles (RuleEntry, mkRuleEntry)
import Snarky.Circuit.DSL (F)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.TransactionSnark (Stmt, baseRule)
import Test.Snarky.Example.Monad (TransferRefM)
import Test.Spec (SpecT, describe, it)

type SF = Vesta.ScalarField

-- | Tree depth used for this validation.
type D = 4

spec :: SpecT Aff Unit Aff Unit
spec =
  describe "Snarky.Example.TransactionSnark" do
    it "base rule registers as a pickles rule at the bare app monad TransferRefM" do
      -- The mere fact that this elaborates proves app advice
      -- (AccountMapM/MerkleRequestM/TransactionM) discharges on the bare
      -- app monad — no StepProverT, no orphan, no mkRuleEntryM.
      -- `prevsSpec = Unit` (mpv=0, no prev slots) is pinned via the
      -- RuleEntry annotation so `BuildSlotVkSources` resolves.
      _entry :: RuleEntry Unit 0 1 1 Unit (Stmt (F SF)) _ _ Unit _ _ (TransferRefM D SF) <-
        liftEffect $ mkRuleEntry
          @0
          @Unit
          @(Stmt (F SF))
          @1
          @1
          @(TransferRefM D SF)
          (baseRule @D)
          unit
      pure unit
