module Test.Pickles.RuleDumpSpec (spec) where

import Prelude

import Colog (LoggerT, Message)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Pickles.Field (StepField)
import Pickles.Prove.RuleDump (recordRule, writeRuleDump)
import Simple.JSON (writeJSON)
import Snarky.Circuit.DSL (F)
import Test.Pickles.Prove.TwoPhaseChain (incrementRule, makeZeroRule)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | The recording interpreter on TwoPhaseChain's two rules, whose
-- | bodies are small enough to write out: `makeZeroRule` asserts its
-- | input is zero; `incrementRule` allocates `prev`, asserts
-- | `self = 1 + prev`, and returns `prev` in its one slot, which must
-- | verify.
spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.RuleDump" do
  it "records makeZeroRule" \_ -> liftEffect do
    d <- recordRule @0 @() @(F StepField) @Unit makeZeroRule
    writeJSON (writeRuleDump d) `shouldEqual`
      """{"publicOutput":[],"prevs":[],"ops":[{"constraint":{"basic":{"equal":[{"var":0},{"const":"0"}]}}}],"inputSize":1}"""
  it "records incrementRule" \_ -> liftEffect do
    d <- recordRule @1 @() @(F StepField) @Unit incrementRule
    writeJSON (writeRuleDump d) `shouldEqual`
      """{"publicOutput":[],"prevs":[{"statement":[{"var":1}],"mustVerify":{"const":"1"}}],"ops":[{"alloc":1},{"constraint":{"basic":{"equal":[{"var":0},{"add":[{"const":"1"},{"var":1}]}]}}}],"inputSize":1}"""
