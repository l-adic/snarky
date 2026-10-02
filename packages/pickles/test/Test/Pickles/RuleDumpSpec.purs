module Test.Pickles.RuleDumpSpec (spec) where

import Prelude

import Colog (LoggerT, Message)
import Data.Either (Either(..))
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Pickles.Field (StepField)
import Pickles.Prove.RuleDump (encodeRuleDump, recordRule, ruleWitness)
import Pickles.Step.Slots (mkPrevValues)
import Pickles.Types (StatementIO(..))
import Simple.JSON (writeJSON)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Circuit.DSL (F(..))
import Snarky.Curves.Class (fromInt)
import Test.Pickles.Prove.TwoPhaseChain (IncrementPrevsSpec, incrementRule, makeZeroRule)
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
    writeJSON (encodeRuleDump d) `shouldEqual`
      """{"publicOutput":[],"prevs":[],"ops":[{"constraint":{"basic":{"equal":[{"var":0},{"const":"0"}]}}}],"inputSize":1}"""
  it "records incrementRule" \_ -> liftEffect do
    d <- recordRule @1 @() @(F StepField) @Unit incrementRule
    writeJSON (encodeRuleDump d) `shouldEqual`
      """{"publicOutput":[],"prevs":[{"statement":[{"var":1}],"mustVerify":{"const":"1"}}],"ops":[{"alloc":1},{"constraint":{"basic":{"equal":[{"var":0},{"add":[{"const":"1"},{"var":1}]}]}}}],"inputSize":1}"""
  it "witnesses incrementRule at self = 5 over prev = 4" \_ -> liftEffect do
    let
      prev = mkPrevValues @IncrementPrevsSpec
        (Tuple (StatementIO { input: F (fromInt 4 :: StepField), output: unit }) unit)
    w <- ruleWitness @(F StepField) noAdvice (pure prev) (F (fromInt 5)) incrementRule
    w `shouldEqual` Right { input: [ fromInt 5 ], values: [ fromInt 4 ] }
