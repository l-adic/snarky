module Test.Pickles.RuleDumpSpec (spec) where

import Prelude

import Colog (LoggerT, Message)
import Data.Either (Either(..))
import Data.List (List(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Pickles (StepRule, toPrevs)
import Pickles.Field (StepField)
import Pickles.Prove.RuleDump (RuleDumpJson(..), recordRule)
import Pickles.RuleWitness (RuleWitness, captureAllocations, ruleWitness)
import Pickles.Step.Main (RuleOutput, runRuleWithInput)
import Pickles.Step.Slots (PrevValues, mkPrevValues)
import Pickles.Types (StatementIO(..))
import Simple.JSON (writeJSON)
import Snarky.Backend.Advice (AdviceHandler, noAdvice)
import Snarky.Backend.Compile (SolverT, makeSolver')
import Snarky.Circuit.CVar (CVar(..), EvaluationError(..))
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (class CircuitType, AsProver, BoolVar, F(..), FVar, Snarky, assertEqual_, const_, exists, fieldsToValue, fieldsToVar, read, sizeInFields, valueToFields, varToFields)
import Snarky.Circuit.DSL.Monad (class CheckedType, assignVars, fresh)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (fromInt)
import Test.Pickles.Prove.TwoPhaseChain (IncrementPrevsSpec, incrementRule, makeZeroRule)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy)
import Type.Proxy (Proxy(..))

newtype CheckedInput a = CheckedInput a

instance CircuitType f a var => CircuitType f (CheckedInput a) (CheckedInput var) where
  valueToFields (CheckedInput x) = valueToFields x
  fieldsToValue = CheckedInput <<< fieldsToValue
  sizeInFields pf _ = sizeInFields pf (Proxy @a)
  varToFields (CheckedInput x) = varToFields @f @a x
  fieldsToVar = CheckedInput <<< fieldsToVar @f @a

instance CheckedType StepField (KimchiConstraint StepField) (CheckedInput (FVar StepField)) where
  check (CheckedInput x) = do
    y <- exists $ read x <#> \(F a) -> F (a + one)
    assertEqual_ y (CVar.add_ x (const_ one))

booleanRule :: StepRule Unit Boolean (BoolVar StepField) Unit Unit
booleanRule _ _ = pure { prevs: toPrevs unit, publicOutput: unit }

allocatingRule
  :: StepRule Unit (CheckedInput (F StepField)) (CheckedInput (FVar StepField))
       (F StepField)
       (FVar StepField)
allocatingRule _ (CheckedInput x) = do
  y <- exists $ read x <#> \(F a) -> F (a + a)
  assertEqual_ y (CVar.add_ x x)
  pure { prevs: toPrevs unit, publicOutput: y }

unitInputRule :: StepRule Unit Unit Unit (F StepField) (FVar StepField)
unitInputRule _ _ = do
  y <- exists (pure (F (fromInt 7 :: StepField)))
  pure { prevs: toPrevs unit, publicOutput: y }

solveRule
  :: forall @inputVal r prevsSpec inputVar outputVar
   . CircuitType StepField inputVal inputVar
  => CheckedType StepField (KimchiConstraint StepField) inputVar
  => AdviceHandler r
  -> AsProver StepField r (PrevValues prevsSpec)
  -> inputVal
  -> ( AsProver StepField r (PrevValues prevsSpec)
       -> inputVar
       -> Snarky StepField (KimchiConstraint StepField) r (RuleOutput prevsSpec outputVar)
     )
  -> Effect (Either EvaluationError RuleWitness)
solveRule handler prevs input rule = do
  capture <- Ref.new Nil
  let
    solver :: SolverT StepField (KimchiConstraint StepField) r Unit Unit
    solver = makeSolver' { debug: true } (Proxy @(KimchiConstraint StepField)) \(_ :: Unit) -> do
      _ <- exists (pure (F (fromInt 99 :: StepField)))
      void $ captureAllocations (Just capture) $ runRuleWithInput @inputVal rule (pure input) prevs
      _ <- exists (pure (F (fromInt 100 :: StepField)))
      pure unit
  result <- solver handler unit
  vars <- Ref.read capture
  pure $ case result of
    Left err -> Left err
    Right (Tuple _ assignments) -> ruleWitness
      (sizeInFields (Proxy @StepField) (Proxy @inputVal))
      vars
      assignments

-- | Input checks precede rule operations in both recordings and witnesses.
spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.RuleDump" do
  it "records a Boolean input check even when the rule emits nothing" \_ -> liftEffect do
    d <- recordRule @0 @() @Boolean @Unit booleanRule
    writeJSON (RuleDumpJson d) `shouldEqual`
      """{"publicOutput":[],"prevs":[],"ops":[{"constraint":{"basic":{"boolean":{"var":0}}}}],"inputSize":1}"""
    w <- solveRule @Boolean noAdvice (pure (mkPrevValues @Unit unit)) true booleanRule
    w `shouldEqual` Right { input: [ one ], values: [] }

  it "numbers input-check allocations before rule allocations" \_ -> liftEffect do
    d <- recordRule @0 @() @(CheckedInput (F StepField)) @(F StepField) allocatingRule
    writeJSON (RuleDumpJson d) `shouldEqual`
      """{"publicOutput":[{"var":2}],"prevs":[],"ops":[{"alloc":1},{"constraint":{"basic":{"equal":[{"var":1},{"add":[{"var":0},{"const":"1"}]}]}}},{"alloc":1},{"constraint":{"basic":{"equal":[{"var":2},{"add":[{"var":0},{"var":0}]}]}}}],"inputSize":1}"""
    w <- solveRule @(CheckedInput (F StepField)) noAdvice (pure (mkPrevValues @Unit unit))
      (CheckedInput (F (fromInt 5)))
      allocatingRule
    w `shouldEqual` Right { input: [ fromInt 5 ], values: [ fromInt 6, fromInt 10 ] }

  it "keeps the first body allocation when the input has no fields" \_ -> liftEffect do
    d <- recordRule @0 @() @Unit @(F StepField) unitInputRule
    writeJSON (RuleDumpJson d) `shouldEqual`
      """{"publicOutput":[{"var":0}],"prevs":[],"ops":[{"alloc":1}],"inputSize":0}"""
    w <- solveRule @Unit noAdvice (pure (mkPrevValues @Unit unit)) unit unitInputRule
    w `shouldEqual` Right { input: [], values: [ fromInt 7 ] }

  it "records makeZeroRule" \_ -> liftEffect do
    d <- recordRule @0 @() @(F StepField) @Unit makeZeroRule
    writeJSON (RuleDumpJson d) `shouldEqual`
      """{"publicOutput":[],"prevs":[],"ops":[{"constraint":{"basic":{"equal":[{"var":0},{"const":"0"}]}}}],"inputSize":1}"""
  it "records incrementRule" \_ -> liftEffect do
    d <- recordRule @1 @() @(F StepField) @Unit incrementRule
    writeJSON (RuleDumpJson d) `shouldEqual`
      """{"publicOutput":[],"prevs":[{"statement":[{"var":1}],"mustVerify":{"const":"1"}}],"ops":[{"alloc":1},{"constraint":{"basic":{"equal":[{"var":0},{"add":[{"const":"1"},{"var":1}]}]}}}],"inputSize":1}"""
  it "witnesses incrementRule at self = 5 over prev = 4" \_ -> liftEffect do
    let
      prev = mkPrevValues @IncrementPrevsSpec
        (Tuple (StatementIO { input: F (fromInt 4 :: StepField), output: unit }) unit)
    w <- solveRule @(F StepField) noAdvice (pure prev) (F (fromInt 5)) incrementRule
    w `shouldEqual` Right { input: [ fromInt 5 ], values: [ fromInt 4 ] }

  it "captures stateful advice without executing it again" \_ -> liftEffect do
    calls <- Ref.new 0
    let
      rule :: StepRule Unit (CheckedInput (F StepField)) (CheckedInput (FVar StepField)) Unit Unit
      rule _ (CheckedInput x) = do
        y <- exists do
          n <- liftEffect $ Ref.modify (_ + 1) calls
          pure (F (fromInt n :: StepField))
        assertEqual_ y x
        pure { prevs: toPrevs unit, publicOutput: unit }
    w <- solveRule @(CheckedInput (F StepField)) noAdvice (pure (mkPrevValues @Unit unit))
      (CheckedInput (F one))
      rule
    w `shouldEqual` Right { input: [ one ], values: [ fromInt 2, one ] }
    Ref.read calls >>= (_ `shouldEqual` 1)

  it "captures fresh variables assigned later in the solve" \_ -> liftEffect do
    let
      rule :: StepRule Unit (F StepField) (FVar StepField) Unit Unit
      rule _ x = do
        v <- fresh
        assignVars [ v ] (read x <#> \(F a) -> [ a ])
        assertEqual_ (Var v) x
        pure { prevs: toPrevs unit, publicOutput: unit }
    w <- solveRule @(F StepField) noAdvice (pure (mkPrevValues @Unit unit)) (F one) rule
    w `shouldEqual` Right { input: [ one ], values: [ one ] }

  it "rejects an unassigned rule variable" \_ -> liftEffect do
    let
      rule :: StepRule Unit Unit Unit Unit Unit
      rule _ _ = do
        _ <- fresh
        pure { prevs: toPrevs unit, publicOutput: unit }
    w <- solveRule @Unit noAdvice (pure (mkPrevValues @Unit unit)) unit rule
    w `shouldSatisfy` case _ of
      Left (MissingVariable _) -> true
      _ -> false
