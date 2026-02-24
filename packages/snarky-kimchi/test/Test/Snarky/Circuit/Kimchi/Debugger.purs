module Test.Snarky.Circuit.Kimchi.Debugger
  ( spec
  ) where

import Prelude

import Data.Either (Either(..), isRight)
import Data.Identity (Identity)
import Data.String as String
import Data.Tuple (Tuple(..), uncurry)
import Snarky.Circuit.CVar (EvaluationError(..))
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, addConstraint, const_, div_, label, mul_, r1cs)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pallas as Pallas
import Test.Snarky.Circuit.Debugger (debugCircuitPure)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual, shouldSatisfy)
import Type.Proxy (Proxy(..))

type F' = F Pallas.BaseField
type FV = FVar Pallas.BaseField
type KC = KimchiConstraint Pallas.BaseField

spec :: Spec Unit
spec = describe "CircuitDebuggerT" do

  it "succeeds on a correct mul circuit" do
    let
      circuit :: forall t. CircuitM Pallas.BaseField KC t Identity => FV -> FV -> Snarky KC t Identity FV
      circuit a b = mul_ a b

      result :: Either EvaluationError F'
      result = debugCircuitPure (Proxy @KC) (uncurry circuit) (Tuple (F one) (F one))
    result `shouldSatisfy` isRight

  it "catches R1CS constraint violation" do
    let
      -- Circuit that adds a deliberately wrong constraint:
      -- asserts input * input = 0 (only true when input = 0)
      badCircuit :: forall t. CircuitM Pallas.BaseField KC t Identity => FV -> Snarky KC t Identity FV
      badCircuit input = do
        res <- mul_ input input
        addConstraint $ r1cs { left: input, right: input, output: const_ zero }
        pure res

      result :: Either EvaluationError F'
      result = debugCircuitPure (Proxy @KC) badCircuit (F one)
    case result of
      Left (FailedAssertion msg) ->
        msg `shouldSatisfy` String.contains (String.Pattern "R1CS")
      Left e ->
        fail $ "Expected FailedAssertion but got: " <> show e
      Right _ ->
        fail "Expected constraint failure but circuit succeeded"

  it "catches DivisionByZero" do
    let
      -- Division by a variable-valued zero (not const_ zero, which throws unsafely)
      circuit :: forall t. CircuitM Pallas.BaseField KC t Identity => FV -> FV -> Snarky KC t Identity FV
      circuit a b = div_ a b

      result :: Either EvaluationError F'
      result = debugCircuitPure (Proxy @KC) (uncurry circuit) (Tuple (F one) (F zero))
    case result of
      Left (DivisionByZero _) -> pure unit
      Left e ->
        fail $ "Expected DivisionByZero but got: " <> show e
      Right _ ->
        fail "Expected DivisionByZero but circuit succeeded"

  it "constraint satisfied when input is zero" do
    let
      -- Same deliberately wrong constraint, but with input = 0 it IS satisfied (0*0=0)
      badCircuit :: forall t. CircuitM Pallas.BaseField KC t Identity => FV -> Snarky KC t Identity FV
      badCircuit input = do
        res <- mul_ input input
        addConstraint $ r1cs { left: input, right: input, output: const_ zero }
        pure res

      result :: Either EvaluationError F'
      result = debugCircuitPure (Proxy @KC) badCircuit (F zero)
    result `shouldEqual` Right (F zero)

  it "label wraps errors with WithContext" do
    let
      circuit :: forall t. CircuitM Pallas.BaseField KC t Identity => FV -> Snarky KC t Identity FV
      circuit input = label "my-label" do
        res <- mul_ input input
        addConstraint $ r1cs { left: input, right: input, output: const_ zero }
        pure res

      result :: Either EvaluationError F'
      result = debugCircuitPure (Proxy @KC) circuit (F one)
    case result of
      Left (WithContext ctx (FailedAssertion _)) ->
        ctx `shouldEqual` "my-label"
      Left e ->
        fail $ "Expected WithContext but got: " <> show e
      Right _ ->
        fail "Expected labeled error but circuit succeeded"

  it "labels nest correctly" do
    let
      circuit :: forall t. CircuitM Pallas.BaseField KC t Identity => FV -> Snarky KC t Identity FV
      circuit input = label "outer" $ label "inner" do
        res <- mul_ input input
        addConstraint $ r1cs { left: input, right: input, output: const_ zero }
        pure res

      result :: Either EvaluationError F'
      result = debugCircuitPure (Proxy @KC) circuit (F one)
    case result of
      Left (WithContext "outer" (WithContext "inner" (FailedAssertion _))) ->
        pure unit
      Left e ->
        fail $ "Expected nested WithContext but got: " <> show e
      Right _ ->
        fail "Expected labeled error but circuit succeeded"
