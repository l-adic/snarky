module Test.Snarky.Circuit.Kimchi.Debugger
  ( spec
  ) where

import Prelude

import Data.Either (Either(..), isRight)
import Data.Identity (Identity)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Tuple (Tuple(..), uncurry)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.CVar (EvaluationError(..), incrementVariable, v0)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, addConstraint, const_, div_, label, mul_, r1cs)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate, initialState)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Pallas as Pallas
import Test.Snarky.Circuit.Debugger (debugCircuitPure)
import Test.Snarky.Circuit.Utils (decorateError)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual, shouldSatisfy)
import Type.Proxy (Proxy(..))

type F' = F Pallas.BaseField
type FV = FVar Pallas.BaseField
type KC = KimchiConstraint Pallas.BaseField
type KG = KimchiGate Pallas.BaseField
type AS = AuxState Pallas.BaseField

spec :: Spec Unit
spec = describe "ProverT debug mode" do

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

  describe "variable birth metadata" do
    let
      -- v0=0, v1=1, v2=2, v3=3
      v1 = incrementVariable v0
      v2 = incrementVariable v1
      v3 = incrementVariable v2

    it "varMetadata tracks which label block allocated each variable" do
      let
        -- A circuit with two labeled sections, each allocating an intermediate variable
        circuit :: forall t. CircuitM Pallas.BaseField KC t Identity => FV -> Snarky KC t Identity FV
        circuit input = do
          x <- label "squaring" $ mul_ input input
          y <- label "cubing" $ mul_ x input
          pure y

        builtState :: CircuitBuilderState KG AS
        builtState = compilePure (Proxy @F') (Proxy @F') (Proxy @KC) circuit initialState

      -- Variables 0,1 are public I/O (allocated by compile, no label context)
      Map.lookup v0 builtState.varMetadata `shouldEqual` Just []
      Map.lookup v1 builtState.varMetadata `shouldEqual` Just []
      -- Variable 2 is the intermediate from mul_ inside "squaring"
      Map.lookup v2 builtState.varMetadata `shouldEqual` Just [ "squaring" ]
      -- Variable 3 is the intermediate from mul_ inside "cubing"
      Map.lookup v3 builtState.varMetadata `shouldEqual` Just [ "cubing" ]

    it "nested labels produce nested birth context paths" do
      let
        circuit :: forall t. CircuitM Pallas.BaseField KC t Identity => FV -> Snarky KC t Identity FV
        circuit input = label "outer" do
          x <- label "square" $ mul_ input input
          label "cube" $ mul_ x input

        builtState :: CircuitBuilderState KG AS
        builtState = compilePure (Proxy @F') (Proxy @F') (Proxy @KC) circuit initialState

      -- Variable 2: allocated inside "outer" > "square"
      Map.lookup v2 builtState.varMetadata `shouldEqual` Just [ "outer", "square" ]
      -- Variable 3: allocated inside "outer" > "cube"
      Map.lookup v3 builtState.varMetadata `shouldEqual` Just [ "outer", "cube" ]

    it "decorateError enriches MissingVariable with birth context" do
      let
        circuit :: forall t. CircuitM Pallas.BaseField KC t Identity => FV -> Snarky KC t Identity FV
        circuit input = label "scalar-mul" do
          x <- mul_ input input
          mul_ x input

        builtState :: CircuitBuilderState KG AS
        builtState = compilePure (Proxy @F') (Proxy @F') (Proxy @KC) circuit initialState

        -- Simulate a MissingVariable error for variable 2 (inside "scalar-mul")
        err = MissingVariable v2
        decorated = decorateError builtState err

      -- Without metadata: "MissingVariable 2"
      -- With metadata: "MissingVariable 2 (scalar-mul)"
      decorated `shouldSatisfy` String.contains (String.Pattern "(scalar-mul)")
      decorated `shouldSatisfy` String.contains (String.Pattern "MissingVariable 2")
