module Test.Snarky.Circuit.Kimchi.Debugger
  ( spec
  ) where

import Prelude

import Data.Either (Either(..), isRight)
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Tuple (Tuple(..), fst, uncurry)
import Effect.Class (liftEffect)
import Effect.Unsafe (unsafePerformEffect)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Assignments as Assignments
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (compile', makeSolver')
import Snarky.Backend.Prover (class SolveCircuit)
import Snarky.Circuit.CVar (EvaluationError(..), incrementVariable, v0)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, F(..), FVar, Snarky, addConstraint, const_, div_, label, mul_, r1cs)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Pallas as Pallas
import Test.Snarky.Circuit.Utils (decorateError)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual, shouldSatisfy)
import Type.Proxy (Proxy(..))

type F' = F Pallas.BaseField
type FV = FVar Pallas.BaseField
type KC = KimchiConstraint Pallas.BaseField
type KG = KimchiGate Pallas.BaseField
type AS = AuxState Pallas.BaseField

debugCircuitPure
  :: forall f c a b avar bvar
   . SolveCircuit f c
  => CheckedType f c avar
  => CircuitType f a avar
  => CircuitType f b bvar
  => Proxy c
  -> (avar -> Snarky f c () bvar)
  -> a
  -> Either EvaluationError b
debugCircuitPure pc circuit inputs =
  unsafePerformEffect (makeSolver' { debug: true } pc circuit noAdvice inputs)
    <#> fst

spec :: Spec Unit
spec = describe "ProverT debug mode" do

  it "succeeds on a correct mul circuit" do
    let
      circuit :: FV -> FV -> Snarky Pallas.BaseField KC () FV
      circuit a b = mul_ a b

      result :: Either EvaluationError F'
      result = debugCircuitPure (Proxy @KC) (uncurry circuit) (Tuple (F one) (F one))
    result `shouldSatisfy` isRight

  it "catches R1CS constraint violation" do
    let
      -- Circuit that adds a deliberately wrong constraint:
      -- asserts input * input = 0 (only true when input = 0)
      badCircuit :: FV -> Snarky Pallas.BaseField KC () FV
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
      circuit :: FV -> FV -> Snarky Pallas.BaseField KC () FV
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
      badCircuit :: FV -> Snarky Pallas.BaseField KC () FV
      badCircuit input = do
        res <- mul_ input input
        addConstraint $ r1cs { left: input, right: input, output: const_ zero }
        pure res

      result :: Either EvaluationError F'
      result = debugCircuitPure (Proxy @KC) badCircuit (F zero)
    result `shouldEqual` Right (F zero)

  it "label wraps errors with WithContext" do
    let
      circuit :: FV -> Snarky Pallas.BaseField KC () FV
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
      circuit :: FV -> Snarky Pallas.BaseField KC () FV
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
        circuit :: FV -> Snarky Pallas.BaseField KC () FV
        circuit input = do
          x <- label "squaring" $ mul_ input input
          y <- label "cubing" $ mul_ x input
          pure y

        builtState :: CircuitBuilderState KG AS
        builtState = unsafePerformEffect $ compile' noAdvice { debug: true } (Proxy @F') (Proxy @F') (Proxy @KC) circuit

      -- Variables 0,1 are public I/O (allocated by compile, no label context)
      let meta0 = Assignments.lookup v0 builtState.varMetadata
      meta0 `shouldEqual` Just []
      let meta1 = Assignments.lookup v1 builtState.varMetadata
      meta1 `shouldEqual` Just []
      -- Variable 2 is the intermediate from mul_ inside "squaring"
      let metav2 = Assignments.lookup v2 builtState.varMetadata
      metav2 `shouldEqual` Just [ "squaring" ]
      -- Variable 3 is the intermediate from mul_ inside "cubing"
      let metav3 = Assignments.lookup v3 builtState.varMetadata
      metav3 `shouldEqual` Just [ "cubing" ]

    it "nested labels produce nested birth context paths" do
      let
        circuit :: FV -> Snarky Pallas.BaseField KC () FV
        circuit input = label "outer" do
          x <- label "square" $ mul_ input input
          label "cube" $ mul_ x input

        builtState :: CircuitBuilderState KG AS
        builtState = unsafePerformEffect $ compile' noAdvice { debug: true } (Proxy @F') (Proxy @F') (Proxy @KC) circuit

      -- Variable 2: allocated inside "outer" > "square"
      let mv2 = Assignments.lookup v2 builtState.varMetadata
      mv2 `shouldEqual` Just [ "outer", "square" ]
      -- Variable 3: allocated inside "outer" > "cube"
      let mv3 = Assignments.lookup v3 builtState.varMetadata
      mv3 `shouldEqual` Just [ "outer", "cube" ]

    it "decorateError enriches MissingVariable with birth context" do
      let
        circuit :: FV -> Snarky Pallas.BaseField KC () FV
        circuit input = label "scalar-mul" do
          x <- mul_ input input
          mul_ x input

        -- Simulate a MissingVariable error for variable 2 (inside "scalar-mul")
        err = MissingVariable v2
      builtState <- liftEffect $ compile' noAdvice { debug: true } (Proxy @F') (Proxy @F') (Proxy @KC) circuit
      metaLookup <- liftEffect $ Assignments.toLookup builtState.varMetadata
      let decorated = decorateError metaLookup err

      -- Without metadata: "MissingVariable 2"
      -- With metadata: "MissingVariable 2 (scalar-mul)"
      decorated `shouldSatisfy` String.contains (String.Pattern "(scalar-mul)")
      decorated `shouldSatisfy` String.contains (String.Pattern "MissingVariable 2")
