module Test.Snarky.Test.Circuit.Factors (spec) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (throwError)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Circuit.Builder (CircuitBuilderState, emptyCircuitBuilderState, execCircuitBuilderT)
import Snarky.Circuit.CVar (EvaluationError(..), const_)
import Snarky.Circuit.Constraint (R1CS, R1CSCircuit(..), evalR1CSCircuit)
import Snarky.Circuit.DSL (class CircuitM, exists, publicInputs, read, runAsProverT)
import Snarky.Circuit.DSL.Assert (assert)
import Snarky.Circuit.DSL.Boolean (all_)
import Snarky.Circuit.DSL.Field (eq_, mul_, neq_)
import Snarky.Circuit.Prover (assignPublicInputs, emptyProverState, runProverT)
import Snarky.Circuit.Types (class ConstrainedType, FieldElem(..), Variable)
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (Result, arbitrary, withHelp)
import Test.QuickCheck.Gen (Gen, suchThat)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck)
import Type.Proxy (Proxy(..))

type Fr = Vesta.ScalarField

type ConstraintSystem = R1CS Fr Variable

class Monad m <= FactorM f m where
  factor :: f -> m (Tuple f f)

factorsCircuit
  :: forall m n
   . FactorM Fr n
  => CircuitM Fr ConstraintSystem m n
  => m Unit
factorsCircuit = do
  n <- publicInputs @Fr (Proxy @(FieldElem Fr))
  Tuple a b <- exists do
    FieldElem nVal <- read n
    Tuple a b <- lift $ factor @Fr nVal
    pure $ Tuple (FieldElem a) (FieldElem b)
  c1 <- mul_ a b >>= eq_ n
  c2 <- neq_ a (const_ one)
  c3 <- neq_ b (const_ one)
  assert =<< all_ [ c1, c2, c3 ]

instance FactorM Fr Gen where
  factor n = do
    a <- arbitrary @Fr `suchThat` \a ->
      a /= one && a /= n
    let b = n / a
    pure $ Tuple a b

instance FactorM Fr Effect where
  factor _ = do
    throw "unhandled request: Factor"

mkCircuitSpec'
  :: forall a avar
   . ConstrainedType Fr avar a ConstraintSystem
  => Gen a
  -> { constraints :: Array (R1CS Fr Variable)
     , publicInputs :: Array Variable
     }
  -> (forall m. CircuitM Fr ConstraintSystem m Gen => m Unit)
  -> Gen Result
mkCircuitSpec' gen { constraints, publicInputs } circuit = do
  inputs <- gen
  Tuple _ (assignments :: Map Variable Fr) <- do
    let proverState = emptyProverState { publicInputs = publicInputs }
    res <- runProverT
      ( do
          assignPublicInputs inputs
          circuit
      )
      proverState
    case res of
      Tuple (Left e) _ -> unsafeCrashWith $ "Error in circuit: " <> show e
      Tuple (Right c) { assignments } -> pure $ Tuple c assignments
  let
    _lookup v = case Map.lookup v assignments of
      Nothing -> throwError $ MissingVariable v
      Just res -> pure res
  eres <- runAsProverT
    (evalR1CSCircuit _lookup (R1CSCircuit constraints))
    assignments
  pure $
    case eres of
      Right res -> withHelp res "Circuit constraints satisfied and evals correctly"
      Left e -> withHelp false ("Failed to parse circuit output: " <> show e)

spec :: Spec Unit
spec = describe "Factors Specs" do

  it "factors Circuit is Valid" $ do
    { constraints, publicInputs } <- liftEffect $
      execCircuitBuilderT factorsCircuit (emptyCircuitBuilderState :: CircuitBuilderState ConstraintSystem)
    quickCheck $
      mkCircuitSpec' (arbitrary @(FieldElem Fr)) { constraints, publicInputs } factorsCircuit