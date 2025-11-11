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
import Snarky.Circuit.CVar (CVar, EvaluationError(..))
import Snarky.Circuit.Constraint (R1CS, R1CSCircuit(..), evalR1CSCircuit)
import Snarky.Circuit.DSL (class CircuitM, all_, const_, eq_, exists, mul_, neq_, publicInputs, read, runAsProverT)
import Snarky.Circuit.Prover (assignPublicInputs, emptyProverState, runProverT)
import Snarky.Circuit.Types (class ConstrainedType, BooleanVariable, FieldElem(..), Variable)
import Snarky.Curves.Types (class PrimeField)
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (Result, arbitrary, withHelp)
import Test.QuickCheck.Gen (Gen)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck)
import Type.Proxy (Proxy(..))

type Fr = Vesta.ScalarField

class Monad m <= FactorM f m where
  factor :: f -> m (Tuple f f)

factorsCircuit
  :: forall m n
   . FactorM Fr n
  => CircuitM Fr m n
  => m (CVar Fr BooleanVariable)
factorsCircuit = do
  n <- publicInputs @Fr (Proxy @(FieldElem Fr))
  Tuple a b <- exists @Fr @m @n do
    FieldElem nVal <- read n
    Tuple a b <- lift $ factor @Fr nVal
    pure $ Tuple (FieldElem a) (FieldElem b)
  c1 <- mul_ a b >>= eq_ n
  c2 <- neq_ a (const_ one)
  c3 <- neq_ b (const_ one)
  all_ [ c1, c2, c3 ]

instance FactorM Fr Gen where
  factor f = do
    a <- arbitrary @Fr
    pure $ Tuple a (f / a)

instance FactorM Fr Effect where
  factor _ = do
    throw "unhandled request: Factor"

mkCircuitSpec'
  :: forall f a avar bvar
   . PrimeField f
  => ConstrainedType f avar a
  => ConstrainedType f bvar Boolean
  => Proxy f
  -> Gen a
  -> { constraints :: Array (R1CS f Variable)
     , publicInputs :: Array Variable
     }
  -> (forall m. CircuitM f m Gen => m bvar)
  -> Gen Result
mkCircuitSpec' (_ :: Proxy f) gen { constraints, publicInputs } circuit = do
  inputs <- gen
  Tuple _ (assignments :: Map Variable f) <- do
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
      execCircuitBuilderT factorsCircuit (emptyCircuitBuilderState :: CircuitBuilderState Fr)
    quickCheck $
      mkCircuitSpec' (Proxy @Fr) (arbitrary @(FieldElem Fr)) { constraints, publicInputs } factorsCircuit