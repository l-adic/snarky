module Test.Snarky.Test.Circuit.Factors (spec) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Array (cons)
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect.Aff (throwError)
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Circuit.Builder (CircuitBuilderState, emptyCircuitBuilderState, execCircuitBuilderT)
import Snarky.Circuit.CVar (CVar, EvaluationError(..))
import Snarky.Circuit.Constraint (R1CSCircuit(..), evalR1CSCircuit)
import Snarky.Circuit.DSL (class CircuitM, all_, const_, eq_, exists, mul_, not_, publicInputs, read, runAsProverT)
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
  c2 <- not_ <$> eq_ a (const_ one)
  c3 <- not_ <$> eq_ b (const_ one)
  let cs = c1 `cons` (c2 `cons` (c3 `cons` mempty))
  all_ cs

instance FactorM Fr Gen where
  factor f = do
    a <- arbitrary @Fr
    pure $ Tuple a (f / a)

mkCircuitSpec'
  :: forall f a avar bvar
   . PrimeField f
  => ConstrainedType f avar a
  => ConstrainedType f bvar Boolean
  => Proxy f
  -> Gen a
  -> (forall m. CircuitM f m Gen => m bvar)
  -> Gen Result
mkCircuitSpec' (_ :: Proxy f) gen circuit = do
  inputs <- gen
  { constraints, publicInputs } <-
    execCircuitBuilderT circuit (emptyCircuitBuilderState :: CircuitBuilderState f)
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

  it "factors Circuit is Valid" $ quickCheck $
    mkCircuitSpec' (Proxy @Fr) (arbitrary @(FieldElem Fr)) factorsCircuit