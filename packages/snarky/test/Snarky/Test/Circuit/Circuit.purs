module Snarky.Test.Circuit.Circuit where

import Prelude

import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff, throwError)
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Circuit.Builder (CircuitBuilderState, emptyCircuitBuilderState, runCircuitBuilderM)
import Snarky.Circuit.CVar (CVar, EvaluationError(..))
import Snarky.Circuit.Constraint (R1CSCircuit(..), evalR1CSCircuit)
import Snarky.Circuit.DSL (class CircuitM, mul_, publicInputs, read, runAsProver)
import Snarky.Circuit.Prover (assignPublicInputs, emptyProverState, runProverM)
import Snarky.Circuit.Types (class ConstrainedType, FieldElem(..), Variable)
import Snarky.Curves.BN254 as BN254
import Snarky.Curves.Types (class PrimeField)
import Test.QuickCheck (class Arbitrary, Result, withHelp)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck)
import Type.Proxy (Proxy(..))

type Fr = BN254.ScalarField

type PublicInputs =
  Tuple
    (FieldElem Fr)
    (FieldElem Fr)

mulCircuit
  :: forall m
  . CircuitM Fr m
  => m (CVar Fr Variable)
mulCircuit = do
  Tuple a b <- publicInputs @Fr (Proxy @PublicInputs)
  mul_ a b


mkCircuitSpec 
  :: forall f avar a bvar b.
     PrimeField f
  => ConstrainedType f avar a
  => ConstrainedType f bvar b
  => Arbitrary a
  => Eq b
  => Proxy f
  -> (forall m. CircuitM f m => m bvar)
  -> (a -> b)
  -> Aff Unit
mkCircuitSpec (_ :: Proxy f) circuit f = quickCheck $ \inputs ->
  let
    Tuple _ { constraints, publicInputs } = 
      runCircuitBuilderM circuit (emptyCircuitBuilderState :: CircuitBuilderState f)
    Tuple result assignments =
      let
        proverState = emptyProverState { publicInputs = publicInputs }
      in
        case runProverM (assignPublicInputs inputs *> circuit) proverState of
          Tuple (Left e) _ -> unsafeCrashWith $ "Error in circuit: " <> show e
          Tuple (Right c) { assignments } -> Tuple c assignments
    _lookup v = case Map.lookup v assignments of
      Nothing -> throwError $ MissingVariable v
      Just res -> pure res
    eres = runAsProver (do
      isSatisfied <- evalR1CSCircuit _lookup (R1CSCircuit constraints)
      isProd <- read result >>= \cVal -> pure $ f inputs == cVal
      pure $ withHelp (isSatisfied && isProd) "Cicuit is sound and complete"
    ) assignments
  in
    case eres of
      Right res -> res :: Result
      Left _ -> unsafeCrashWith "oops"


spec :: Spec Unit
spec = describe "Circuit Specs" do
  it "Multiplication Circuit is Valid" $
    mkCircuitSpec (Proxy @Fr) mulCircuit \(Tuple (FieldElem a) (FieldElem b)) -> 
      FieldElem @Fr (a * b)