module Snarky.Circuit.TestUtils where

import Prelude

import Control.Monad.Except (Except, runExcept, throwError)
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Identity (Identity(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Unsafe (unsafePerformEffect)
import Snarky.Circuit.CVar (EvaluationError(..), Variable)
import Snarky.Circuit.Compile (Solver, SolverT, Checker, runSolverT)
import Snarky.Circuit.Types (class CircuitType)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (class Arbitrary, Result(..), arbitrary, quickCheck, withHelp)
import Test.QuickCheck.Gen (Gen)

data Expectation f a
  = Satisfied a
  | Unsatisfied
  | ProverError (EvaluationError f -> Boolean)

instance Show a => Show (Expectation f a) where
  show = case _ of
    Unsatisfied -> "Unsatisfiable"
    Satisfied a -> "Satisfied " <> show a
    ProverError _ -> "[ProverError]"

satisfied :: forall f a b. (a -> b) -> a -> Expectation f b
satisfied f a = Satisfied (f a)

satisfied_ :: forall f a. a -> Expectation f Unit
satisfied_ _ = Satisfied unit

unsatisfied :: forall f a b. a -> Expectation f b
unsatisfied _ = Unsatisfied

expectDivideByZero :: forall f. (forall a b. a -> Expectation f b)
expectDivideByZero _ = ProverError \e -> case e of
  DivisionByZero _ -> true
  _ -> false

makeCircuitSpec
  :: forall f c a avar m b
   . CircuitType f a avar
  => Monad m
  => Eq b
  => Show b
  => PrimeField f
  => { constraints :: Array c
     , solver :: SolverT f m a b
     , evalConstraint ::
         (Variable -> Except (EvaluationError f) f)
         -> c
         -> Except (EvaluationError f) Boolean
     , isValid :: a -> Expectation f b
     }
  -> a
  -> m Result
makeCircuitSpec { constraints, solver, evalConstraint, isValid } inputs = do
  runSolverT solver inputs <#> case _ of
    Left e ->
      case isValid inputs of
        ProverError f -> withHelp (f e) ("Prover exited with error " <> show e)
        _ -> withHelp false ("Encountered unexpected  error when proving circuit: " <> show e)
    Right (Tuple b assignments) ->
      let
        checker :: Array c -> Except (EvaluationError f) Boolean
        checker =
          let
            lookup v = case Map.lookup v assignments of
              Nothing -> throwError $ MissingVariable v
              Just res -> pure res
          in
            foldM (\acc c -> conj acc <$> evalConstraint lookup c) true
      in
        case runExcept $ checker constraints of
          Left e -> withHelp false ("Encountered unexpected error when checking circuit: " <> show e)
          Right isSatisfied -> case isValid inputs of
            Satisfied expected | isSatisfied == true ->
              withHelp (expected == b) ("Circuit disagrees with test function, cirvuit got " <> show b <> " expected " <> show expected <> " from test function")
            Unsatisfied | isSatisfied == false -> Success
            res -> withHelp false ("Circuit satisfiability: " <> show isSatisfied <> ", checker exited with " <> show res)

circuitSpecPure
  :: forall a avar b bvar f c
   . CircuitType f a avar
  => CircuitType f b bvar
  => PrimeField f
  => Eq b
  => Show b
  => Arbitrary a
  => Array c
  -> Checker f c
  -> Solver f a b
  -> (a -> Expectation f b)
  -> Aff Unit
circuitSpecPure constraints evalConstraint solver f =
  circuitSpecPure' constraints evalConstraint solver f arbitrary

circuitSpecPure'
  :: forall a b avar bvar f c
   . CircuitType f a avar
  => CircuitType f b bvar
  => PrimeField f
  => Eq b
  => Show b
  => Array c
  -> Checker f c
  -> Solver f a b
  -> (a -> Expectation f b)
  -> Gen a
  -> Aff Unit
circuitSpecPure' constraints evalConstraint solver isValid g = liftEffect
  let
    spc = un Identity <<<
      makeCircuitSpec { constraints, solver, evalConstraint, isValid }
  in
    quickCheck $
      g <#> spc

-- Warning: circuitSpec and circuitSpec' use unsafePerformEffect
-- to run their effects layer, use with caution
circuitSpec
  :: forall a avar b bvar f m c
   . CircuitType f a avar
  => CircuitType f b bvar
  => PrimeField f
  => Eq b
  => Show b
  => Monad m
  => Arbitrary a
  => (m ~> Effect)
  -> Array c
  -> Checker f c
  -> SolverT f m a b
  -> (a -> Expectation f b)
  -> Aff Unit
circuitSpec nat constraints evalConstraint solver f =
  circuitSpec' nat constraints evalConstraint solver f arbitrary

circuitSpec'
  :: forall a avar b bvar f m c
   . CircuitType f a avar
  => CircuitType f b bvar
  => PrimeField f
  => Eq b
  => Show b
  => Monad m
  => (m ~> Effect)
  -> Array c
  -> Checker f c
  -> SolverT f m a b
  -> (a -> Expectation f b)
  -> Gen a
  -> Aff Unit
circuitSpec' nat constraints evalConstraint solver isValid g =
  let
    spc = makeCircuitSpec { constraints, solver, evalConstraint, isValid }
  in
    liftEffect (quickCheck $ g <#> \a -> unsafePerformEffect $ nat $ spc a)