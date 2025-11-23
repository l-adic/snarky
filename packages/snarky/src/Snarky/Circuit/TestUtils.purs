module Snarky.Circuit.TestUtils where

import Prelude

import Control.Monad.Except (Except, runExcept, throwError)
import Data.Either (Either(..))
import Data.Identity (Identity(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Unsafe (unsafePerformEffect)
import Snarky.Circuit.CVar (EvaluationError(..))
import Snarky.Circuit.Compile (Solver, SolverT, makeChecker, runSolverT)
import Snarky.Circuit.Constraint (R1CS, evalR1CSConstraint)
import Snarky.Circuit.Types (class CircuitType, Variable)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (class Arbitrary, Result(..), arbitrary, quickCheck, withHelp)
import Test.QuickCheck.Gen (Gen)

type ConstraintSystem f = R1CS f Variable

data Expectation f a
  = Satisfied a
  | Unsatisfied
  | ProverError (EvaluationError f Variable -> Boolean)

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
         (Variable -> Except (EvaluationError f Variable) f)
         -> c
         -> Except (EvaluationError f Variable) Boolean
     , isValid :: a -> Expectation f b
     }
  -> a
  -> m Result
makeCircuitSpec { constraints, solver, evalConstraint, isValid } inputs = do
  runSolverT solver inputs <#> case _ of
    Left e ->
      case isValid inputs of
        ProverError f -> withHelp (f e) ("Prover exited with error " <> show e)
        _ -> withHelp false
          ("Encountered unexpected  error when proving circuit: " <> show e)
    Right (Tuple b assignments) ->
      let
        checker =
          let
            lookup v = case Map.lookup v assignments of
              Nothing -> throwError $ MissingVariable v
              Just res -> pure res
          in
            makeChecker (evalConstraint lookup)
      in
        case runExcept $ checker constraints of
          Left e -> withHelp false
            ("Encountered unexpected error when checking circuit: " <> show e)
          Right isSatisfied -> case isValid inputs of
            Satisfied expected | isSatisfied == true ->
              withHelp (expected == b)
                ( "Circuit disagrees with test function, got " <> show b
                    <> " expected "
                    <> show expected
                )
            Unsatisfied | isSatisfied == false -> Success
            res -> withHelp false
              ( "Circuit satisfiability: " <> show isSatisfied
                  <> ", checker exited with "
                  <> show res
              )

circuitSpecPure
  :: forall a avar b bvar f
   . CircuitType f a avar
  => CircuitType f b bvar
  => PrimeField f
  => Eq b
  => Show b
  => Arbitrary a
  => Array (R1CS f Variable)
  -> Solver f a b
  -> (a -> Expectation f b)
  -> Aff Unit
circuitSpecPure constraints solver f =
  circuitSpecPure' constraints solver f arbitrary

circuitSpecPure'
  :: forall a b avar bvar f
   . CircuitType f a avar
  => CircuitType f b bvar
  => PrimeField f
  => Eq b
  => Show b
  => Array (R1CS f Variable)
  -> Solver f a b
  -> (a -> Expectation f b)
  -> Gen a
  -> Aff Unit
circuitSpecPure' constraints solver isValid g = liftEffect
  let
    spc = un Identity <<<
      makeCircuitSpec
        { constraints, solver, evalConstraint: evalR1CSConstraint, isValid }
  in
    quickCheck $
      g <#> spc

-- Warning: circuitSpec and circuitSpec' use unsafePerformEffect
-- to run their effects layer, use with caution
circuitSpec
  :: forall a avar b bvar f m
   . CircuitType f a avar
  => CircuitType f b bvar
  => PrimeField f
  => Eq b
  => Show b
  => Monad m
  => Arbitrary a
  => (m ~> Effect)
  -> Array (R1CS f Variable)
  -> SolverT f m a b
  -> (a -> Expectation f b)
  -> Aff Unit
circuitSpec nat constraints solver f =
  circuitSpec' nat constraints solver f arbitrary

circuitSpec'
  :: forall a avar b bvar f m
   . CircuitType f a avar
  => CircuitType f b bvar
  => PrimeField f
  => Eq b
  => Show b
  => Monad m
  => (m ~> Effect)
  -> Array (R1CS f Variable)
  -> SolverT f m a b
  -> (a -> Expectation f b)
  -> Gen a
  -> Aff Unit
circuitSpec' nat constraints solver isValid g =
  let
    spc = makeCircuitSpec
      { constraints, solver, evalConstraint: evalR1CSConstraint, isValid }
  in
    liftEffect (quickCheck $ g <#> \a -> unsafePerformEffect $ nat $ spc a)