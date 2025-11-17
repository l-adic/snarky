module Snarky.Circuit.TestUtils where

import Prelude

import Control.Monad.Except (Except, runExcept, throwError)
import Data.Either (Either(..))
import Data.Identity (Identity(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Snarky.Circuit.CVar (EvaluationError(..))
import Snarky.Circuit.Compile (Solver, SolverT, makeChecker, runSolverT)
import Snarky.Circuit.Constraint (R1CS, evalR1CSConstraint)
import Snarky.Circuit.Types (class ConstrainedType, Variable)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (class Arbitrary, Result(..), arbitrary, quickCheck, withHelp)
import Test.QuickCheck.Gen (Gen)

type ConstraintSystem f = R1CS f Variable

makeCircuitSpec
  :: forall f c a b avar bvar m
   . ConstrainedType f a c avar
  => ConstrainedType f b c bvar
  => Eq b
  => PrimeField f
  => Monad m
  => { constraints :: Array c
     , solver :: SolverT f m a b
     , evalConstraint ::
         (Variable -> Except (EvaluationError f Variable) f)
         -> c
         -> Except (EvaluationError f Variable) Boolean
     , f :: a -> b
     }
  -> a
  -> m Result
makeCircuitSpec { constraints, solver, evalConstraint, f } inputs = do
  runSolverT solver inputs <#> case _ of
    Left e -> withHelp false ("Prover error when solving ciruit: " <> show e)
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
          Left e -> withHelp false ("Error during constraint checking: " <> show e)
          Right isSatisfied ->
            withHelp (isSatisfied && (f inputs == b)) "Circuit is satisfied and agrees with spec"

data AssertionExpectation f
  = Unsatisfied
  | Satisfied
  | ProverError (EvaluationError f Variable -> Boolean)

expectDivideByZero :: forall a f. a -> AssertionExpectation f
expectDivideByZero _ = ProverError \e -> case e of
  DivisionByZero _ -> true
  _ -> false

instance Show (AssertionExpectation f) where
  show = case _ of
    Unsatisfied -> "Unsatisfiable"
    Satisfied -> "Satisfied"
    ProverError _ -> "ProverError"

makeAssertionSpec
  :: forall f c a avar m
   . ConstrainedType f a c avar
  => Monad m
  => PrimeField f
  => { constraints :: Array c
     , solver :: SolverT f m a Unit
     , evalConstraint ::
         (Variable -> Except (EvaluationError f Variable) f)
         -> c
         -> Except (EvaluationError f Variable) Boolean
     , isValid :: a -> AssertionExpectation f
     }
  -> a
  -> m Result
makeAssertionSpec { constraints, solver, evalConstraint, isValid } inputs = do
  runSolverT solver inputs <#> case _ of
    Left e ->
      case isValid inputs of
        ProverError f -> withHelp (f e) ("Prover exited with error " <> show e)
        _ -> withHelp false ("Encountered unexpected  error when proving circuit: " <> show e)
    Right (Tuple _ assignments) ->
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
          Left e -> withHelp false ("Encountered unexpected  error when checking circuit: " <> show e)
          Right isSatisfied -> case isValid inputs of
            Satisfied | isSatisfied == true -> Success
            Unsatisfied | isSatisfied == false -> Success
            res -> withHelp false ("Circuit satisfiability: " <> show isSatisfied <> ", checker exited with " <> show res)

circuitSpec
  :: forall a avar b bvar f
   . ConstrainedType f a (R1CS f Variable) avar
  => ConstrainedType f b (R1CS f Variable) bvar
  => PrimeField f
  => Eq b
  => Arbitrary a
  => Array (R1CS f Variable)
  -> Solver f a b
  -> (a -> b)
  -> Aff Unit
circuitSpec constraints solver f =
  circuitSpec' constraints solver f arbitrary

circuitSpec'
  :: forall a avar b bvar f
   . ConstrainedType f a (R1CS f Variable) avar
  => ConstrainedType f b (R1CS f Variable) bvar
  => PrimeField f
  => Eq b
  => Array (R1CS f Variable)
  -> Solver f a b
  -> (a -> b)
  -> Gen a
  -> Aff Unit
circuitSpec' constraints solver f g = liftEffect
  let
    spc = un Identity <<<
      makeCircuitSpec { constraints, solver, evalConstraint: evalR1CSConstraint, f }
  in
    quickCheck $
      g <#> spc

assertionSpec
  :: forall a avar f
   . PrimeField f
  => ConstrainedType f a (R1CS f Variable) avar
  => Arbitrary a
  => Array (R1CS f Variable)
  -> Solver f a Unit
  -> (a -> AssertionExpectation f)
  -> Aff Unit
assertionSpec constraints solver isValid =
  assertionSpec' constraints solver isValid arbitrary

assertionSpec'
  :: forall a avar f
   . PrimeField f
  => ConstrainedType f a (R1CS f Variable) avar
  => Array (R1CS f Variable)
  -> Solver f a Unit
  -> (a -> AssertionExpectation f)
  -> Gen a
  -> Aff Unit
assertionSpec' constraints solver isValid g = liftEffect
  let
    spc = un Identity <<<
      makeAssertionSpec { constraints, solver, evalConstraint: evalR1CSConstraint, isValid }
  in
    quickCheck $
      g <#> spc