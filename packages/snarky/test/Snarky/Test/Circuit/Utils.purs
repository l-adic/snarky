module Test.Snarky.Test.Circuit.Utils
  ( circuitSpec
  , circuitSpec'
  , assertionSpec
  , assertionSpec'
  , ConstraintSystem
  ) where

import Prelude

import Data.Identity (Identity(..))
import Data.Newtype (un)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Snarky.Circuit.Compile (Solver, makeAssertionSpec, makeCircuitSpec)
import Snarky.Circuit.Constraint (R1CS, evalR1CSConstraint)
import Snarky.Circuit.Types (class ConstrainedType, Variable)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (class Arbitrary, arbitrary, quickCheck)
import Test.QuickCheck.Gen (Gen)

type ConstraintSystem f = R1CS f Variable

circuitSpec
  :: forall a avar b bvar f
   . PrimeField f
  => ConstrainedType f a (ConstraintSystem f) avar
  => ConstrainedType f b (ConstraintSystem f) bvar
  => Eq b
  => Arbitrary a
  => Array (ConstraintSystem f)
  -> Solver f a b
  -> (a -> b)
  -> Aff Unit
circuitSpec constraints solver f =
  circuitSpec' constraints solver f arbitrary

circuitSpec'
  :: forall a avar b bvar f
   . PrimeField f
  => ConstrainedType f a (ConstraintSystem f) avar
  => ConstrainedType f b (ConstraintSystem f) bvar
  => Eq b
  => Array (ConstraintSystem f)
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
  => ConstrainedType f a (ConstraintSystem f) avar
  => Arbitrary a
  => Array (ConstraintSystem f)
  -> Solver f a Unit
  -> (a -> Boolean)
  -> Aff Unit
assertionSpec constraints solver isValid =
  assertionSpec' constraints solver isValid arbitrary

assertionSpec'
  :: forall a avar f
   . PrimeField f
  => ConstrainedType f a (ConstraintSystem f) avar
  => Array (ConstraintSystem f)
  -> Solver f a Unit
  -> (a -> Boolean)
  -> Gen a
  -> Aff Unit
assertionSpec' constraints solver isValid g = liftEffect
  let
    spc = un Identity <<<
      makeAssertionSpec { constraints, solver, evalConstraint: evalR1CSConstraint, isValid }
  in
    quickCheck $
      g <#> spc