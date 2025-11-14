module Test.Snarky.Circuit.Curves.Main where

import Prelude

import Data.Identity (Identity(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..), uncurry)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Snarky.Circuit.Compile (Solver, makeAssertionSpec, makeCircuitSpec, makeSolver, compile)
import Snarky.Circuit.Constraint (R1CS, evalR1CSConstraint)
import Snarky.Circuit.Curves (AffinePoint(..), CurveParams(..), assertOnCurve, genAffinePoint)
import Snarky.Circuit.Types (class ConstrainedType, Variable)
import Snarky.Curves.Class (class PrimeField, curveParams)
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (class Arbitrary, arbitrary, quickCheck)
import Test.QuickCheck.Gen (Gen)
import Test.Spec (describe, it)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))

type Curve = Vesta.G

type Fr = Vesta.ScalarField

type Fq = Vesta.BaseField

type ConstraintSystem = R1CS Fq Variable

type AssertOnCurvePublicInputs =
  Tuple
    (CurveParams Fq)
    (AffinePoint Fq)

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  describe "Snarky.Circuit.Curves" do

    it "assertOnCurve Circuit is Valid" $
      let
        isValid :: AssertOnCurvePublicInputs -> Boolean
        isValid (Tuple (CurveParams { a, b }) (AffinePoint { x, y })) =
          let
            y_sq = y * y
            x_sq = x * x
            x_cb = x_sq * x
            rhs = x_cb + a * x + b
          in
            y_sq == rhs
        solver = makeSolver (Proxy @ConstraintSystem) (uncurry assertOnCurve)
        { constraints } = un Identity $
          compile
            (Proxy @AssertOnCurvePublicInputs)
            (Proxy @Unit)
            (uncurry assertOnCurve)

        gen :: Gen AssertOnCurvePublicInputs
        gen = do
          p :: AffinePoint Fq <- genAffinePoint (Proxy @Curve)
          pure $ Tuple (CurveParams $ curveParams (Proxy @Curve)) p

      in
        assertionSpec' constraints solver isValid gen

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
  -> (a -> Boolean)
  -> Aff Unit
assertionSpec constraints solver isValid =
  assertionSpec' constraints solver isValid arbitrary

assertionSpec'
  :: forall a avar f
   . PrimeField f
  => ConstrainedType f a (R1CS f Variable) avar
  => Array (R1CS f Variable)
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