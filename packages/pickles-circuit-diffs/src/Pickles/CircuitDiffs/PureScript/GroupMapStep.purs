module Pickles.CircuitDiffs.PureScript.GroupMapStep
  ( groupMapStepCircuit
  , compileGroupMapStep
  ) where

import Prelude

import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Field (StepField)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F, FVar, Snarky)
import Snarky.Circuit.Kimchi (groupMapCircuit, groupMapParams) as Kimchi
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

groupMapStepCircuit
  :: forall r
   . PrimeField StepField
  => FVar StepField
  -> Snarky StepField (KimchiConstraint StepField) r (AffinePoint (FVar StepField))
groupMapStepCircuit = Kimchi.groupMapCircuit (Kimchi.groupMapParams (Proxy @PallasG))

compileGroupMapStep :: Effect (CompiledCircuit StepField)
compileGroupMapStep =
  compile noAdvice (Proxy @(F StepField)) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (void <<< groupMapStepCircuit)
