module Pickles.CircuitDiffs.PureScript.GroupMapStep
  ( parseGroupMapStepInput
  , groupMapStepCircuit
  , compileGroupMapStep
  ) where

import Prelude

import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Field (StepField)
import Run as Run
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F, FVar, Snarky)
import Snarky.Circuit.Kimchi (groupMapCircuit, groupMapParams) as Kimchi
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

parseGroupMapStepInput :: Vector 1 (FVar StepField) -> FVar StepField
parseGroupMapStepInput = Vector.head

groupMapStepCircuit
  :: forall r
   . PrimeField StepField
  => FVar StepField
  -> Snarky StepField (KimchiConstraint StepField) r (AffinePoint (FVar StepField))
groupMapStepCircuit = Kimchi.groupMapCircuit (Kimchi.groupMapParams (Proxy @PallasG))

compileGroupMapStep :: Effect (CompiledCircuit StepField)
compileGroupMapStep =
  Run.runBaseEffect $ compile (Proxy @(Vector 1 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> void $ groupMapStepCircuit (parseGroupMapStepInput inputs))
