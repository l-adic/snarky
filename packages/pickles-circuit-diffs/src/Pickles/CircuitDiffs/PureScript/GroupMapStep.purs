module Pickles.CircuitDiffs.PureScript.GroupMapStep
  ( parseGroupMapStepInput
  , groupMapStepCircuit
  , compileGroupMapStep
  ) where

import Prelude

import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Field (StepField)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky)
import Snarky.Circuit.Kimchi (groupMapCircuit, groupMapParams) as Kimchi
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi (initialState) as Kimchi
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

parseGroupMapStepInput :: Vector 1 (FVar StepField) -> FVar StepField
parseGroupMapStepInput = Vector.head

groupMapStepCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => FVar StepField
  -> Snarky (KimchiConstraint StepField) t m (AffinePoint (FVar StepField))
groupMapStepCircuit = Kimchi.groupMapCircuit (Kimchi.groupMapParams (Proxy @PallasG))

compileGroupMapStep :: CompiledCircuit StepField
compileGroupMapStep =
  compilePure (Proxy @(Vector 1 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> void $ groupMapStepCircuit (parseGroupMapStepInput inputs))
    Kimchi.initialState
