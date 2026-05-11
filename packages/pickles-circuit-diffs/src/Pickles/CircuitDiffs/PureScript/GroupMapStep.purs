module Pickles.CircuitDiffs.PureScript.GroupMapStep
  ( parseGroupMapStepInput
  , groupMapStepCircuit
  , compileGroupMapStep
  ) where

import Prelude

import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Step.Types (Field)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky)
import Snarky.Circuit.Kimchi (groupMapCircuit, groupMapParams) as Kimchi
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi (initialState) as Kimchi
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

parseGroupMapStepInput :: Vector 1 (FVar Field) -> FVar Field
parseGroupMapStepInput = Vector.head

groupMapStepCircuit
  :: forall t m
   . CircuitM Field (KimchiConstraint Field) t m
  => FVar Field
  -> Snarky (KimchiConstraint Field) t m (AffinePoint (FVar Field))
groupMapStepCircuit = Kimchi.groupMapCircuit (Kimchi.groupMapParams (Proxy @PallasG))

compileGroupMapStep :: CompiledCircuit Field
compileGroupMapStep =
  compilePure (Proxy @(Vector 1 (F Field))) (Proxy @Unit) (Proxy @(KimchiConstraint Field))
    (\inputs -> void $ groupMapStepCircuit (parseGroupMapStepInput inputs))
    Kimchi.initialState
