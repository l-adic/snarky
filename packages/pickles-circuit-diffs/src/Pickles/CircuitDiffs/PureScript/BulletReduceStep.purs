module Pickles.CircuitDiffs.PureScript.BulletReduceStep
  ( parseBulletReduceStepInput
  , bulletReduceStepCircuit
  , compileBulletReduceStep
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.BulletReduce (BulletReduceInput)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, compiledCircuit, unsafeIdx)
import Pickles.IPA (bulletReduceCircuit)
import Pickles.Types (StepField)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, Snarky)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

parseBulletReduceStepInput :: Vector 75 (FVar StepField) -> BulletReduceInput 15 StepField
parseBulletReduceStepInput inputs =
  let
    at = unsafeIdx inputs
    readPt i = { x: at i, y: at (i + 1) }
  in
    { pairs: Vector.generate \j ->
        { l: readPt (4 * getFinite j), r: readPt (4 * getFinite j + 2) }
    , challenges: Vector.generate \j -> asSizedF128 (at (60 + getFinite j))
    }

bulletReduceStepCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => BulletReduceInput 15 StepField
  -> Snarky (KimchiConstraint StepField) t m { p :: AffinePoint (FVar StepField), isInfinity :: BoolVar StepField }
bulletReduceStepCircuit = bulletReduceCircuit @StepField @PallasG

compileBulletReduceStep :: CompiledCircuit StepField
compileBulletReduceStep = compiledCircuit @StepField $
  compilePure (Proxy @(Vector 75 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> void $ bulletReduceStepCircuit (parseBulletReduceStepInput inputs))
    Kimchi.initialState
