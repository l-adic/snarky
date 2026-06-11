module Pickles.CircuitDiffs.PureScript.BulletReduceStep
  ( parseBulletReduceStepInput
  , bulletReduceStepCircuit
  , compileBulletReduceStep
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.BulletReduce (BulletReduceInput)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, unsafeIdx)
import Pickles.Field (StepField)
import Pickles.IPA (bulletReduceCircuit)
import Run as Run
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (BoolVar, F, FVar, Snarky)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

parseBulletReduceStepInput :: Vector 75 (FVar StepField) -> BulletReduceInput 15 StepField
parseBulletReduceStepInput inputs =
  let
    at = unsafeIdx inputs
    readPt i = AffinePoint { x: at i, y: at (i + 1) }
  in
    { pairs: Vector.generate \j ->
        { l: readPt (4 * getFinite j), r: readPt (4 * getFinite j + 2) }
    , challenges: Vector.generate \j -> asSizedF128 (at (60 + getFinite j))
    }

bulletReduceStepCircuit
  :: forall r
   . PrimeField StepField
  => BulletReduceInput 15 StepField
  -> Snarky StepField (KimchiConstraint StepField) r { p :: AffinePoint (FVar StepField), isInfinity :: BoolVar StepField }
bulletReduceStepCircuit = bulletReduceCircuit @StepField @PallasG

compileBulletReduceStep :: Effect (CompiledCircuit StepField)
compileBulletReduceStep =
  Run.runBaseEffect $ compile (Proxy @(Vector 75 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> void $ bulletReduceStepCircuit (parseBulletReduceStepInput inputs))
