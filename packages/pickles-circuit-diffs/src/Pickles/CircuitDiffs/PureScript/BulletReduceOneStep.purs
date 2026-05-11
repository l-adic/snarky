module Pickles.CircuitDiffs.PureScript.BulletReduceOneStep
  ( BulletReduceOneStepInput
  , parseBulletReduceOneStepInput
  , bulletReduceOneStepCircuit
  , compileBulletReduceOneStep
  ) where

import Prelude

import Data.Vector (Vector)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, unsafeIdx)
import Pickles.Types (StepField)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, SizedF, Snarky)
import Snarky.Circuit.Kimchi (addComplete, endo, endoInv)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type BulletReduceOneStepInput f =
  { l :: AffinePoint (FVar f)
  , r :: AffinePoint (FVar f)
  , u :: SizedF 128 (FVar f)
  }

parseBulletReduceOneStepInput :: Vector 5 (FVar StepField) -> BulletReduceOneStepInput StepField
parseBulletReduceOneStepInput inputs =
  let
    at = unsafeIdx inputs
  in
    { l: { x: at 0, y: at 1 }
    , r: { x: at 2, y: at 3 }
    , u: asSizedF128 (at 4)
    }

bulletReduceOneStepCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => BulletReduceOneStepInput StepField
  -> Snarky (KimchiConstraint StepField) t m { p :: AffinePoint (FVar StepField), isInfinity :: BoolVar StepField }
bulletReduceOneStepCircuit input = do
  lScaled <- endoInv @StepField @Pallas.ScalarField @PallasG input.l input.u
  rScaled <- endo @128 @32 input.r input.u
  addComplete lScaled rScaled

compileBulletReduceOneStep :: CompiledCircuit StepField
compileBulletReduceOneStep =
  compilePure (Proxy @(Vector 5 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> void $ bulletReduceOneStepCircuit (parseBulletReduceOneStepInput inputs))
    Kimchi.initialState
