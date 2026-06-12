module Pickles.CircuitDiffs.PureScript.BulletReduceOneStep
  ( BulletReduceOneStepInput
  , parseBulletReduceOneStepInput
  , bulletReduceOneStepCircuit
  , compileBulletReduceOneStep
  ) where

import Prelude

import Data.Vector (Vector)
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, unsafeIdx)
import Pickles.Field (StepField)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (BoolVar, F, FVar, SizedF, Snarky)
import Snarky.Circuit.Kimchi (addComplete, endo, endoInv)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
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
    { l: AffinePoint { x: at 0, y: at 1 }
    , r: AffinePoint { x: at 2, y: at 3 }
    , u: asSizedF128 (at 4)
    }

bulletReduceOneStepCircuit
  :: forall r
   . PrimeField StepField
  => BulletReduceOneStepInput StepField
  -> Snarky StepField (KimchiConstraint StepField) r { p :: AffinePoint (FVar StepField), isInfinity :: BoolVar StepField }
bulletReduceOneStepCircuit input = do
  lScaled <- endoInv @StepField @Pallas.ScalarField @PallasG input.l input.u
  rScaled <- endo @128 @32 input.r input.u
  addComplete lScaled rScaled

compileBulletReduceOneStep :: Effect (CompiledCircuit StepField)
compileBulletReduceOneStep =
  compile noAdvice (Proxy @(Vector 5 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> void $ bulletReduceOneStepCircuit (parseBulletReduceOneStepInput inputs))
