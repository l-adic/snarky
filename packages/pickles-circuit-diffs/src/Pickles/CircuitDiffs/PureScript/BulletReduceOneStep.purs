module Pickles.CircuitDiffs.PureScript.BulletReduceOneStep
  ( BulletReduceOneStepInput
  , parseBulletReduceOneStepInput
  , bulletReduceOneStepCircuit
  , compileBulletReduceOneStep
  ) where

import Prelude

import Data.Vector (Vector)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, unsafeIdx)
import Pickles.Step.Types (Field)
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

parseBulletReduceOneStepInput :: Vector 5 (FVar Field) -> BulletReduceOneStepInput Field
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
   . CircuitM Field (KimchiConstraint Field) t m
  => BulletReduceOneStepInput Field
  -> Snarky (KimchiConstraint Field) t m { p :: AffinePoint (FVar Field), isInfinity :: BoolVar Field }
bulletReduceOneStepCircuit input = do
  lScaled <- endoInv @Field @Pallas.ScalarField @PallasG input.l input.u
  rScaled <- endo @128 @32 input.r input.u
  addComplete lScaled rScaled

compileBulletReduceOneStep :: CompiledCircuit Field
compileBulletReduceOneStep =
  compilePure (Proxy @(Vector 5 (F Field))) (Proxy @Unit) (Proxy @(KimchiConstraint Field))
    (\inputs -> void $ bulletReduceOneStepCircuit (parseBulletReduceOneStepInput inputs))
    Kimchi.initialState
