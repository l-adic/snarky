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
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, unsafeIdx)
import Pickles.IPA (bulletReduceCircuit)
import Pickles.Step.Types (Field)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, Snarky)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

parseBulletReduceStepInput :: Vector 75 (FVar Field) -> BulletReduceInput 15 Field
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
   . CircuitM Field (KimchiConstraint Field) t m
  => BulletReduceInput 15 Field
  -> Snarky (KimchiConstraint Field) t m { p :: AffinePoint (FVar Field), isInfinity :: BoolVar Field }
bulletReduceStepCircuit = bulletReduceCircuit @Field @PallasG

compileBulletReduceStep :: CompiledCircuit Field
compileBulletReduceStep =
  compilePure (Proxy @(Vector 75 (F Field))) (Proxy @Unit) (Proxy @(KimchiConstraint Field))
    (\inputs -> void $ bulletReduceStepCircuit (parseBulletReduceStepInput inputs))
    Kimchi.initialState
