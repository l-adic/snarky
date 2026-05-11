module Pickles.CircuitDiffs.PureScript.BulletReduce
  ( BulletReduceInput
  , parseBulletReduceInput
  , bulletReduceWrapCircuit
  , compileBulletReduce
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, unsafeIdx)
import Pickles.IPA (bulletReduceCircuit)
import Pickles.Wrap.Types (Field)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, SizedF, Snarky)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type BulletReduceInput n f =
  { pairs :: Vector n { l :: AffinePoint (FVar f), r :: AffinePoint (FVar f) }
  , challenges :: Vector n (SizedF 128 (FVar f))
  }

parseBulletReduceInput :: Vector 80 (FVar Field) -> BulletReduceInput 16 Field
parseBulletReduceInput inputs =
  let
    at = unsafeIdx inputs
    readPt i = { x: at i, y: at (i + 1) }
  in
    { pairs: Vector.generate \j ->
        { l: readPt (4 * getFinite j), r: readPt (4 * getFinite j + 2) }
    , challenges: Vector.generate \j -> asSizedF128 (at (64 + getFinite j))
    }

bulletReduceWrapCircuit
  :: forall t m
   . CircuitM Field (KimchiConstraint Field) t m
  => BulletReduceInput 16 Field
  -> Snarky (KimchiConstraint Field) t m { p :: AffinePoint (FVar Field), isInfinity :: BoolVar Field }
bulletReduceWrapCircuit = bulletReduceCircuit @Field @VestaG

compileBulletReduce :: CompiledCircuit Field
compileBulletReduce =
  compilePure (Proxy @(Vector 80 (F Field))) (Proxy @Unit) (Proxy @(KimchiConstraint Field))
    (\inputs -> void $ bulletReduceWrapCircuit (parseBulletReduceInput inputs))
    Kimchi.initialState
