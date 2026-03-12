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
import Pickles.Types (WrapField)
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

parseBulletReduceInput :: Vector 80 (FVar WrapField) -> BulletReduceInput 16 WrapField
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
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => BulletReduceInput 16 WrapField
  -> Snarky (KimchiConstraint WrapField) t m { p :: AffinePoint (FVar WrapField), isInfinity :: BoolVar WrapField }
bulletReduceWrapCircuit = bulletReduceCircuit @WrapField @VestaG

compileBulletReduce :: CompiledCircuit WrapField
compileBulletReduce =
  compilePure (Proxy @(Vector 80 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\inputs -> void $ bulletReduceWrapCircuit (parseBulletReduceInput inputs))
    Kimchi.initialState
