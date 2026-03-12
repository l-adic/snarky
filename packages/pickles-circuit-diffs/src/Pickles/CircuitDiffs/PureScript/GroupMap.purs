module Pickles.CircuitDiffs.PureScript.GroupMap
  ( parseGroupMapInput
  , groupMapCircuit
  , compileGroupMap
  ) where

import Prelude

import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, compiledCircuit)
import Pickles.Types (WrapField)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky)
import Snarky.Circuit.Kimchi (groupMapCircuit, groupMapParams) as Kimchi
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi (initialState) as Kimchi
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

parseGroupMapInput :: Vector 1 (FVar WrapField) -> FVar WrapField
parseGroupMapInput = Vector.head

groupMapCircuit
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => FVar WrapField
  -> Snarky (KimchiConstraint WrapField) t m (AffinePoint (FVar WrapField))
groupMapCircuit = Kimchi.groupMapCircuit (Kimchi.groupMapParams (Proxy @VestaG))

compileGroupMap :: CompiledCircuit WrapField
compileGroupMap = compiledCircuit @WrapField $
  compilePure (Proxy @(Vector 1 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\inputs -> void $ groupMapCircuit (parseGroupMapInput inputs))
    Kimchi.initialState
