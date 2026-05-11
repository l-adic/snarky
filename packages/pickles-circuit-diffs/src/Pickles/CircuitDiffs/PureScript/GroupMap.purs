module Pickles.CircuitDiffs.PureScript.GroupMap
  ( parseGroupMapInput
  , groupMapCircuit
  , compileGroupMap
  ) where

import Prelude

import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Wrap.Types (Field)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky)
import Snarky.Circuit.Kimchi (groupMapCircuit, groupMapParams) as Kimchi
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi (initialState) as Kimchi
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

parseGroupMapInput :: Vector 1 (FVar Field) -> FVar Field
parseGroupMapInput = Vector.head

groupMapCircuit
  :: forall t m
   . CircuitM Field (KimchiConstraint Field) t m
  => FVar Field
  -> Snarky (KimchiConstraint Field) t m (AffinePoint (FVar Field))
groupMapCircuit = Kimchi.groupMapCircuit (Kimchi.groupMapParams (Proxy @VestaG))

compileGroupMap :: CompiledCircuit Field
compileGroupMap =
  compilePure (Proxy @(Vector 1 (F Field))) (Proxy @Unit) (Proxy @(KimchiConstraint Field))
    (\inputs -> void $ groupMapCircuit (parseGroupMapInput inputs))
    Kimchi.initialState
