module Pickles.CircuitDiffs.PureScript.GroupMap
  ( groupMapCircuit
  , compileGroupMap
  ) where

import Prelude

import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Field (WrapField)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F, FVar, Snarky)
import Snarky.Circuit.Kimchi (groupMapCircuit, groupMapParams) as Kimchi
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

groupMapCircuit
  :: forall r
   . PrimeField WrapField
  => FVar WrapField
  -> Snarky WrapField (KimchiConstraint WrapField) r (AffinePoint (FVar WrapField))
groupMapCircuit = Kimchi.groupMapCircuit (Kimchi.groupMapParams (Proxy @VestaG))

compileGroupMap :: Effect (CompiledCircuit WrapField)
compileGroupMap =
  compile noAdvice (Proxy @(F WrapField)) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (void <<< groupMapCircuit)
