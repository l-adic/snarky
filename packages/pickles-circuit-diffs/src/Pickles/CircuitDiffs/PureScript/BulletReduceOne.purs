module Pickles.CircuitDiffs.PureScript.BulletReduceOne
  ( BulletReduceOneInput
  , parseBulletReduceOneInput
  , bulletReduceOneCircuit
  , compileBulletReduceOne
  ) where

import Prelude

import Data.Vector (Vector)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, unsafeIdx)
import Pickles.Wrap.Types (Field)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, SizedF, Snarky)
import Snarky.Circuit.Kimchi (addComplete, endo, endoInv)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Pasta (VestaG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type BulletReduceOneInput f =
  { l :: AffinePoint (FVar f)
  , r :: AffinePoint (FVar f)
  , u :: SizedF 128 (FVar f)
  }

parseBulletReduceOneInput :: Vector 5 (FVar Field) -> BulletReduceOneInput Field
parseBulletReduceOneInput inputs =
  let
    at = unsafeIdx inputs
  in
    { l: { x: at 0, y: at 1 }
    , r: { x: at 2, y: at 3 }
    , u: asSizedF128 (at 4)
    }

bulletReduceOneCircuit
  :: forall t m
   . CircuitM Field (KimchiConstraint Field) t m
  => BulletReduceOneInput Field
  -> Snarky (KimchiConstraint Field) t m { p :: AffinePoint (FVar Field), isInfinity :: BoolVar Field }
bulletReduceOneCircuit input = do
  lScaled <- endoInv @Field @Vesta.ScalarField @VestaG input.l input.u
  rScaled <- endo @128 @32 input.r input.u
  addComplete lScaled rScaled

compileBulletReduceOne :: CompiledCircuit Field
compileBulletReduceOne =
  compilePure (Proxy @(Vector 5 (F Field))) (Proxy @Unit) (Proxy @(KimchiConstraint Field))
    (\inputs -> void $ bulletReduceOneCircuit (parseBulletReduceOneInput inputs))
    Kimchi.initialState
