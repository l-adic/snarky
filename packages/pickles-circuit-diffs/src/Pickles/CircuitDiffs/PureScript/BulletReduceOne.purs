module Pickles.CircuitDiffs.PureScript.BulletReduceOne
  ( BulletReduceOneInput
  , parseBulletReduceOneInput
  , bulletReduceOneCircuit
  , compileBulletReduceOne
  ) where

import Prelude

import Data.Vector (Vector)
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, unsafeIdx)
import Pickles.Field (WrapField)
import Run as Run
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (BoolVar, F, FVar, SizedF, Snarky)
import Snarky.Circuit.Kimchi (addComplete, endo, endoInv)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

type BulletReduceOneInput f =
  { l :: AffinePoint (FVar f)
  , r :: AffinePoint (FVar f)
  , u :: SizedF 128 (FVar f)
  }

parseBulletReduceOneInput :: Vector 5 (FVar WrapField) -> BulletReduceOneInput WrapField
parseBulletReduceOneInput inputs =
  let
    at = unsafeIdx inputs
  in
    { l: AffinePoint { x: at 0, y: at 1 }
    , r: AffinePoint { x: at 2, y: at 3 }
    , u: asSizedF128 (at 4)
    }

bulletReduceOneCircuit
  :: forall r
   . PrimeField WrapField
  => BulletReduceOneInput WrapField
  -> Snarky WrapField (KimchiConstraint WrapField) r { p :: AffinePoint (FVar WrapField), isInfinity :: BoolVar WrapField }
bulletReduceOneCircuit input = do
  lScaled <- endoInv @WrapField @Vesta.ScalarField @VestaG input.l input.u
  rScaled <- endo @128 @32 input.r input.u
  addComplete lScaled rScaled

compileBulletReduceOne :: Effect (CompiledCircuit WrapField)
compileBulletReduceOne =
  Run.runBaseEffect $ compile (Proxy @(Vector 5 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\inputs -> void $ bulletReduceOneCircuit (parseBulletReduceOneInput inputs))
