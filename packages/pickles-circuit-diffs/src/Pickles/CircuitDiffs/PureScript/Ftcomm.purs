module Pickles.CircuitDiffs.PureScript.Ftcomm
  ( FtcommInput
  , parseFtcommInput
  , ftcommWrapCircuit
  , compileFtcomm
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Maybe (fromJust)
import Data.Vector (Vector)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, unsafeIdx)
import Pickles.Field (WrapField)
import Pickles.FtComm (ftComm) as FtComm
import Pickles.Wrap.OtherField as WrapOtherField
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, const_)
import Snarky.Circuit.Kimchi (Type1(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (generator, toAffine)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type FtcommInput f =
  { tComm :: Vector 7 (AffinePoint (FVar f))
  , perm :: Type1 (FVar f)
  , zetaToSrsLength :: Type1 (FVar f)
  , zetaToDomainSize :: Type1 (FVar f)
  }

parseFtcommInput :: Vector 17 (FVar WrapField) -> FtcommInput WrapField
parseFtcommInput inputs =
  let
    at = unsafeIdx inputs
    readPt i = { x: at i, y: at (i + 1) }
  in
    { tComm: Vector.generate \j -> readPt (2 * getFinite j)
    , perm: Type1 (at 14)
    , zetaToSrsLength: Type1 (at 15)
    , zetaToDomainSize: Type1 (at 16)
    }

ftcommWrapCircuit
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => FtcommInput WrapField
  -> Snarky (KimchiConstraint WrapField) t m (AffinePoint (FVar WrapField))
ftcommWrapCircuit input =
  let
    g = unsafePartial $ fromJust $ toAffine (generator :: VestaG)
    sigmaLast = Vector.singleton { x: const_ g.x, y: const_ g.y }
  in
    FtComm.ftComm WrapOtherField.ipaScalarOps
      { sigmaLast
      , tComm: input.tComm
      , perm: input.perm
      , zetaToSrsLength: input.zetaToSrsLength
      , zetaToDomainSize: input.zetaToDomainSize
      }

compileFtcomm :: CompiledCircuit WrapField
compileFtcomm =
  compilePure (Proxy @(Vector 17 (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\inputs -> void $ ftcommWrapCircuit (parseFtcommInput inputs))
    Kimchi.initialState
