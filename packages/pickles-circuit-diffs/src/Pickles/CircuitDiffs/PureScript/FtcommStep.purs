module Pickles.CircuitDiffs.PureScript.FtcommStep
  ( FtcommStepInput
  , parseFtcommStepInput
  , ftcommStepCircuit
  , compileFtcommStep
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Maybe (fromJust)
import Data.Vector (Vector)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, unsafeIdx)
import Pickles.Field (StepField)
import Pickles.FtComm (ftComm) as FtComm
import Pickles.Step.OtherField as StepOtherField
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F, FVar, Snarky, const_)
import Snarky.Circuit.Kimchi (SplitField(..), Type2(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (generator, toAffine)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type FtcommStepInput f =
  { tComm :: Vector 7 (AffinePoint (FVar f))
  , perm :: Type2 (SplitField (FVar f) (BoolVar f))
  , zetaToSrsLength :: Type2 (SplitField (FVar f) (BoolVar f))
  , zetaToDomainSize :: Type2 (SplitField (FVar f) (BoolVar f))
  }

parseFtcommStepInput :: Vector 20 (FVar StepField) -> FtcommStepInput StepField
parseFtcommStepInput inputs =
  let
    at = unsafeIdx inputs
    readPt i = { x: at i, y: at (i + 1) }
    readOtherField i = Type2 (SplitField { sDiv2: at i, sOdd: coerce (at (i + 1)) })
  in
    { tComm: Vector.generate \j -> readPt (2 * getFinite j)
    , perm: readOtherField 14
    , zetaToSrsLength: readOtherField 16
    , zetaToDomainSize: readOtherField 18
    }

ftcommStepCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => FtcommStepInput StepField
  -> Snarky (KimchiConstraint StepField) t m (AffinePoint (FVar StepField))
ftcommStepCircuit input =
  let
    g = unsafePartial $ fromJust $ toAffine (generator :: PallasG)
    sigmaLast = { x: const_ g.x, y: const_ g.y }
  in
    FtComm.ftComm StepOtherField.ipaScalarOps
      { sigmaLast
      , tComm: input.tComm
      , perm: input.perm
      , zetaToSrsLength: input.zetaToSrsLength
      , zetaToDomainSize: input.zetaToDomainSize
      }

compileFtcommStep :: CompiledCircuit StepField
compileFtcommStep =
  compilePure (Proxy @(Vector 20 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> void $ ftcommStepCircuit (parseFtcommStepInput inputs))
    Kimchi.initialState
