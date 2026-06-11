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
import Effect (Effect)
import Partial.Unsafe (unsafePartial)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, unsafeIdx)
import Pickles.Field (StepField)
import Pickles.FtComm (ftComm) as FtComm
import Pickles.Step.OtherField as StepOtherField
import Run as Run
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (Bool(..), BoolVar, F, FVar, Snarky, const_)
import Snarky.Circuit.Kimchi (SplitField(..), Type2(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField, generator, toAffine)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
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
    readPt i = AffinePoint { x: at i, y: at (i + 1) }
    readOtherField i = Type2 (SplitField { sDiv2: at i, sOdd: coerce (at (i + 1)) })
  in
    { tComm: Vector.generate \j -> readPt (2 * getFinite j)
    , perm: readOtherField 14
    , zetaToSrsLength: readOtherField 16
    , zetaToDomainSize: readOtherField 18
    }

ftcommStepCircuit
  :: forall r
   . PrimeField StepField
  => FtcommStepInput StepField
  -> Snarky StepField (KimchiConstraint StepField) r (AffinePoint (FVar StepField))
ftcommStepCircuit input =
  let
    g = unsafePartial $ fromJust $ toAffine (generator :: PallasG)
    sigmaLast = Vector.singleton (AffinePoint { x: const_ g.x, y: const_ g.y })
  in
    FtComm.ftComm StepOtherField.ipaScalarOps
      { sigmaLast
      , tComm: input.tComm
      , perm: input.perm
      , zetaToSrsLength: input.zetaToSrsLength
      , zetaToDomainSize: input.zetaToDomainSize
      }

compileFtcommStep :: Effect (CompiledCircuit StepField)
compileFtcommStep =
  Run.runBaseEffect $ compile (Proxy @(Vector 20 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> void $ ftcommStepCircuit (parseFtcommStepInput inputs))
