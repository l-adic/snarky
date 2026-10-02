module Pickles.CircuitDiffs.PureScript.FtcommStep
  ( compileFtcommStep
  ) where

import Prelude

import Data.Maybe (fromJust)
import Data.Vector as Vector
import Effect (Effect)
import Partial.Unsafe (unsafePartial)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.CircuitDiffs.PureScript.Ftcomm (FtcommInput(..))
import Pickles.Field (StepField)
import Pickles.IncrementallyVerifyProof (ftComm) as FtComm
import Pickles.Step.OtherField as StepOtherField
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (BoolVar, F, FVar, Snarky, UnChecked(..), const_)
import Snarky.Circuit.Kimchi (SplitField, Type2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (generator, toAffine)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

ftcommStepCircuit
  :: forall r
   . UnChecked (FtcommInput (AffinePoint (FVar StepField)) (Type2 (SplitField (FVar StepField) (BoolVar StepField))))
  -> Snarky StepField (KimchiConstraint StepField) r Unit
ftcommStepCircuit (UnChecked (FtcommInput i)) =
  let
    g = unsafePartial $ fromJust $ toAffine (generator :: PallasG)
    sigmaLast = Vector.singleton (AffinePoint { x: const_ g.x, y: const_ g.y })
  in
    void $ FtComm.ftComm StepOtherField.ipaScalarOps
      { sigmaLast
      , tComm: i.tComm
      , perm: i.perm
      , zetaToSrsLength: i.zetaToSrsLength
      , zetaToDomainSize: i.zetaToDomainSize
      }

compileFtcommStep :: Effect (CompiledCircuit StepField)
compileFtcommStep =
  compile noAdvice
    (Proxy @(UnChecked (FtcommInput (AffinePoint StepField) (Type2 (SplitField (F StepField) Boolean)))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    ftcommStepCircuit
