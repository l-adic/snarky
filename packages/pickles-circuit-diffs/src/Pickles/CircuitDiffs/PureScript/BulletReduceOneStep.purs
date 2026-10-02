module Pickles.CircuitDiffs.PureScript.BulletReduceOneStep
  ( compileBulletReduceOneStep
  ) where

import Prelude

import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.BulletReduceOne (BulletReduceOneInput(..))
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Field (StepField)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F, FVar, SizedF, Snarky, UnChecked(..))
import Snarky.Circuit.Kimchi (addComplete, endo, endoInv)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

bulletReduceOneStepCircuit
  :: forall r
   . UnChecked (BulletReduceOneInput (AffinePoint (FVar StepField)) (SizedF 128 (FVar StepField)))
  -> Snarky StepField (KimchiConstraint StepField) r Unit
bulletReduceOneStepCircuit (UnChecked (BulletReduceOneInput i)) = do
  lScaled <- endoInv @StepField @Pallas.ScalarField @PallasG i.l i.u
  rScaled <- endo @128 @32 i.r i.u
  void $ addComplete lScaled rScaled

compileBulletReduceOneStep :: Effect (CompiledCircuit StepField)
compileBulletReduceOneStep =
  compile noAdvice
    (Proxy @(UnChecked (BulletReduceOneInput (AffinePoint StepField) (SizedF 128 (F StepField)))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    bulletReduceOneStepCircuit
