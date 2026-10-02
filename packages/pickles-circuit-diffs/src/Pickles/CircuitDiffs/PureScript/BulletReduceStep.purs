module Pickles.CircuitDiffs.PureScript.BulletReduceStep
  ( compileBulletReduceStep
  ) where

import Prelude

import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.BulletReduce (BulletReduceInput(..))
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Field (StepField)
import Pickles.IPA (bulletReduceCircuit)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F, FVar, SizedF, Snarky, UnChecked(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pasta (PallasG)
import Type.Proxy (Proxy(..))

bulletReduceStepCircuit
  :: forall r
   . UnChecked (BulletReduceInput 15 (FVar StepField) (SizedF 128 (FVar StepField)))
  -> Snarky StepField (KimchiConstraint StepField) r Unit
bulletReduceStepCircuit (UnChecked (BulletReduceInput i)) =
  void $ bulletReduceCircuit @StepField @PallasG i

compileBulletReduceStep :: Effect (CompiledCircuit StepField)
compileBulletReduceStep =
  compile noAdvice (Proxy @(UnChecked (BulletReduceInput 15 StepField (SizedF 128 (F StepField)))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    bulletReduceStepCircuit
