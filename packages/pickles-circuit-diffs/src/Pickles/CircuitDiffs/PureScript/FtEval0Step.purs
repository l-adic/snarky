module Pickles.CircuitDiffs.PureScript.FtEval0Step
  ( compileFtEval0Step
  ) where

import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, domainLog2)
import Pickles.CircuitDiffs.PureScript.FtEval0Common (FtEval0Input, ftEval0CircuitM)
import Pickles.Field (StepField)
import Pickles.Linearization.Pallas as PallasTokens
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F, UnChecked)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))

compileFtEval0Step :: Effect (CompiledCircuit StepField)
compileFtEval0Step =
  compile noAdvice
    (Proxy @(UnChecked (FtEval0Input (F StepField))))
    (Proxy @(F StepField))
    (Proxy @(KimchiConstraint StepField))
    (ftEval0CircuitM domainLog2 PallasTokens.constantTermTokens)
