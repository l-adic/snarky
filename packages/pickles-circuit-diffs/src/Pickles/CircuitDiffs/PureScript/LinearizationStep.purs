module Pickles.CircuitDiffs.PureScript.LinearizationStep
  ( compileLinearizationStep
  ) where

import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, domainLog2)
import Pickles.CircuitDiffs.PureScript.LinearizationCommon (LinearizationInput, linearizationCircuitM)
import Pickles.Field (StepField)
import Pickles.Linearization.Pallas as PallasTokens
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F, UnChecked)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))

compileLinearizationStep :: Effect (CompiledCircuit StepField)
compileLinearizationStep =
  compile noAdvice
    (Proxy @(UnChecked (LinearizationInput (F StepField))))
    (Proxy @(F StepField))
    (Proxy @(KimchiConstraint StepField))
    (linearizationCircuitM domainLog2 PallasTokens.constantTermTokens)
