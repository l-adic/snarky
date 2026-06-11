module Pickles.CircuitDiffs.PureScript.LinearizationStep
  ( compileLinearizationStep
  ) where

import Prelude

import Data.Vector (Vector)
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, domainLog2)
import Pickles.CircuitDiffs.PureScript.LinearizationCommon (linearizationCircuitM)
import Pickles.Field (StepField)
import Pickles.Linearization.Pallas as PallasTokens
import Run as Run
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))

compileLinearizationStep :: Effect (CompiledCircuit StepField)
compileLinearizationStep =
  Run.runBaseEffect $ compile
    (Proxy @(Vector 90 (F StepField)))
    (Proxy @(F StepField))
    (Proxy @(KimchiConstraint StepField))
    (linearizationCircuitM domainLog2 PallasTokens.constantTermTokens)
