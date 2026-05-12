module Pickles.CircuitDiffs.PureScript.LinearizationStep
  ( compileLinearizationStep
  ) where

import Data.Vector (Vector)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, domainLog2)
import Pickles.CircuitDiffs.PureScript.LinearizationCommon (linearizationCircuitM)
import Pickles.Field (StepField)
import Pickles.Linearization.Pallas as PallasTokens
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (F)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))

compileLinearizationStep :: CompiledCircuit StepField
compileLinearizationStep =
  compilePure
    (Proxy @(Vector 90 (F StepField)))
    (Proxy @(F StepField))
    (Proxy @(KimchiConstraint StepField))
    (linearizationCircuitM domainLog2 PallasTokens.constantTermTokens)
    Kimchi.initialState
