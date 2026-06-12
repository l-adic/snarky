module Pickles.CircuitDiffs.PureScript.LinearizationWrap
  ( compileLinearizationWrap
  ) where

import Data.Vector (Vector)
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, wrapDomainLog2)
import Pickles.CircuitDiffs.PureScript.LinearizationCommon (linearizationCircuitM)
import Pickles.Field (WrapField)
import Pickles.Linearization.Vesta as VestaTokens
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))

compileLinearizationWrap :: Effect (CompiledCircuit WrapField)
compileLinearizationWrap =
  compile noAdvice
    (Proxy @(Vector 90 (F WrapField)))
    (Proxy @(F WrapField))
    (Proxy @(KimchiConstraint WrapField))
    (linearizationCircuitM wrapDomainLog2 VestaTokens.constantTermTokens)
