module Pickles.CircuitDiffs.PureScript.LinearizationWrap
  ( compileLinearizationWrap
  ) where

import Data.Vector (Vector)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, wrapDomainLog2)
import Pickles.CircuitDiffs.PureScript.LinearizationCommon (linearizationCircuitM)
import Pickles.Linearization.Vesta as VestaTokens
import Pickles.Types (WrapField)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (F)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))

compileLinearizationWrap :: CompiledCircuit WrapField
compileLinearizationWrap =
  compilePure
    (Proxy @(Vector 90 (F WrapField)))
    (Proxy @(F WrapField))
    (Proxy @(KimchiConstraint WrapField))
    (linearizationCircuitM wrapDomainLog2 VestaTokens.constantTermTokens)
    Kimchi.initialState
