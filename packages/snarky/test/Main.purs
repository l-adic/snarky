module Test.Snarky.Circuit.Main where

import Prelude

import Effect (Effect)
import Snarky.Constraint.Basic (Basic)
import Snarky.Constraint.Basic as Basic
import Snarky.Curves.BN254 as BN254
import Snarky.Curves.Vesta as Vesta
import Test.Snarky.Circuit as CircuitTests
import Test.Snarky.Circuit.Types as TypesTests
import Test.Snarky.Constraint as ConstraintTests
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  ConstraintTests.spec $ Proxy @BN254.ScalarField
  CircuitTests.spec (Proxy @Vesta.ScalarField) (Proxy @(Basic Vesta.ScalarField)) (Basic.eval)
  TypesTests.spec $ Proxy @(Vesta.BaseField)