module Test.Snarky.Circuit.Main where

import Prelude

import Effect (Effect)
import Snarky.Curves.BN254 as BN254
import Snarky.Curves.Vesta as Vesta
import Snarky.Test.Circuit.Constraint as ConstraintTests
import Test.Snarky.Circuit.Assert as AssertTest
import Test.Snarky.Circuit.Bits as BitsTest
import Test.Snarky.Circuit.Boolean as BoolTest
import Test.Snarky.Circuit.Factors as Factors
import Test.Snarky.Circuit.Field as FieldTest
import Test.Snarky.Circuit.Types as TypesTest
import Test.Spec (Spec)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  ConstraintTests.spec $ Proxy @BN254.ScalarField
  circuitSpec
  Factors.spec $ Proxy @Vesta.ScalarField

circuitSpec :: Spec Unit
circuitSpec = do
  FieldTest.spec $ Proxy @Vesta.ScalarField
  BoolTest.spec $ Proxy @Vesta.BaseField
  AssertTest.spec $ Proxy @BN254.ScalarField
  BitsTest.spec $ Proxy @Vesta.ScalarField
  TypesTest.spec $ Proxy @Vesta.ScalarField