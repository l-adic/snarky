module Test.Snarky.Curves.Main where

import Prelude

import Effect (Effect)
import Snarky.Curves.BN254 as BN254
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.Snarky.Curves.BaseField as BaseField
import Test.Snarky.Curves.Field as Field
import Test.Snarky.Curves.GroupElement as GroupElement
import Test.Spec (describe)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  describe "Bn254.ScalarField" $
    Field.spec (Proxy @BN254.ScalarField)
  describe "Pallas.ScalarField" $
    Field.spec (Proxy @Pallas.ScalarField)
  describe "Pallas.BaseField" $
    Field.spec (Proxy @Pallas.BaseField)
  describe "Vesta.ScalarField" $
    Field.spec (Proxy @Vesta.ScalarField)
  describe "Vesta.BaseField" $
    BaseField.spec (Proxy @Vesta.BaseField)
  GroupElement.spec