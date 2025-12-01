module Test.Snarky.Circuit.R1CS (spec) where

import Prelude

import Snarky.Constraint.R1CS (R1CS, eval)
import Snarky.Curves.Vesta as Vesta
import Test.Snarky.Circuit as CircuitTests
import Test.Spec (Spec)
import Type.Proxy (Proxy(..))

spec :: Spec Unit
spec = do
  CircuitTests.spec (Proxy @Vesta.BaseField) (Proxy @(R1CS Vesta.BaseField)) eval
