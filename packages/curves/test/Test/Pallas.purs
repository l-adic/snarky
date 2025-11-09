module Test.Pallas where

import Prelude

import Effect.Class (liftEffect)
import Snarky.Curves.Pallas (ScalarField)
import Snarky.Curves.Pallas as Pallas
import Test.QuickCheck (quickCheck)
import Test.QuickCheck.Laws.Data as Laws
import Test.Spec (Spec, describe, it)
import Test.BigInt (bigIntHomomorphismSpec)
import Type.Proxy (Proxy(..))

spec :: Spec Unit
spec = describe "Pallas Field Laws" do
  it "satisfies Eq laws" $ liftEffect $
    Laws.checkEq prxTestPallas

  it "satisfies Semiring laws" $ liftEffect $
    Laws.checkSemiring prxTestPallas

  it "satisfies Ring laws" $ liftEffect $
    Laws.checkRing prxTestPallas

  it "satisfies CommutativeRing laws" $ liftEffect $
    Laws.checkCommutativeRing prxTestPallas

  it "satisfies EuclideanRing laws" $ liftEffect $
    Laws.checkEuclideanRing prxTestPallas

  it "satisfies DivisionRing laws" $ liftEffect $
    Laws.checkDivisionRing prxTestPallas

  bigIntHomomorphismSpec "Pallas" Pallas.fromBigInt zero one

  where
  prxTestPallas = Proxy :: Proxy ScalarField