module Test.Vesta where

import Prelude

import Effect.Class (liftEffect)
import Snarky.Curves.Vesta (ScalarField)
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (quickCheck)
import Test.QuickCheck.Laws.Data as Laws
import Test.Spec (Spec, describe, it)
import Test.BigInt (bigIntHomomorphismSpec)
import Type.Proxy (Proxy(..))

spec :: Spec Unit
spec = describe "Vesta Field Laws" do
  it "satisfies Eq laws" $ liftEffect $
    Laws.checkEq prxTestVesta

  it "satisfies Semiring laws" $ liftEffect $
    Laws.checkSemiring prxTestVesta

  it "satisfies Ring laws" $ liftEffect $
    Laws.checkRing prxTestVesta

  it "satisfies CommutativeRing laws" $ liftEffect $
    Laws.checkCommutativeRing prxTestVesta

  it "satisfies EuclideanRing laws" $ liftEffect $
    Laws.checkEuclideanRing prxTestVesta

  it "satisfies DivisionRing laws" $ liftEffect $
    Laws.checkDivisionRing prxTestVesta

  bigIntHomomorphismSpec "Vesta" Vesta.fromBigInt zero one

  where
  prxTestVesta = Proxy :: Proxy ScalarField