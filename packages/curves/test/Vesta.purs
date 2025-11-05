module Test.Vesta where

import Prelude

import Effect.Class (liftEffect)
import Test.Spec (Spec, describe, it)
import Test.QuickCheck.Laws.Data as Laws
import Type.Proxy (Proxy(..))

import Snarky.Curves.Vesta (ScalarField)

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
  where
    prxTestVesta = Proxy :: Proxy ScalarField