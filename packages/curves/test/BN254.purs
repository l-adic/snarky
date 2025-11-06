module Test.BN254 where

import Prelude

import Effect.Class (liftEffect)
import Snarky.Curves.BN254 (ScalarField)
import Test.QuickCheck.Laws.Data as Laws
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec :: Spec Unit
spec = describe "BN254 Field Laws" do
  it "satisfies Eq laws" $ liftEffect $
    Laws.checkEq prxTestBN254

  it "satisfies Semiring laws" $ liftEffect $
    Laws.checkSemiring prxTestBN254

  it "satisfies Ring laws" $ liftEffect $
    Laws.checkRing prxTestBN254

  it "satisfies CommutativeRing laws" $ liftEffect $
    Laws.checkCommutativeRing prxTestBN254

  it "satisfies EuclideanRing laws" $ liftEffect $
    Laws.checkEuclideanRing prxTestBN254

  it "satisfies DivisionRing laws" $ liftEffect $
    Laws.checkDivisionRing prxTestBN254
  where
  prxTestBN254 = Proxy :: Proxy ScalarField