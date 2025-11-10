module Test.Snarky.Curves.Field where

import Prelude

import Effect.Class (liftEffect)
import Snarky.Curves.Types (class PrimeField)
import Test.Snarky.Curves.BigInt (bigIntHomomorphismSpec)
import Test.QuickCheck (class Arbitrary)
import Test.QuickCheck.Laws.Data as Laws
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy)

spec :: forall f. Arbitrary f => PrimeField f => Proxy f -> Spec Unit
spec proxy = describe "Pallas Field Laws" do
  it "satisfies Eq laws" $ liftEffect $
    Laws.checkEq proxy

  it "satisfies Semiring laws" $ liftEffect $
    Laws.checkSemiring proxy

  it "satisfies Ring laws" $ liftEffect $
    Laws.checkRing proxy

  it "satisfies CommutativeRing laws" $ liftEffect $
    Laws.checkCommutativeRing proxy

  it "satisfies EuclideanRing laws" $ liftEffect $
    Laws.checkEuclideanRing proxy

  it "satisfies DivisionRing laws" $ liftEffect $
    Laws.checkDivisionRing proxy

  bigIntHomomorphismSpec proxy