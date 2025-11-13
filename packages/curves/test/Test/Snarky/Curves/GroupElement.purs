module Test.Snarky.Curves.GroupElement where

import Prelude

import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Snarky.Curves.Class (curveParams, fromBigInt, inverse, scalarMul)
import Snarky.Curves.Vesta (BaseField, G, ScalarField)
import Test.QuickCheck (quickCheck, (===))
import Test.QuickCheck.Laws (checkLaws)
import Test.QuickCheck.Laws.Data as Data
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))

spec :: Spec Unit
spec = describe "Vesta GroupElement" do
  describe "Weierstrass parameters" do
    it "coefficient A should be 0" do
      (curveParams (Proxy @G)).a `shouldEqual` (zero :: BaseField)

    it "coefficient B should be 5" do
      let five = fromBigInt (BigInt.fromInt 5) :: BaseField
      (curveParams (Proxy @G)).b `shouldEqual` five

  describe "Group operations" do
    it "satisfies type class laws" $ liftEffect $ checkLaws "GroupElement" do
      Data.checkEq (Proxy :: Proxy G)
      Data.checkSemigroup (Proxy :: Proxy G)
      Data.checkMonoid (Proxy :: Proxy G)

    it "negation is involutive" $ liftEffect $ quickCheck \(g :: G) ->
      inverse (inverse g) === g

    it "negation gives additive inverse" $ liftEffect $ quickCheck \(g :: G) ->
      (g <> inverse g) === mempty

    it "scalar multiplication by zero gives identity" $ liftEffect $ quickCheck \(g :: G) ->
      scalarMul (zero :: ScalarField) g === mempty

    it "scalar multiplication by one is identity" $ liftEffect $ quickCheck \(g :: G) ->
      scalarMul (one :: ScalarField) g === g

    it "scalar multiplication distributes over group addition" $ liftEffect $ quickCheck \(g1 :: G) (g2 :: G) (s :: ScalarField) ->
      scalarMul s (g1 <> g2) === (scalarMul s g1 <> scalarMul s g2)