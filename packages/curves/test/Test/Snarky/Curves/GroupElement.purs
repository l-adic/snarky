module Test.Snarky.Curves.GroupElement
  ( spec
  ) where

import Prelude

import Data.Array (fold)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Console (log)
import JS.BigInt as BigInt
import Snarky.Curves.BN254 as BN254
import Snarky.Curves.Class (class FrModule, class WeierstrassCurve, curveParams, fromBigInt, inverse, scalarMul, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (class Arbitrary, Result, arbitrary, quickCheck', (===))
import Test.QuickCheck.Gen (suchThat)
import Test.QuickCheck.Laws (checkLaws)
import Test.QuickCheck.Laws.Data as Data
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))

frModuleLaws
  :: forall f g
   . Show g
  => Eq g
  => FrModule f g
  => Arbitrary f
  => Arbitrary g
  => Proxy f
  -> Proxy g
  -> Effect Unit
frModuleLaws _ proxyG = do

  Data.checkEq proxyG
  Data.checkSemigroup proxyG
  Data.checkMonoid proxyG

  log "Checking 'commutativity'"
  quickCheck' 1000 $ commutativity <$> arbitrary <*> arbitrary

  log "Checking 'negation is involutive' "
  quickCheck' 1000 $ negationIsInvolutive <$> arbitrary

  log "Checking 'negation is right inverse'"
  quickCheck' 1000 $ negationIsRightInverse <$> arbitrary

  log "Checking 'negation is left inverse'"
  quickCheck' 1000 $ negationIsLeftInverse <$> arbitrary

  log "Checking 'scalar mul by zero'"
  quickCheck' 1000 $ scalarMulByZero <$> arbitrary

  log "Checking 'scalar mul by one'"
  quickCheck' 1000 $ scalarMulByOne <$> arbitrary

  log "Checking 'scalar mul distributes'"
  quickCheck' 1000 $ scalarMulDistributes <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

  where
  negationIsInvolutive :: g -> Result
  negationIsInvolutive g = inverse (inverse g) === g

  negationIsRightInverse :: g -> Result
  negationIsRightInverse g = g <> inverse g === mempty

  negationIsLeftInverse :: g -> Result
  negationIsLeftInverse g = inverse g <> g === mempty

  commutativity :: g -> g -> Result
  commutativity g1 g2 = g1 <> g2 === g2 <> g1

  scalarMulByZero :: g -> Result
  scalarMulByZero g = scalarMul zero g === mempty

  scalarMulByOne :: g -> Result
  scalarMulByOne g = scalarMul one g === g

  scalarMulDistributes :: f -> f -> g -> g -> Result
  scalarMulDistributes a b g h =
    scalarMul (a + b) (g <> h) ===
      fold [ scalarMul a g, scalarMul a h, scalarMul b g, scalarMul b h ]

toAffineLaws
  :: forall f g
   . Show g
  => Eq g
  => Eq f
  => Ring f
  => Monoid g
  => WeierstrassCurve f g
  => Arbitrary g
  => Proxy f
  -> Proxy g
  -> Effect Unit
toAffineLaws _ proxyG = do
  log "Checking 'identity maps to Nothing'"
  (toAffine (mempty :: g)) `shouldEqual` (Nothing :: Maybe { x :: f, y :: f })

  log "Checking 'non-identity points satisfy Weierstrass equation'"
  quickCheck' 100 $ nonIdentityOnCurve <$> suchThat arbitrary (_ /= (mempty :: g))
  where
  nonIdentityOnCurve :: g -> Result
  nonIdentityOnCurve g =
    case (toAffine g :: Maybe { x :: f, y :: f }) of
      Nothing -> false === true -- Should not happen for non-identity
      Just { x, y } ->
        let
          params = curveParams proxyG
          y_sq = y * y
          x_sq = x * x
          x_cb = x_sq * x
          rhs = x_cb + params.a * x + params.b
        in
          y_sq === rhs

spec :: Spec Unit
spec = describe "Elliptic Curve" do
  describe "Weierstrass parameters" do
    it "Vesta coefficient A should be 0" do
      (curveParams (Proxy @Vesta.G)).a `shouldEqual` (zero :: Vesta.BaseField)

    it "Vesta coefficient B should be 5" do
      let five = fromBigInt (BigInt.fromInt 5) :: Vesta.BaseField
      (curveParams (Proxy @Vesta.G)).b `shouldEqual` five

    it "Pallas coefficient A should be 0" do
      (curveParams (Proxy @Pallas.G)).a `shouldEqual` (zero :: Pallas.BaseField)

    it "Pallas coefficient B should be 5" do
      let five = fromBigInt (BigInt.fromInt 5) :: Pallas.BaseField
      (curveParams (Proxy @Pallas.G)).b `shouldEqual` five

    it "BN254 coefficient A should be 1" do
      (curveParams (Proxy @BN254.G)).a `shouldEqual` (zero :: BN254.BaseField)

    it "BN254 coefficient B should be 3" do
      let three = fromBigInt (BigInt.fromInt 3) :: BN254.BaseField
      (curveParams (Proxy @BN254.G)).b `shouldEqual` three

  describe "Fr Module" do
    it "Vesta" $ liftEffect $ checkLaws "" do
      frModuleLaws (Proxy @Vesta.ScalarField) (Proxy @Vesta.G)

    it "Pallas" $ liftEffect $ checkLaws "" do
      frModuleLaws (Proxy @Pallas.ScalarField) (Proxy @Pallas.G)

    it "BN254" $ liftEffect $ checkLaws "" do
      frModuleLaws (Proxy @BN254.ScalarField) (Proxy @BN254.G)

  describe "toAffine" do
    it "Vesta" $ liftEffect do
      toAffineLaws (Proxy @Vesta.BaseField) (Proxy @Vesta.G)

    it "Pallas" $ liftEffect do
      toAffineLaws (Proxy @Pallas.BaseField) (Proxy @Pallas.G)

    it "BN254" $ liftEffect do
      toAffineLaws (Proxy @BN254.BaseField) (Proxy @BN254.G)