module Test.Data.Schnorr
  ( spec
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromJust)
import Data.Schnorr (Signature(..))
import Data.Schnorr as Schnorr
import Data.Schnorr.ChainId (ChainId(..), signaturePrefix)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import Snarky.Curves.Class (generator, scalarMul, toAffine)
import Snarky.Curves.Pasta (PallasBaseField, PallasG, PallasScalarField)
import Test.QuickCheck (arbitrary, quickCheckGen, withHelp)
import Test.QuickCheck.Gen (Gen, suchThat)
import Test.Spec (Spec, describe, it)

-- | A QuickCheck-friendly sign that rotates nonces until acceptance.
-- |
-- | The new circuit-matching `Data.Schnorr.sign` rejection-samples
-- | (`ry` even, `e < 2^254`, `s < 2^254`). Tests need a deterministic
-- | "always-success" sign for the round-trip property — this generator
-- | composes the raw sign with QuickCheck's `suchThat` so the inner
-- | generator only emits succeeding `(privateKey, nonce)` triples.
type SignAndKey =
  { privateKey :: PallasScalarField
  , signature :: Schnorr.Signature PallasBaseField
  , publicKey :: { x :: PallasBaseField, y :: PallasBaseField }
  }

genSignedMessage :: Array PallasBaseField -> Gen SignAndKey
genSignedMessage message =
  let
    tryOne = do
      privateKey :: PallasScalarField <- arbitrary
      nonce :: PallasScalarField <- arbitrary
      pure
        { privateKey
        , nonce
        , maybeSig: Schnorr.sign
            { spongePrefix: signaturePrefix Mainnet, privateKey, nonce, message }
        }
  in
    do
      { privateKey, maybeSig } <- tryOne `suchThat` \r -> case r.maybeSig of
        Just _ -> true
        Nothing -> false
      let
        signature = unsafePartial fromJust maybeSig
        publicKey = unsafePartial fromJust $ toAffine
          (scalarMul privateKey (generator :: PallasG))
      pure { privateKey, signature, publicKey }

spec :: Spec Unit
spec = describe "Data.Schnorr (Pallas curve, kimchi-circuit convention)" do

  it "sign produces valid signatures" do
    liftEffect $ quickCheckGen do
      msg :: PallasBaseField <- arbitrary
      { signature, publicKey } <- genSignedMessage [ msg ]
      pure $ withHelp
        (Schnorr.verify (signaturePrefix Mainnet) signature publicKey [ msg ])
        "Signature should verify"

  it "verify rejects wrong message" do
    liftEffect $ quickCheckGen do
      msg1 :: PallasBaseField <- arbitrary
      msg2 :: PallasBaseField <- arbitrary `suchThat` (_ /= msg1)
      { signature, publicKey } <- genSignedMessage [ msg1 ]
      pure $ withHelp
        (not $ Schnorr.verify (signaturePrefix Mainnet) signature publicKey [ msg2 ])
        "Signature should NOT verify with different message"

  it "verify rejects wrong public key" do
    liftEffect $ quickCheckGen do
      msg :: PallasBaseField <- arbitrary
      { signature, privateKey } <- genSignedMessage [ msg ]
      wrongSk :: PallasScalarField <- arbitrary `suchThat` (_ /= privateKey)
      let
        wrongPk = unsafePartial fromJust $ toAffine
          (scalarMul wrongSk (generator :: PallasG))
      pure $ withHelp
        (not $ Schnorr.verify (signaturePrefix Mainnet) signature wrongPk [ msg ])
        "Signature should NOT verify with wrong public key"

  it "verify rejects tampered r" do
    liftEffect $ quickCheckGen do
      msg :: PallasBaseField <- arbitrary
      { signature: Signature { r, s }, publicKey } <- genSignedMessage [ msg ]
      tamperedR :: PallasBaseField <- arbitrary `suchThat` (_ /= r)
      pure $ withHelp
        (not $ Schnorr.verify (signaturePrefix Mainnet) (Signature { r: tamperedR, s }) publicKey [ msg ])
        "Signature should NOT verify with tampered r"

  it "verify rejects tampered s" do
    liftEffect $ quickCheckGen do
      msg :: PallasBaseField <- arbitrary
      { signature: Signature { r, s }, publicKey } <- genSignedMessage [ msg ]
      tamperedS :: PallasBaseField <- arbitrary `suchThat` (_ /= s)
      pure $ withHelp
        (not $ Schnorr.verify (signaturePrefix Mainnet) (Signature { r, s: tamperedS }) publicKey [ msg ])
        "Signature should NOT verify with tampered s"
