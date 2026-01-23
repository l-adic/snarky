module Test.Data.Schnorr
  ( spec
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Schnorr (Signature(..))
import Data.Schnorr as Schnorr
import Effect.Class (liftEffect)
import Poseidon as Poseidon
import Snarky.Curves.Class (fromAffine, fromBigInt, generator, inverse, scalarMul, toAffine, toBigInt)
import Snarky.Curves.Pasta (PallasBaseField, PallasG, PallasScalarField)
import Test.QuickCheck (Result(..), quickCheck, withHelp)
import Test.Spec (Spec, describe, it)

type PallasSignature = Schnorr.Signature PallasBaseField PallasScalarField

pallasGen :: PallasG
pallasGen = generator

signPallas :: PallasScalarField -> Array PallasBaseField -> Maybe PallasSignature
signPallas privateKey message = do
  publicKey <- toAffine $ scalarMul privateKey (pallasGen :: PallasG)
  let
    msgHash = Poseidon.hash message

    kPrime :: PallasScalarField
    kPrime =
      let
        kPrimeBase = Poseidon.hash [ publicKey.x, publicKey.y, msgHash ]
      in
        fromBigInt (toBigInt kPrimeBase)

  if kPrime == zero then Nothing
  else do
    { x: r, y: ry } <- toAffine $ scalarMul kPrime (pallasGen :: PallasG)
    let
      k = if Schnorr.isEven ry then kPrime else negate kPrime
      e =
        let
          eBase = Schnorr.hashMessage publicKey r message
        in
          fromBigInt (toBigInt eBase)
      s = k + e * privateKey
    pure $ Signature { r, s }

verifyPallas :: PallasSignature -> { x :: PallasBaseField, y :: PallasBaseField } -> Array PallasBaseField -> Boolean
verifyPallas (Signature { r, s }) publicKey message =
  let
    e :: PallasScalarField
    e =
      let
        eBase = Schnorr.hashMessage publicKey r message
      in
        fromBigInt (toBigInt eBase)

    pkPoint :: PallasG
    pkPoint = fromAffine publicKey
    sG = scalarMul s (pallasGen :: PallasG)
    ePk = scalarMul e pkPoint
    rPoint = sG <> inverse ePk
  in
    case toAffine rPoint of
      Nothing -> false
      Just { x: rx, y: ry } -> Schnorr.isEven ry && rx == r

spec :: Spec Unit
spec = describe "Data.Schnorr (Pallas curve)" do

  it "sign produces valid signatures" do
    liftEffect $ quickCheck signProducesValidSignature

  it "verify rejects invalid signatures (wrong message)" do
    liftEffect $ quickCheck verifyRejectsWrongMessage

  it "verify rejects invalid signatures (wrong public key)" do
    liftEffect $ quickCheck verifyRejectsWrongPublicKey

  it "verify rejects invalid signatures (tampered r)" do
    liftEffect $ quickCheck verifyRejectsTamperedR

  it "verify rejects invalid signatures (tampered s)" do
    liftEffect $ quickCheck verifyRejectsTamperedS

-- | Test that signing a message produces a signature that verifies
signProducesValidSignature :: PallasScalarField -> PallasBaseField -> Result
signProducesValidSignature privateKey msgField =
  case signPallas privateKey [ msgField ] of
    Nothing -> withHelp false "Failed to create signature (zero nonce?)"
    Just sig ->
      let
        pkPoint = scalarMul privateKey pallasGen
      in
        case toAffine pkPoint of
          Nothing -> withHelp false "Failed to compute public key"
          Just publicKey ->
            withHelp
              (verifyPallas sig publicKey [ msgField ])
              "Signature should verify"

-- | Test that verification fails with a different message
verifyRejectsWrongMessage :: PallasScalarField -> PallasBaseField -> PallasBaseField -> Result
verifyRejectsWrongMessage privateKey msg1 msg2 =
  if msg1 == msg2 then Success -- Skip if messages are the same
  else
    case signPallas privateKey [ msg1 ] of
      Nothing -> withHelp false "Failed to create signature"
      Just sig ->
        let
          pkPoint = scalarMul privateKey pallasGen
        in
          case toAffine pkPoint of
            Nothing -> withHelp false "Failed to compute public key"
            Just publicKey ->
              withHelp
                (not $ verifyPallas sig publicKey [ msg2 ])
                "Signature should NOT verify with different message"

-- | Test that verification fails with a different public key
verifyRejectsWrongPublicKey :: PallasScalarField -> PallasScalarField -> PallasBaseField -> Result
verifyRejectsWrongPublicKey privateKey1 privateKey2 msgField =
  if privateKey1 == privateKey2 then Success -- Skip if keys are the same
  else
    case signPallas privateKey1 [ msgField ] of
      Nothing -> withHelp false "Failed to create signature"
      Just sig ->
        let
          wrongPkPoint = scalarMul privateKey2 pallasGen
        in
          case toAffine wrongPkPoint of
            Nothing -> withHelp false "Failed to compute wrong public key"
            Just wrongPublicKey ->
              withHelp
                (not $ verifyPallas sig wrongPublicKey [ msgField ])
                "Signature should NOT verify with wrong public key"

-- | Test that verification fails when r is tampered
verifyRejectsTamperedR :: PallasScalarField -> PallasBaseField -> PallasBaseField -> Result
verifyRejectsTamperedR privateKey msgField tamperedR =
  case signPallas privateKey [ msgField ] of
    Nothing -> withHelp false "Failed to create signature"
    Just (Signature { r, s }) ->
      if r == tamperedR then Success -- Skip if r is the same
      else
        let
          pkPoint = scalarMul privateKey pallasGen
          tamperedSig = Signature { r: tamperedR, s }
        in
          case toAffine pkPoint of
            Nothing -> withHelp false "Failed to compute public key"
            Just publicKey ->
              withHelp
                (not $ verifyPallas tamperedSig publicKey [ msgField ])
                "Signature should NOT verify with tampered r"

-- | Test that verification fails when s is tampered
verifyRejectsTamperedS :: PallasScalarField -> PallasBaseField -> PallasScalarField -> Result
verifyRejectsTamperedS privateKey msgField tamperedS =
  case signPallas privateKey [ msgField ] of
    Nothing -> withHelp false "Failed to create signature"
    Just (Signature { r, s }) ->
      if s == tamperedS then Success
      else
        let
          pkPoint = scalarMul privateKey pallasGen
          tamperedSig = Signature { r, s: tamperedS }
        in
          case toAffine pkPoint of
            Nothing -> withHelp false "Failed to compute public key"
            Just publicKey ->
              withHelp
                (not $ verifyPallas tamperedSig publicKey [ msgField ])
                "Signature should NOT verify with tampered s"
