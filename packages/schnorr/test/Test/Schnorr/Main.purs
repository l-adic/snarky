module Test.Schnorr.Main where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Schnorr (Signature(..))
import Data.Schnorr as Schnorr
import Effect (Effect)
import Snarky.Curves.Pasta (PallasBaseField, PallasG, PallasScalarField)
import Snarky.Curves.Class (fromAffine, fromBigInt, generator, inverse, scalarMul, toAffine, toBigInt)
import Poseidon as Poseidon
import Test.QuickCheck (Result(..), withHelp)
import Test.Spec.QuickCheck (quickCheck)
import Test.Spec (Spec, describe, it)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

-- | For Pallas curve:
-- | - Base field = PallasBaseField (= VestaScalarField)
-- | - Scalar field = PallasScalarField
-- | So Signature type is: Signature PallasBaseField PallasScalarField
type PallasSignature = Schnorr.Signature PallasBaseField PallasScalarField

-- | Get Pallas generator
pallasGen :: PallasG
pallasGen = generator

-- | Helper to sign with Pallas curve.
-- | We inline the implementation to avoid ambiguous type issues.
signPallas :: PallasScalarField -> Array PallasBaseField -> Maybe PallasSignature
signPallas privateKey message = do
  -- Compute public key: pk = d * G (using PallasG explicitly)
  publicKey <- toAffine $ scalarMul privateKey (pallasGen :: PallasG)

  -- Derive nonce deterministically using Poseidon hash (in base field)
  let
    msgHash = Poseidon.hash message
    kPrimeBase :: PallasBaseField
    kPrimeBase = Poseidon.hash [ publicKey.x, publicKey.y, msgHash ]
    -- Convert to scalar field via BigInt
    kPrime :: PallasScalarField
    kPrime = fromBigInt (toBigInt kPrimeBase)

  -- Guard against zero nonce
  if kPrime == zero then Nothing
  else do
    -- Compute R = k' * G
    { x: r, y: ry } <- toAffine $ scalarMul kPrime (pallasGen :: PallasG)

    -- Normalize k based on y parity
    let k = if Schnorr.isEven ry then kPrime else negate kPrime

    -- Compute challenge hash (in base field)
    let eBase :: PallasBaseField
        eBase = Schnorr.hashMessage publicKey r message
        -- Convert to scalar field via BigInt
        e :: PallasScalarField
        e = fromBigInt (toBigInt eBase)

    -- Compute s = k + e * d (all in scalar field)
    let s = k + e * privateKey

    pure $ Signature { r, s }

-- | Helper to verify with Pallas curve.
verifyPallas :: PallasSignature -> { x :: PallasBaseField, y :: PallasBaseField } -> Array PallasBaseField -> Boolean
verifyPallas (Signature { r, s }) publicKey message =
  let
    -- Compute challenge hash (in base field)
    eBase :: PallasBaseField
    eBase = Schnorr.hashMessage publicKey r message
    -- Convert to scalar field via BigInt
    e :: PallasScalarField
    e = fromBigInt (toBigInt eBase)

    -- Reconstruct the public key point
    pkPoint :: PallasG
    pkPoint = fromAffine publicKey

    -- Compute R' = s*G - e*pk (using scalar field values)
    sG = scalarMul s (pallasGen :: PallasG)
    ePk = scalarMul e pkPoint
    rPoint = sG <> inverse ePk
  in
    case toAffine rPoint of
      Nothing -> false
      Just { x: rx, y: ry } -> Schnorr.isEven ry && rx == r

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  pureSpec

-- | Pure (non-circuit) tests for Schnorr signatures using Pallas curve.
pureSpec :: Spec Unit
pureSpec = describe "Data.Schnorr (Pallas curve)" do

  it "sign produces valid signatures" do
    quickCheck signProducesValidSignature

  it "verify rejects invalid signatures (wrong message)" do
    quickCheck verifyRejectsWrongMessage

  it "verify rejects invalid signatures (wrong public key)" do
    quickCheck verifyRejectsWrongPublicKey

  it "verify rejects invalid signatures (tampered r)" do
    quickCheck verifyRejectsTamperedR

  it "verify rejects invalid signatures (tampered s)" do
    quickCheck verifyRejectsTamperedS

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
      if s == tamperedS then Success -- Skip if s is the same
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
