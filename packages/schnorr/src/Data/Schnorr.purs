-- | Pure Schnorr signature implementation.
-- |
-- | This module provides the pure (non-circuit) implementation of
-- | Schnorr signatures over elliptic curves with Poseidon hash.
-- |
-- | The base field and scalar field are different,
-- | so this implementation uses separate type parameters for each:
-- | - fb: base field (for coordinates and message hashing)
-- | - fs: scalar field (for private keys and scalar s)
module Data.Schnorr
  ( Signature(..)
  , sign
  , verify
  , isEven
  , hashMessage
  , truncateFieldCoerce
  ) where

import Prelude

import Data.Array ((:))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Vector as Vector
import JS.BigInt as BigInt
import Poseidon (class PoseidonField)
import Poseidon as Poseidon
import Snarky.Circuit.DSL.Bits (packPure, unpackPure)
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class PrimeField, class WeierstrassCurve, fromAffine, fromBigInt, generator, inverse, scalarMul, toAffine, toBigInt)

-- | Truncating coercion between 255-bit fields.
-- | WARNING: This truncates to 254 bits, discarding the MSB. For values >= 2^254,
-- | the result will differ from the input. Only use when:
-- | - You know the value is < 2^254, or
-- | - You don't care about truncation (e.g., nonce derivation where any 254-bit value works)
truncateFieldCoerce
  :: forall f f'
   . PrimeField f
  => PrimeField f'
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => f
  -> f'
truncateFieldCoerce x =
  let
    bits = unpackPure x -- Vector 255 Boolean, LSB first
    truncated = Vector.take @254 bits -- Vector 254 Boolean (lower 254 bits)
    padded = Vector.snoc truncated false -- Vector 255 Boolean with MSB = 0
  in
    packPure padded

-- | Schnorr signature: (r, s) where:
-- | - r is an x-coordinate (base field element)
-- | - s is the scalar component (scalar field element)
newtype Signature fb fs = Signature
  { r :: fb
  , s :: fs
  }

derive instance Newtype (Signature fb fs) _
derive instance Generic (Signature fb fs) _
derive newtype instance (Show fb, Show fs) => Show (Signature fb fs)
derive newtype instance (Eq fb, Eq fs) => Eq (Signature fb fs)

-- | Check if a field element is even (LSB is 0).
isEven :: forall f. PrimeField f => f -> Boolean
isEven x = not $ BigInt.odd (toBigInt x)

-- | Hash the message for signature verification.
-- |
-- | e = H(pk_x, pk_y, r, message)
-- | where (pk_x, pk_y) is the public key and r is the signature's r component.
hashMessage
  :: forall fb
   . PoseidonField fb
  => { x :: fb, y :: fb }
  -> fb
  -> Array fb
  -> fb
hashMessage { x: px, y: py } r message =
  Poseidon.hash $ px : py : r : message

-- | Sign a message with a private key.
-- |
-- | Algorithm:
-- | 1. Compute public key: pk = [d] * G
-- | 2. Derive nonce: k' = H(pk_x, pk_y, message) truncated to 254 bits
-- | 3. Compute R = [k'] * G
-- | 4. r = x-coordinate of R
-- | 5. If y-coordinate of R is odd, k = -k', else k = k'
-- | 6. e = H(pk_x, pk_y, r, message) (in base field, coerced to scalar)
-- | 7. s = k + e * d (in scalar field)
-- | 8. Return (r, s)
-- |
-- | Note: The nonce is truncated to 254 bits to ensure it fits in both Pasta
-- | field primes without modular reduction.
sign
  :: forall fb fs g
   . PoseidonField fb
  => PrimeField fb
  => PrimeField fs
  => FieldSizeInBits fb 255
  => FieldSizeInBits fs 255
  => WeierstrassCurve fb g
  => FrModule fs g
  => fs
  -> Array fb
  -> Maybe (Signature fb fs)
sign privateKey message = do
  publicKey <- toAffine $ scalarMul privateKey (generator @_ @g)
  let
    -- Convert base field to scalar field via bit truncation (254 bits)
    -- This ensures the value fits in both fields without modular reduction.
    kPrime =
      let
        kPrimeBase = Poseidon.hash $ publicKey.x : publicKey.y : message
      in
        truncateFieldCoerce kPrimeBase

  if kPrime == zero then Nothing
  else do
    { x: r, y: ry } <- toAffine $ scalarMul kPrime (generator @_ @g)
    let
      k = if isEven ry then kPrime else negate kPrime

      e =
        let
          eBase = hashMessage publicKey r message
        in
          fromBigInt (toBigInt eBase)
      s = k + e * privateKey
    pure $ Signature { r, s }

-- | Verify a Schnorr signature.
-- |
-- | Algorithm:
-- | 1. e = H(pk_x, pk_y, r, H(message))
-- | 2. R' = [s] * G - [e] * pk
-- | 3. Return: y-coordinate of R' is even AND x-coordinate of R' == r
verify
  :: forall fb fs g
   . PoseidonField fb
  => PrimeField fb
  => PrimeField fs
  => WeierstrassCurve fb g
  => FrModule fs g
  => Signature fb fs
  -> { x :: fb, y :: fb }
  -> Array fb
  -> Boolean
verify (Signature { r, s }) publicKey message =
  let
    e =
      let
        eBase = hashMessage publicKey r message
      in
        fromBigInt (toBigInt eBase)

    pkPoint :: g
    pkPoint = fromAffine publicKey

    sG = scalarMul s generator
    ePk = scalarMul e pkPoint
    rPoint = sG <> inverse ePk
  in
    case toAffine rPoint of
      Nothing -> false
      Just { x: rx, y: ry } -> isEven ry && rx == r
