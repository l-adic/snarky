-- | Pure Schnorr signature implementation.
-- |
-- | This module provides the pure (non-circuit) implementation of
-- | Schnorr signatures over elliptic curves with Poseidon hash.
-- |
-- | For Pasta curves, the base field and scalar field are different,
-- | so this implementation uses separate type parameters for each:
-- | - fb: base field (for coordinates and message hashing)
-- | - fs: scalar field (for private keys and scalar s)
module Data.Schnorr
  ( Signature(..)
  , sign
  , verify
  , isEven
  , hashMessage
  , safeFieldCoerce
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

-- | Safe coercion between 255-bit fields via bit truncation.
-- | Truncates to 254 bits to ensure the value is < 2^254, which is guaranteed
-- | to fit in both Pasta field primes without modular reduction.
-- | This matches Mina's approach for nonce derivation.
safeFieldCoerce
  :: forall f f'
   . PrimeField f
  => PrimeField f'
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => f
  -> f'
safeFieldCoerce x =
  let
    bits = unpackPure x -- Vector 255 Boolean, LSB first
    truncated = Vector.take @254 bits -- Vector 254 Boolean (lower 254 bits)
    padded = Vector.snoc truncated false -- Vector 255 Boolean with MSB = 0
  in
    packPure padded

-- | Schnorr signature: (r, s) where:
-- | - r is an x-coordinate (base field element)
-- | - s is the scalar component (scalar field element)
-- |
-- | For Pasta curves: Signature PallasBaseField PallasScalarField
newtype Signature fb fs = Signature
  { r :: fb -- x-coordinate (base field)
  , s :: fs -- scalar component (scalar field)
  }

derive instance Newtype (Signature fb fs) _
derive instance Generic (Signature fb fs) _
derive newtype instance (Show fb, Show fs) => Show (Signature fb fs)
derive newtype instance (Eq fb, Eq fs) => Eq (Signature fb fs)

-- | Check if a field element is even (LSB is 0).
-- | In the Schnorr scheme, we use this to normalize the nonce.
isEven :: forall f. PrimeField f => f -> Boolean
isEven x = not $ BigInt.odd (toBigInt x)

-- | Hash the message for signature verification.
-- |
-- | e = H(pk_x, pk_y, r, H(message))
-- |
-- | where (pk_x, pk_y) is the public key and r is the signature's r component.
-- | All inputs and outputs are in the base field.
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
-- | 2. Derive nonce: k' = H(pk_x, pk_y, H(message)) truncated to 254 bits
-- | 3. Compute R = [k'] * G
-- | 4. r = x-coordinate of R
-- | 5. If y-coordinate of R is odd, k = -k', else k = k'
-- | 6. e = H(pk_x, pk_y, r, H(message)) (in base field, coerced to scalar)
-- | 7. s = k + e * d (in scalar field)
-- | 8. Return (r, s)
-- |
-- | Note: The nonce is truncated to 254 bits to ensure it fits in both Pasta
-- | field primes without modular reduction, matching Mina's approach.
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
  -- Compute public key: pk = d * G
  publicKey <- toAffine $ scalarMul privateKey (generator @_ @g)

  -- Derive nonce deterministically using Poseidon hash (in base field)
  -- k' = H(pk_x, pk_y, H(message))
  let
    kPrimeBase :: fb
    kPrimeBase = Poseidon.hash $ publicKey.x : publicKey.y : message

    -- Convert base field to scalar field via bit truncation (254 bits)
    -- This ensures the value fits in both fields without modular reduction,
    -- matching Mina's approach for nonce derivation.
    kPrime :: fs
    kPrime = safeFieldCoerce kPrimeBase

  -- Guard against zero nonce
  if kPrime == zero then Nothing
  else do
    -- Compute R = k' * G
    { x: r, y: ry } <- toAffine $ scalarMul kPrime (generator @_ @g)

    -- Normalize k based on y parity (BIP-340 style)
    let k = if isEven ry then kPrime else negate kPrime

    -- Compute challenge hash: e = H(pk_x, pk_y, r, H(message)) (in base field)
    let
      eBase :: fb
      eBase = hashMessage publicKey r message

      -- Convert to scalar field via BigInt for arithmetic
      e :: fs
      e = fromBigInt (toBigInt eBase)

    -- Compute s = k + e * d (in scalar field)
    let s = k + e * privateKey

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
    -- Compute challenge hash: e = H(pk_x, pk_y, r, H(message)) (in base field)
    eBase :: fb
    eBase = hashMessage publicKey r message

    -- Convert to scalar field via BigInt
    e :: fs
    e = fromBigInt (toBigInt eBase)

    -- Reconstruct the public key point from affine coordinates
    pkPoint :: g
    pkPoint = fromAffine publicKey

    -- Compute R' = s*G - e*pk = s*G + (-e)*pk
    sG = scalarMul s generator
    ePk = scalarMul e pkPoint
    rPoint = sG <> inverse ePk
  in
    case toAffine rPoint of
      Nothing -> false
      Just { x: rx, y: ry } -> isEven ry && rx == r
