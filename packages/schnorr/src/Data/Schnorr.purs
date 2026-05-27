-- | Out-of-circuit Schnorr signature signer/verifier matching the
-- | kimchi-circuit verifier in `Snarky.Circuit.Schnorr.verifies`.
-- |
-- | Both `r` and `s` live in `Pallas.BaseField` (= `Vesta.ScalarField`,
-- | the native circuit field), not in the curve's scalar field. The
-- | verifier interprets `(s + 2^255)` and `(e + 2^255)` as Pallas
-- | scalars and computes `R' = [s+2^255]·G − [e+2^255]·pk`. The signer
-- | solves the matching equation modulo the Pallas scalar order, then
-- | rejects samples where `s` or `e` would overflow the circuit's
-- | top-bit-zero constraint (`< 2^254`) or where the nonce produces an
-- | odd `R.y`.
-- |
-- | Reference: `mina/src/lib/crypto/pickles/dump_circuit_impl.ml`
-- | `schnorr_verify_circuit`, plus `Ops.scale_fast2'` semantics in
-- | `plonk_curve_ops.ml` (`actual_bits_used = 255` ⇒ `2^255` shift).
module Data.Schnorr
  ( Signature(..)
  , isEven
  , hashMessage
  , sign
  , verify
  , twoTo254
  , twoTo255Pallas
  ) where

import Prelude

import Data.Array ((:))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import JS.BigInt (BigInt)
import JS.BigInt as BigInt
import Poseidon as Poseidon
import Snarky.Curves.Class (fromAffine, fromBigInt, generator, inverse, scalarMul, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG)

-- | Schnorr signature: both components are circuit-field values
-- | (`Pallas.BaseField`).
-- |
-- |   - `r` is the x-coordinate of the commitment point `R = k·G`.
-- |   - `s` is a 254-bit value such that `(s + 2^255)·G = R + (e + 2^255)·pk`
-- |     in the Pallas scalar field, where `e = Poseidon(pk.x, pk.y, r, msg)`.
newtype Signature f = Signature
  { r :: f
  , s :: f
  }

derive instance Newtype (Signature f) _
derive instance Generic (Signature f) _
derive newtype instance Show f => Show (Signature f)
derive newtype instance Eq f => Eq (Signature f)

-- | 2^254 as a `BigInt` — the upper bound the circuit enforces on both
-- | `s_field` and `e_field` (via the top-bit-zero constraint inside
-- | `scaleFast2'`).
twoTo254 :: BigInt
twoTo254 = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 254)

-- | 2^255 reduced into `Pallas.ScalarField`. The verifier circuit
-- | computes `(s + 2^255)·G`, where `2^255 mod q` is this constant.
-- | (Note: `2^255 > q`, so this reduces to `2^255 - q ≈ 2^254`.)
twoTo255Pallas :: Pallas.ScalarField
twoTo255Pallas = fromBigInt (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 255))

-- | LSB-is-0 check on a field element (matches the circuit's `y_even`).
isEven :: Pallas.BaseField -> Boolean
isEven x = not $ BigInt.odd (toBigInt x)

-- | Zero-seed Poseidon hash: `e = Poseidon(pk.x, pk.y, r, ...msg)`.
-- | Mirrors the in-circuit `Sponge.absorb`-then-`squeeze` shape used by
-- | `Snarky.Circuit.Schnorr.verifies`.
hashMessage
  :: { x :: Pallas.BaseField, y :: Pallas.BaseField }
  -> Pallas.BaseField
  -> Array Pallas.BaseField
  -> Pallas.BaseField
hashMessage { x: px, y: py } r message =
  Poseidon.hash $ px : py : r : message

-- | Try to sign `message` with `privateKey` using the supplied `nonce`.
-- | Returns `Nothing` on a rejection condition; caller rotates the
-- | nonce and retries.
-- |
-- | Rejection conditions (all happen with probability ~½ each, so a
-- | random nonce succeeds in ~8 tries on average):
-- |   - `R.y` is odd (the verifier asserts `y_even`).
-- |   - `e_bigint ≥ 2^254` (the circuit's `scaleFast2' @51 @253` zeros
-- |     the top 2 bits of `s_div_2`).
-- |   - `s_bigint ≥ 2^254` (same constraint, this time on `s`).
sign
  :: { privateKey :: Pallas.ScalarField
     , nonce :: Pallas.ScalarField
     , message :: Array Pallas.BaseField
     }
  -> Maybe (Signature Pallas.BaseField)
sign { privateKey: d, nonce: k, message } = do
  publicKey <- toAffine (scalarMul d (generator :: PallasG))
  { x: r, y: ry } <- toAffine (scalarMul k (generator :: PallasG))
  if not (isEven ry) then Nothing
  else do
    let
      eTick = hashMessage publicKey r message
      eBigint = toBigInt eTick
    if eBigint >= twoTo254 then Nothing
    else
      let
        ePallas = fromBigInt eBigint :: Pallas.ScalarField
        eEff = ePallas + twoTo255Pallas
        sEff = k + d * eEff
        sPallas = sEff - twoTo255Pallas
        sBigint = toBigInt sPallas
      in
        if sBigint >= twoTo254 then Nothing
        else Just $ Signature { r, s: fromBigInt sBigint }

-- | Verify a Schnorr signature out-of-circuit, mirroring the circuit
-- | math. Returns `false` if either component overflows the 254-bit
-- | constraint, the reconstructed `R'` lands at infinity, `R'.y` is
-- | odd, or `R'.x ≠ r`.
verify
  :: Signature Pallas.BaseField
  -> { x :: Pallas.BaseField, y :: Pallas.BaseField }
  -> Array Pallas.BaseField
  -> Boolean
verify (Signature { r, s }) publicKey message =
  let
    sBigint = toBigInt s
    eTick = hashMessage publicKey r message
    eBigint = toBigInt eTick
  in
    if sBigint >= twoTo254 || eBigint >= twoTo254 then false
    else
      let
        ePallas = fromBigInt eBigint :: Pallas.ScalarField
        sPallas = fromBigInt sBigint :: Pallas.ScalarField
        eEff = ePallas + twoTo255Pallas
        sEff = sPallas + twoTo255Pallas

        pkPoint :: PallasG
        pkPoint = fromAffine publicKey
        sG = scalarMul sEff (generator :: PallasG)
        ePk = scalarMul eEff pkPoint
        rPoint = sG <> inverse ePk
      in
        case toAffine rPoint of
          Nothing -> false
          Just { x: rx, y: ry } -> isEven ry && rx == r
