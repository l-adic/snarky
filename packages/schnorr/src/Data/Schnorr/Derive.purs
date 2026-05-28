-- | Deterministic Schnorr nonce derivation, byte-compatible with
-- | `Schnorr.Chunked.Message.make_derive` /
-- | `mina/src/lib/crypto/signature_lib/schnorr.ml:402`.
-- |
-- | Pipeline:
-- |   1. Build a `Random_oracle.Input.Chunked` whose `field_elements`
-- |      are `[pk.x; pk.y; project(privateKey)]` and whose `packeds`
-- |      include the 1-byte network-id tag (8 bits, LSB-first).
-- |   2. `pack_to_fields` it (greedy left-to-right bit-packer).
-- |   3. Unpack each resulting field to 255 LSB-first bits and concat.
-- |   4. Pack bits into a byte-string (LSB-first within each byte) and
-- |      Blake2b-256-hash it.
-- |   5. Unpack the digest into 256 LSB-first bits, take the first
-- |      `min 256 (scalar.size_in_bits - 1) = 254` bits, project as a
-- |      Pallas scalar — that is the nonce.
module Data.Schnorr.Derive
  ( deriveNonce
  ) where

import Prelude

import Data.Array as Array
import Data.Blake2b (blake2b256Bits)
import Data.Enum (fromEnum, toEnum)
import Data.Foldable (foldl)
import Data.Maybe (fromMaybe)
import Data.Reflectable (reflectType)
import Data.String.CodeUnits as String
import JS.BigInt (BigInt)
import JS.BigInt as BigInt
import RandomOracle.Input as Input
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromBigInt, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Type.Proxy (Proxy(..))

-- | LSB-first bit unpacking of a field element, padded to
-- | `size_in_bits` (mirrors OCaml `Field.unpack`).
fieldToBitsLE
  :: forall f n
   . PrimeField f
  => FieldSizeInBits f n
  => f
  -> Array Boolean
fieldToBitsLE x =
  let
    n = reflectType (Proxy :: Proxy n)
    big = toBigInt x
    one' = BigInt.fromInt 1
    bitAt i = BigInt.and (BigInt.shr big (BigInt.fromInt i)) one' == one'
  in
    map bitAt (Array.range 0 (n - 1))

-- | LSB-first bit packing of a bit array, reduced into `f`. Equivalent
-- | to OCaml `Field.project`: `Σ bits[i] * 2^i mod p`.
projectBitsLE :: forall f. PrimeField f => Array Boolean -> f
projectBitsLE bits =
  let
    folded :: BigInt
    folded =
      _.acc $ foldl
        ( \{ acc, pow } b ->
            { acc: if b then acc + pow else acc
            , pow: pow * BigInt.fromInt 2
            }
        )
        { acc: BigInt.fromInt 0, pow: BigInt.fromInt 1 }
        bits
  in
    fromBigInt folded

-- | LSB-first per-byte bit unpacking of a latin-1 byte-string. Matches
-- | OCaml `Fold_lib.Fold.string_bits`.
stringToBitsLE :: String -> Array Boolean
stringToBitsLE s = Array.concatMap charToBits (String.toCharArray s)
  where
  charToBits c =
    let
      code = fromEnum c `mod` 256
      bitAt i = ((code `div` pow2 i) `mod` 2) == 1
    in
      map bitAt (Array.range 0 7)

-- | Pack a bit array into a latin-1 byte-string, LSB-first within each
-- | byte. Mirrors OCaml `Blake2.bits_to_string`.
bitsToString :: Array Boolean -> String
bitsToString bits =
  let
    nBytes = (Array.length bits + 7) / 8
    byteAt j =
      foldl
        ( \acc i ->
            if fromMaybe false (Array.index bits (8 * j + i)) then acc + pow2 i
            else acc
        )
        0
        (Array.range 0 7)
    chars = map (intToChar <<< byteAt) (Array.range 0 (nBytes - 1))
  in
    String.fromCharArray chars
  where
  intToChar n = fromMaybe '\x00' (toEnum n)

-- | Power of two for `i` in `[0..7]`.
pow2 :: Int -> Int
pow2 i = case i of
  0 -> 1
  1 -> 2
  2 -> 4
  3 -> 8
  4 -> 16
  5 -> 32
  6 -> 64
  _ -> 128

-- | Derive a deterministic Pallas-scalar nonce from `(networkId, sk,
-- | pk, message)`. Byte-compat with OCaml `Schnorr.Chunked.Message.derive`.
deriveNonce
  :: { networkId :: String
     , privateKey :: Pallas.ScalarField
     , publicKey :: { x :: Pallas.BaseField, y :: Pallas.BaseField }
     , message :: Input.Chunked Pallas.BaseField
     }
  -> Pallas.ScalarField
deriveNonce { networkId, privateKey, publicKey: { x, y }, message } =
  let
    idBits = stringToBitsLE networkId
    idLength = Array.length idBits
    idField :: Pallas.BaseField
    idField = projectBitsLE idBits

    -- `Field.project (Tock.Field.unpack private_key)` — re-embed the
    -- scalar's bit representation in the base field. Same as
    -- `fromBigInt (toBigInt _)` because both fields are 255-bit and
    -- `fromBigInt` reduces mod the base field modulus.
    privField :: Pallas.BaseField
    privField = fromBigInt (toBigInt privateKey)

    input :: Input.Chunked Pallas.BaseField
    input = Input.append message
      { fieldElements: [ x, y, privField ]
      , packeds: [ { value: idField, length: idLength } ]
      }

    packed :: Array Pallas.BaseField
    packed = Input.packToFields input

    allBits :: Array Boolean
    allBits = Array.concat (map fieldToBitsLE packed)

    bytes :: String
    bytes = bitsToString allBits

    hashBits :: Array Boolean
    hashBits = blake2b256Bits bytes

    -- `min 256 (Pallas.ScalarField.size_in_bits - 1) = min 256 254 = 254`.
    truncated :: Array Boolean
    truncated = Array.take 254 hashBits
  in
    projectBitsLE truncated
