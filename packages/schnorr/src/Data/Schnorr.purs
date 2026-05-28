-- | Out-of-circuit Schnorr signature signer/verifier matching the
-- | iteration-2c kimchi-circuit verifier in
-- | `Snarky.Circuit.Schnorr.verifies`.
-- |
-- | The signature is `(r :: Pallas.BaseField, s :: Pallas.BaseField)`.
-- | `r = R.x` (so it naturally lives in the base field). `s` is
-- | computed in the Pallas scalar field and re-embedded in the base
-- | field for transport — `s < q < p` so the embedding is lossless.
-- | The verifier circuit re-unpacks `s` to 255 bits and feeds them to
-- | the LSB-first `Snarky_curves.scale`, which now has no cap.
-- |
-- | `sign` is total: the deterministic nonce derivation plus the
-- | negate-k trick (flip `k` when `R.y` is odd; the new `R.y` is then
-- | even because `p - y` has opposite parity to `y` in odd
-- | characteristic) cover both former rejection branches. The 2^254
-- | caps from iter 2a/2b are gone now that the verifier accepts
-- | full-range scalars.
module Data.Schnorr
  ( Signature(..)
  , isEven
  , hashMessage
  , sign
  , verify
  ) where

import Prelude

import Data.Foldable (foldl)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Schnorr.Derive (deriveNonce)
import Data.Vector (Vector)
import JS.BigInt as BigInt
import RandomOracle.Input as Input
import RandomOracle.Sponge (absorb, create, squeeze) as Sponge
import Snarky.Curves.Class (fromAffine, fromBigInt, generator, inverse, scalarMul, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG)

-- | Schnorr signature components, both in the native circuit field
-- | (`Pallas.BaseField`). `r = R.x` is naturally a base-field value;
-- | `s` is the scalar-field result re-embedded in the base field
-- | (lossless because `q < p` for Pasta).
newtype Signature f = Signature
  { r :: f
  , s :: f
  }

derive instance Newtype (Signature f) _
derive instance Generic (Signature f) _
derive newtype instance Show f => Show (Signature f)
derive newtype instance Eq f => Eq (Signature f)

-- | LSB-is-0 check on a field element (matches the circuit's `y_even`).
isEven :: Pallas.BaseField -> Boolean
isEven x = not $ BigInt.odd (toBigInt x)

-- | Schnorr message hash:
-- |
-- |   `e = squeeze ( absorb (msg…, pk.x, pk.y, r) (sponge_init spongePrefix) )`
-- |
-- | Mirrors Mina's `Schnorr.Chunked.Message.hash` shape — caller-supplied
-- | 3-element sponge prefix state, absorb the
-- | `Random_oracle.Input.Chunked.append message {pk; r}` field sequence
-- | (message first), squeeze. The same `(spongePrefix, absorb_order)`
-- | choice is used by `Snarky.Circuit.Schnorr.verifies`, so the value
-- | and circuit hash match by construction.
hashMessage
  :: Vector 3 Pallas.BaseField
  -> { x :: Pallas.BaseField, y :: Pallas.BaseField }
  -> Pallas.BaseField
  -> Array Pallas.BaseField
  -> Pallas.BaseField
hashMessage spongePrefix { x: px, y: py } r message =
  let
    sponge0 = Sponge.create spongePrefix
    spongeMsg = foldl (\sp x -> Sponge.absorb x sp) sponge0 message
    sponge1 = Sponge.absorb px spongeMsg
    sponge2 = Sponge.absorb py sponge1
    sponge3 = Sponge.absorb r sponge2
  in
    (Sponge.squeeze sponge3).result

-- | Re-embed a base-field value as a scalar-field value via its
-- | canonical integer representative. Lossless when the value is
-- | `< min(p, q)`. For Pasta both moduli fit in 255 bits and the
-- | Poseidon-output `e` is always `< p`, so reading as `< q` is the
-- | safe wraparound-mod-q reduction that the circuit performs.
toScalar :: Pallas.BaseField -> Pallas.ScalarField
toScalar = fromBigInt <<< toBigInt

-- | Same direction, scalar → base. `s < q < p` so the read is direct.
toBase :: Pallas.ScalarField -> Pallas.BaseField
toBase = fromBigInt <<< toBigInt

-- | Sign `message` with `privateKey` using the iter-2c convention:
-- | deterministic nonce + negate-k. Total — no rejection branches.
sign
  :: { spongePrefix :: Vector 3 Pallas.BaseField
     , networkId :: String
     , privateKey :: Pallas.ScalarField
     , message :: Array Pallas.BaseField
     }
  -> Maybe (Signature Pallas.BaseField)
sign { spongePrefix, networkId, privateKey: d, message } = do
  publicKey <- toAffine (scalarMul d (generator :: PallasG))
  let
    kPrime = deriveNonce
      { networkId
      , privateKey: d
      , publicKey
      , message: Input.fieldElements message
      }
  { x: r, y: ry } <- toAffine (scalarMul kPrime (generator :: PallasG))
  let
    -- `negate kPrime` flips R.y's sign; since p is odd, `p - ry` has
    -- opposite parity to `ry`, so this always produces an even `R.y`.
    k = if isEven ry then kPrime else zero - kPrime
    eBase = hashMessage spongePrefix publicKey r message
    eScalar = toScalar eBase
    sScalar = k + d * eScalar
  pure $ Signature { r, s: toBase sScalar }

-- | Verify a Schnorr signature out-of-circuit, mirroring the new
-- | iter-2c circuit math: `R' = s·G − e·pk`, accept iff `R'.y` even
-- | and `R'.x == r`. No 2^254 caps.
verify
  :: Vector 3 Pallas.BaseField
  -> Signature Pallas.BaseField
  -> { x :: Pallas.BaseField, y :: Pallas.BaseField }
  -> Array Pallas.BaseField
  -> Boolean
verify spongePrefix (Signature { r, s }) publicKey message =
  let
    eBase = hashMessage spongePrefix publicKey r message
    eScalar = toScalar eBase
    sScalar = toScalar s

    pkPoint :: PallasG
    pkPoint = fromAffine publicKey
    sG = scalarMul sScalar (generator :: PallasG)
    ePk = scalarMul eScalar pkPoint
    rPoint = sG <> inverse ePk
  in
    case toAffine rPoint of
      Nothing -> false
      Just { x: rx, y: ry } -> isEven ry && rx == r
