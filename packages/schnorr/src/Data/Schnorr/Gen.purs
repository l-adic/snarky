-- | QuickCheck generators for Schnorr signatures matching the new
-- | kimchi-circuit verifier (`Snarky.Circuit.Schnorr.verifies`).
-- |
-- | Pallas-specific: both `r` and `s` are `Pallas.BaseField` (the
-- | native circuit field). The generator rejection-samples a fresh
-- | nonce until `Data.Schnorr.sign` accepts it.
module Data.Schnorr.Gen
  ( VerifyInput
  , genValidSignature
  ) where

import Prelude

import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable)
import Data.Schnorr as Schnorr
import Data.Vector (Vector)
import Data.Vector as Vector
import Mina.ChainId (ChainId(..), networkId)
import Partial.Unsafe (unsafePartial)
import Snarky.Circuit.DSL (F(..))
import Snarky.Circuit.DSL.Bits (unpackPure)
import Snarky.Curves.Class (fromBigInt, generator, scalarMul, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen)
import Type.Proxy (Proxy(..))

-- | Flat input to the kimchi Schnorr verifier circuit. Mirrors the
-- | OCaml production `Signature.var = Field.Var.t * Curve.Scalar.var`
-- | shape: `r` is a base-field value, `s_bits` is the 255-bit LSB-first
-- | decomposition of the Pallas-scalar `s` (Booleans).
type VerifyInput n a =
  { signature ::
      { r :: F a
      , sBits :: Vector 255 Boolean
      }
  , publicKey :: AffinePoint a
  , message :: Vector n (F a)
  }

-- | Generate a verifying Schnorr signature for QuickCheck. The nonce is
-- | derived deterministically from `(networkId, sk, pk, message)` and
-- | `Data.Schnorr.sign` is total, so we just sample `(privateKey,
-- | message)` and sign once.
-- |
-- | Caller passes `Proxy @PallasG` and the message-length proxy so the
-- | type-application surface mirrors the older `Data.Schnorr.Gen` API
-- | used by `Test.Snarky.Circuit.Schnorr`. The chain-id tag is hard-wired
-- | to Mainnet here — tests can lift this if they need Testnet coverage.
genValidSignature
  :: forall n
   . Reflectable n Int
  => Vector 3 Pallas.BaseField
  -> Proxy PallasG
  -> Proxy n
  -> Gen (VerifyInput n Pallas.BaseField)
genValidSignature spongePrefix _pg _pn = do
  privateKey :: Pallas.ScalarField <- arbitrary
  message :: Vector n Pallas.BaseField <- Vector.generateA (const arbitrary)
  let
    Schnorr.Signature { r, s } = Schnorr.sign
      { spongePrefix
      , networkId: networkId Mainnet
      , privateKey
      , message: Vector.toUnfoldable message
      }
    publicKey = unsafePartial fromJust
      $ toAffine
      $ scalarMul privateKey (generator :: PallasG)
    -- `s` is the base-field re-embedding of the Pallas scalar;
    -- decompose to 255 LSB-first bits to match the production
    -- `Signature.var` shape.
    sScalar = fromBigInt (toBigInt s) :: Pallas.ScalarField
    sBits = unpackPure sScalar (Proxy @255)
  pure
    { signature: { r: F r, sBits }
    , publicKey: AffinePoint publicKey
    , message: map F message
    }
