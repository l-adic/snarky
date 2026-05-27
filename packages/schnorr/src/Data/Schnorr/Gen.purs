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

import Data.Maybe (Maybe(..), fromJust)
import Data.Reflectable (class Reflectable)
import Data.Schnorr as Schnorr
import Data.Vector (Vector)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Snarky.Circuit.DSL (F(..))
import Snarky.Curves.Class (generator, scalarMul, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen)
import Type.Proxy (Proxy)

-- | Flat input to the kimchi Schnorr verifier circuit. Mirrors the
-- | OCaml fixture's `Typ` layout: pk_x, pk_y, r, s, message…
type VerifyInput n a =
  { signature ::
      { r :: a
      , s :: a
      }
  , publicKey :: AffinePoint a
  , message :: Vector n a
  }

-- | Generate a verifying Schnorr signature for QuickCheck. Loops over
-- | random nonces until `Data.Schnorr.sign` accepts one (rejection
-- | probability ~7/8 per attempt — `ry` even, `e < 2^254`, `s < 2^254`).
-- |
-- | Caller passes `Proxy @PallasG` and the message-length proxy so the
-- | type-application surface mirrors the older `Data.Schnorr.Gen` API
-- | used by `Test.Snarky.Circuit.Schnorr`.
genValidSignature
  :: forall n
   . Reflectable n Int
  => Proxy PallasG
  -> Proxy n
  -> Gen (VerifyInput n (F Pallas.BaseField))
genValidSignature _pg _pn = go
  where
  go = do
    privateKey :: Pallas.ScalarField <- arbitrary
    nonce :: Pallas.ScalarField <- arbitrary
    message :: Vector n Pallas.BaseField <- Vector.generateA (const arbitrary)
    case Schnorr.sign
      { privateKey
      , nonce
      , message: Vector.toUnfoldable message
      } of
      Nothing -> go
      Just (Schnorr.Signature { r, s }) ->
        let
          publicKey = unsafePartial fromJust
            $ toAffine
            $ scalarMul privateKey (generator :: PallasG)
        in
          pure
            { signature: { r: F r, s: F s }
            , publicKey: { x: F publicKey.x, y: F publicKey.y }
            , message: map F message
            }
