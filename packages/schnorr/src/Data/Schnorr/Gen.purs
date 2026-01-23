-- | Test generators for Schnorr signatures
module Data.Schnorr.Gen
  ( VerifyInput
  , genValidSignature
  , coerceViaBits
  ) where

import Prelude

import Data.Array ((:))
import Data.Maybe (Maybe(..), fromJust, isJust)
import Data.Reflectable (class Reflectable)
import Data.Schnorr (isEven, truncateFieldCoerce)
import Data.Vector (Vector)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Poseidon (class PoseidonField)
import Poseidon as Poseidon
import Snarky.Circuit.DSL.Bits (packPure, unpackPure)
import Snarky.Circuit.Types (F(..))
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class PrimeField, class WeierstrassCurve, fromBigInt, generator, scalarMul, toAffine, toBigInt)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (class Shifted, Type2, toShifted)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen, suchThat)
import Type.Proxy (Proxy)

-- | Input type for Schnorr verification circuit.
-- | All values are in the circuit field f (base field of curve g).
-- | Uses a type alias since CircuitType has a generic instance for records.
type VerifyInput n a b =
  { signature ::
      { r :: a
      , s :: Type2 a b
      }
  , publicKey :: AffinePoint a
  , message :: Vector n a
  }

-- | Convert between fields via bit representation (preserves integer value)
coerceViaBits :: forall f f'. PrimeField f => PrimeField f' => FieldSizeInBits f 255 => FieldSizeInBits f' 255 => f -> f'
coerceViaBits = packPure <<< unpackPure

-- | Generate a valid signature for testing using the library's sign function.
-- | Returns VerifyInput with all values in the circuit field (base field).
-- | f = base field of curve g (circuit field)
-- | f' = scalar field of curve g
genValidSignature
  :: forall f f' g n
   . PoseidonField f
  => PrimeField f'
  => Reflectable n Int
  => WeierstrassCurve f g
  => FrModule f' g
  => PrimeField f
  => Shifted (F f') (Type2 (F f) Boolean)
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => Proxy g
  -> Proxy n
  -> Gen (VerifyInput n (F f) Boolean)
genValidSignature pg pn = do
  -- Generate random private key (in scalar field f')
  privateKey <- arbitrary @f' `suchThat` \sk ->
    isJust $ toAffine $ scalarMul sk (generator @_ @g)
  let
    publicKey = unsafePartial fromJust
      $ toAffine
      $ scalarMul privateKey (generator @_ @g)
  -- Generate random message field element (in base field f)
  message <- Vector.generateA @n (const arbitrary)

  -- Compute public key first (this ties the curve type g)

  let
    kPrimeBase = Poseidon.hash $ publicKey.x : publicKey.y : Vector.toUnfoldable message

    kPrime :: f'
    kPrime = truncateFieldCoerce kPrimeBase

  if kPrime == zero then
    genValidSignature pg pn
  else
    case toAffine $ scalarMul kPrime (generator @_ @g) of
      Nothing -> genValidSignature pg pn
      Just { x: r, y: ry } -> do
        let
          k = if isEven ry then kPrime else negate kPrime
          eBase = Poseidon.hash $ publicKey.x : publicKey.y : r : Vector.toUnfoldable message

          e :: f'
          e = fromBigInt (toBigInt eBase)

          s :: f'
          s = k + e * privateKey

        pure
          { signature: { r: F r, s: toShifted $ F s }
          , publicKey: { x: F publicKey.x, y: F publicKey.y }
          , message: map F message
          }
