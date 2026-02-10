-- | Type classes for elliptic curve cryptography.
-- |
-- | This module defines the core abstractions for working with elliptic curves:
-- |
-- | - `PrimeField`: Arithmetic in finite fields of prime order
-- | - `FrModule`: Scalar multiplication on curve groups
-- | - `WeierstrassCurve`: Curves in short Weierstrass form (y² = x³ + ax + b)
-- |
-- | These classes are implemented by concrete curve types in `Snarky.Curves.Pasta`
-- | and `Snarky.Curves.BN254`.
-- |
-- | ```purescript
-- | import Snarky.Curves.Pallas as Pallas
-- |
-- | -- Scalar field arithmetic
-- | x :: Pallas.ScalarField
-- | x = fromInt 42
-- |
-- | -- Group operations
-- | g :: Pallas.G
-- | g = generator  -- curve generator point
-- |
-- | p :: Pallas.G
-- | p = scalarMul x g  -- [42]G
-- | ```
module Snarky.Curves.Class
  ( class PrimeField
  , fromBigInt
  , toBigInt
  , modulus
  , pow
  , class FrModule
  , scalarMul
  , inverse
  , class WeierstrassCurve
  , curveParams
  , toAffine
  , fromAffine
  , generator
  , class FieldSizeInBits
  , fromInt
  , EndoBase(..)
  , EndoScalar(..)
  , class HasEndo
  , endoBase
  , endoScalar
  , class HasSqrt
  , sqrt
  , isSquare
  , BW19Params
  , class HasBW19
  , bw19Params
  ) where

import Prelude

import Data.Maybe (Maybe)
import Data.Reflectable (class Reflectable)
import JS.BigInt (BigInt)
import JS.BigInt as JS.BigInt
import Test.QuickCheck (class Arbitrary)
import Type.Proxy (Proxy)

-- | A prime field F_p with standard field operations.
-- |
-- | Instances must satisfy the field laws, and arithmetic is performed
-- | modulo the prime `modulus`.
class PrimeField :: Type -> Constraint
class (Eq f, Ord f, Show f, Field f, Arbitrary f) <= PrimeField f where
  -- | Convert a `BigInt` to a field element (reduced modulo p).
  fromBigInt :: BigInt -> f
  -- | Convert a field element to its canonical `BigInt` representation in [0, p).
  toBigInt :: f -> BigInt
  -- | The prime modulus p of this field.
  modulus :: BigInt
  -- | Exponentiation: `pow x n = x^n`.
  pow :: f -> BigInt -> f

-- | Convert an `Int` to a field element.
fromInt :: forall @f. PrimeField f => Int -> f
fromInt x = fromBigInt $ JS.BigInt.fromInt x

-- | A module over a scalar field, representing scalar multiplication on groups.
-- |
-- | The functional dependency `g -> f` means each group type has a unique
-- | scalar field.
class (PrimeField f, Monoid g) <= FrModule f g | g -> f where
  -- | Scalar multiplication: `scalarMul k p = [k]p`.
  scalarMul :: f -> g -> g
  -- | Group inverse (negation): `inverse p = -p`.
  inverse :: g -> g

-- | An elliptic curve in short Weierstrass form: y² = x³ + ax + b.
-- |
-- | The functional dependency `g -> f` means each group type has a unique
-- | base field for coordinates.
class PrimeField f <= WeierstrassCurve f g | g -> f where
  -- | The curve parameters a and b.
  curveParams :: Proxy g -> { a :: f, b :: f }
  -- | Convert to affine coordinates, returning `Nothing` for the point at infinity.
  toAffine :: g -> Maybe { x :: f, y :: f }
  -- | Create a point from affine coordinates (must be on the curve).
  fromAffine :: { x :: f, y :: f } -> g
  -- | The standard generator point for this curve.
  generator :: g

-- | Associates a prime field with its bit size at the type level.
class FieldSizeInBits :: Type -> Int -> Constraint
class (PrimeField f, Reflectable n Int) <= FieldSizeInBits f (n :: Int) | f -> n

-- | Efficient endomorphism for GLV scalar multiplication.
-- |
-- | For curves with an efficiently computable endomorphism φ, we have:
-- | ```
-- | φ(x, y) = (endoBase * x, y) = [endoScalar] · (x, y)
-- | ```
-- |
-- | This enables faster scalar multiplication via the GLV decomposition.
-- | The two field types form a 2-cycle (e.g., Pallas/Vesta scalar fields).

newtype EndoBase f = EndoBase f

newtype EndoScalar f = EndoScalar f

class (PrimeField f, PrimeField f') <= HasEndo f f' | f -> f', f' -> f where
  -- | The endomorphism constant for x-coordinates.
  endoBase :: EndoBase f
  -- | The scalar λ such that φ(P) = [λ]P.
  endoScalar :: EndoScalar f'

-- | Square root operations in a prime field.
-- |
-- | Used for point decompression and hash-to-curve implementations.
class PrimeField f <= HasSqrt f where
  -- | Compute √x if x is a quadratic residue, `Nothing` otherwise.
  sqrt :: f -> Maybe f
  -- | Check if x is a quadratic residue (has a square root in the field).
  isSquare :: f -> Boolean

-- | Precomputed constants for the BW19 hash-to-curve algorithm.
-- |
-- | These constants are specific to curves with a = 0 (y² = x³ + b).
type BW19Params f =
  { u :: f -- ^ First valid u where u ≠ 0 and f(u) ≠ 0
  , fu :: f -- ^ f(u) = u³ + b
  , sqrtNeg3U2MinusUOver2 :: f -- ^ (√(-3u²) - u) / 2
  , sqrtNeg3U2 :: f -- ^ √(-3u²)
  , inv3U2 :: f -- ^ 1 / (3u²)
  }

-- | Curves supporting BW19 hash-to-curve (group map).
-- |
-- | The BW19 algorithm maps field elements to curve points deterministically,
-- | used for hashing to elliptic curves.
class (PrimeField f, WeierstrassCurve f g) <= HasBW19 f g | g -> f where
  -- | Get the precomputed BW19 parameters for this curve.
  bw19Params :: Proxy g -> BW19Params f