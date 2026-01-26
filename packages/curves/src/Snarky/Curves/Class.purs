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

class PrimeField :: Type -> Constraint
class (Eq f, Ord f, Show f, Field f, Arbitrary f) <= PrimeField f where
  fromBigInt :: BigInt -> f
  toBigInt :: f -> BigInt
  modulus :: BigInt
  pow :: f -> BigInt -> f

fromInt :: forall @f. PrimeField f => Int -> f
fromInt x = fromBigInt $ JS.BigInt.fromInt x

class (PrimeField f, Monoid g) <= FrModule f g | g -> f where
  scalarMul :: f -> g -> g
  inverse :: g -> g

class PrimeField f <= WeierstrassCurve f g | g -> f where
  curveParams :: Proxy g -> { a :: f, b :: f }
  toAffine :: g -> Maybe { x :: f, y :: f }
  fromAffine :: { x :: f, y :: f } -> g
  generator :: g

class FieldSizeInBits :: Type -> Int -> Constraint
class (PrimeField f, Reflectable n Int) <= FieldSizeInBits f (n :: Int) | f -> n

-- phi p == phi (x,y) := (endBase * x, y) == [endoScalar] \cdot p
class (PrimeField f, PrimeField f') <= HasEndo f f' | f -> f', f' -> f where
  endoBase :: f
  endoScalar :: f'

-- | Square root and quadratic residue operations.
-- | Used for hash-to-curve (group map) implementations.
class PrimeField f <= HasSqrt f where
  -- | Compute sqrt(x) if x is a quadratic residue, Nothing otherwise
  sqrt :: f -> Maybe f
  -- | Check if x is a quadratic residue (has a square root)
  isSquare :: f -> Boolean

-- | BW19 parameters for hash-to-curve (GroupMap)
-- | These are precomputed constants for the BW19 algorithm on curves with a=0
type BW19Params f =
  { u :: f -- First valid u where u ≠ 0 and f(u) ≠ 0
  , fu :: f -- f(u) = u³ + b
  , sqrtNeg3U2MinusUOver2 :: f -- (sqrt(-3u²) - u) / 2
  , sqrtNeg3U2 :: f -- sqrt(-3u²)
  , inv3U2 :: f -- 1 / (3u²)
  }

-- | Typeclass for curves that support BW19 hash-to-curve
class (PrimeField f, WeierstrassCurve f g) <= HasBW19 f g | g -> f where
  bw19Params :: Proxy g -> BW19Params f