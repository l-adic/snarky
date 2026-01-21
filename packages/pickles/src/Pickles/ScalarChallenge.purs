-- | Scalar challenge types and squeeze functions for Pickles.
-- |
-- | This module provides:
-- | - Challenge types for PLONK verification (alpha, beta, gamma, zeta, joint_combiner)
-- | - Squeeze functions to extract 128-bit challenges from a Poseidon sponge
-- |
-- | The key distinction:
-- | - `Challenge f`: Regular challenges (beta, gamma) - 128 bits with boolean constraints
-- | - `ScalarChallenge f`: Scalar challenges (alpha, zeta) - 128 bits without boolean constraints
-- |
-- | Scalar challenges use endomorphism encoding for efficient EC operations.
module Pickles.ScalarChallenge
  ( Challenge(..)
  , Challenges
  , ChallengesMinimal
  , lowest128BitsConstant
  , lowest128Bits
  , squeezeChallengePure
  , squeezeScalarPure
  , squeezeChallenge
  , squeezeScalar
  , module Exports
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Linearization.Types (FeatureFlag)
import Poseidon (class PoseidonField)
import Prim.Int (class Add)
import RandomOracle.Sponge (Sponge)
import RandomOracle.Sponge as Sponge
import Snarky.Circuit.DSL (Snarky)
import Snarky.Circuit.DSL.Bits (pack_, unpackPure, unpack_)
import Snarky.Circuit.DSL.Monad (class CircuitM)
import Snarky.Circuit.Kimchi.EndoScalar (ScalarChallenge(..))
import Snarky.Circuit.Kimchi.EndoScalar (ScalarChallenge(..), toField, toFieldConstant) as Exports
import Snarky.Circuit.RandomOracle.Sponge as CircuitSponge
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromInt)

-------------------------------------------------------------------------------
-- | Challenge Types
-------------------------------------------------------------------------------

-- | A regular challenge value (beta, gamma).
-- | These are 128-bit values with boolean constraints on the low bits.
newtype Challenge f = Challenge f

derive instance Newtype (Challenge f) _
derive instance Eq f => Eq (Challenge f)
derive instance Ord f => Ord (Challenge f)
derive newtype instance Show f => Show (Challenge f)

-- | Minimal set of PLONK challenges.
-- | This is used in proofs - just the raw challenges without derived values.
type ChallengesMinimal challenge scalar =
  { alpha :: scalar
  , beta :: challenge
  , gamma :: challenge
  , zeta :: scalar
  , jointCombiner :: Maybe scalar
  , featureFlags :: Array FeatureFlag
  }

-- | Full set of PLONK challenges with derived values.
-- | Used in-circuit when the verifier needs to compute derived scalars.
type Challenges challenge scalar fp =
  { alpha :: scalar
  , beta :: challenge
  , gamma :: challenge
  , zeta :: scalar
  -- Derived values computed from zeta:
  , zetaToSrsLength :: fp -- zeta^srs_length
  , zetaToDomainSize :: fp -- zeta^domain_size - 1
  , perm :: fp -- permutation scalar
  , jointCombiner :: Maybe scalar
  , featureFlags :: Array FeatureFlag
  }

-------------------------------------------------------------------------------
-- | Pure (constant) squeeze functions
-------------------------------------------------------------------------------

-- | Extract the lowest 128 bits from a field element (pure version).
-- | Returns the low 128 bits as a field element.
lowest128BitsConstant
  :: forall f n _l
   . PrimeField f
  => FieldSizeInBits f n
  => Add 128 _l n
  => f
  -> f
lowest128BitsConstant x =
  let
    -- Unpack to bits (LSB first), take first 128
    bits :: Vector 128 Boolean
    bits = Vector.take @128 $ unpackPure x
  in
    -- Pack back to field element
    foldlWithIndex
      (\i acc b -> if b then acc + pow2 (getFinite i) else acc)
      zero
      bits
  where
  pow2 :: Int -> f
  pow2 0 = one
  pow2 n = fromInt 2 * pow2 (n - 1)

-- | Squeeze a challenge from the sponge (pure version).
-- | Returns the lowest 128 bits of the squeezed field element.
squeezeChallengePure
  :: forall f
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => Sponge f
  -> { result :: Challenge f, sponge :: Sponge f }
squeezeChallengePure sponge =
  let
    { result: x, sponge: sponge' } = Sponge.squeeze sponge
  in
    { result: Challenge $ lowest128BitsConstant x, sponge: sponge' }

-- | Squeeze a scalar challenge from the sponge (pure version).
-- | Returns the lowest 128 bits wrapped as a ScalarChallenge.
squeezeScalarPure
  :: forall f
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => Sponge f
  -> { result :: ScalarChallenge f, sponge :: Sponge f }
squeezeScalarPure sponge =
  let
    { result: x, sponge: sponge' } = Sponge.squeeze sponge
  in
    { result: ScalarChallenge $ lowest128BitsConstant x, sponge: sponge' }

-------------------------------------------------------------------------------
-- | Circuit (in-circuit) squeeze functions
-------------------------------------------------------------------------------

-- | Extract the lowest 128 bits from a field element (circuit version).
-- | Unpacks to bits, takes the low 128, and packs back.
lowest128Bits
  :: forall f t m
   . PrimeField f
  => FieldSizeInBits f 255
  => CircuitM f (KimchiConstraint f) t m
  => FVar f
  -> Snarky (KimchiConstraint f) t m (FVar f)
lowest128Bits x = do
  bits <- unpack_ x
  let low128 = Vector.take @128 bits
  pure $ pack_ low128

-- | Squeeze a challenge from the sponge (circuit version).
-- | Returns the lowest 128 bits of the squeezed field element.
squeezeChallenge
  :: forall f t m
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Sponge (FVar f)
  -> Snarky (KimchiConstraint f) t m { result :: Challenge (FVar f), sponge :: Sponge (FVar f) }
squeezeChallenge sponge = do
  { result: x, sponge: sponge' } <- CircuitSponge.squeeze sponge
  truncated <- lowest128Bits x
  pure { result: Challenge truncated, sponge: sponge' }

-- | Squeeze a scalar challenge from the sponge (circuit version).
-- | Returns the lowest 128 bits wrapped as a ScalarChallenge.
squeezeScalar
  :: forall f t m
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Sponge (FVar f)
  -> Snarky (KimchiConstraint f) t m { result :: ScalarChallenge (FVar f), sponge :: Sponge (FVar f) }
squeezeScalar sponge = do
  { result: x, sponge: sponge' } <- CircuitSponge.squeeze sponge
  truncated <- lowest128Bits x
  pure { result: ScalarChallenge truncated, sponge: sponge' }
