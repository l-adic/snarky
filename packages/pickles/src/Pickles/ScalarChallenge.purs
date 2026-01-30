-- | Scalar challenge types and squeeze functions for Pickles.
-- |
-- | This module provides:
-- | - Challenge types for PLONK verification (alpha, beta, gamma, zeta, joint_combiner)
-- | - Squeeze functions to extract 128-bit challenges from a Poseidon sponge
-- |
-- | The key distinction:
-- | - `Challenge f`: Regular challenges (beta, gamma) - 128 bits with boolean constraints
-- | - `SizedF 128 f`: Scalar challenges (alpha, zeta) - 128 bits without boolean constraints
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
import JS.BigInt as BigInt
import Pickles.Linearization.Types (FeatureFlag)
import Poseidon (class PoseidonField)
import Prim.Int (class Add)
import RandomOracle.Sponge (Sponge)
import RandomOracle.Sponge as Sponge
import Snarky.Circuit.DSL (Snarky)
import Snarky.Circuit.DSL.Bits (pack_, unpackPure, unpack_)
import Snarky.Circuit.DSL.Monad (class CircuitM)
import Snarky.Circuit.Kimchi.EndoScalar (toField, toFieldPure) as Exports
import Snarky.Circuit.RandomOracle.Sponge as CircuitSponge
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromInt, pow)
import Snarky.Data.SizedF (SizedF(..))

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
-- | Scalar challenges (alpha, zeta, jointCombiner) are 128-bit SizedF values.
type ChallengesMinimal challenge f =
  { alpha :: SizedF 128 f
  , beta :: challenge
  , gamma :: challenge
  , zeta :: SizedF 128 f
  , jointCombiner :: Maybe (SizedF 128 f)
  , featureFlags :: Array FeatureFlag
  }

-- | Full set of PLONK challenges with derived values.
-- | Used in-circuit when the verifier needs to compute derived scalars.
type Challenges challenge f =
  { alpha :: SizedF 128 f
  , beta :: challenge
  , gamma :: challenge
  , zeta :: SizedF 128 f
  -- Derived values computed from zeta:
  , zetaToSrsLength :: f -- zeta^srs_length
  , zetaToDomainSize :: f -- zeta^domain_size - 1
  , perm :: f -- permutation scalar
  , jointCombiner :: Maybe (SizedF 128 f)
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
    two = fromInt 2
  in
    -- Pack back to field element
    foldlWithIndex
      (\i acc b -> if b then acc + pow two (BigInt.fromInt $ getFinite i) else acc)
      zero
      bits

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
-- | Returns the lowest 128 bits wrapped as a SizedF 128.
squeezeScalarPure
  :: forall f
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => Sponge f
  -> { result :: SizedF 128 f, sponge :: Sponge f }
squeezeScalarPure sponge =
  let
    { result: x, sponge: sponge' } = Sponge.squeeze sponge
  in
    { result: SizedF $ lowest128BitsConstant x, sponge: sponge' }

-------------------------------------------------------------------------------
-- | Circuit (in-circuit) squeeze functions
-------------------------------------------------------------------------------

-- | Extract the lowest 128 bits from a field element (circuit version).
-- | Unpacks to bits, takes the low 128, and packs back.
lowest128Bits
  :: forall f c t m
   . PrimeField f
  => FieldSizeInBits f 255
  => CircuitM f c t m
  => FVar f
  -> Snarky c t m (FVar f)
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
-- | Returns the lowest 128 bits wrapped as a SizedF 128.
squeezeScalar
  :: forall f t m
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Sponge (FVar f)
  -> Snarky (KimchiConstraint f) t m { result :: SizedF 128 (FVar f), sponge :: Sponge (FVar f) }
squeezeScalar sponge = do
  { result: x, sponge: sponge' } <- CircuitSponge.squeeze sponge
  truncated <- lowest128Bits x
  pure { result: SizedF truncated, sponge: sponge' }
