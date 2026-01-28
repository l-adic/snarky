-- | Bulletproof verifier circuits for Pickles.
-- |
-- | This module implements the core IPA (Inner Product Argument) verification
-- | components needed for recursive proof composition.
-- |
-- | Note: In the Pickles pattern, challenges are computed outside the circuit
-- | (via sponge on the other curve's field) and passed as public inputs.
-- | The `lrProdCircuit` function uses these pre-computed challenges.
module Pickles.BulletproofVerifier
  ( -- Components
    combineSplitCommitments
  -- Pure reference (mirrors Rust IPA verify)
  , lrProdPure
  -- Circuit version (testable against lrProdPure)
  , lrProdCircuit
  ) where

import Prelude

import Data.Foldable (foldM)
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable)
import Data.Semigroup.Foldable (foldl1)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, reverse, uncons)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Prim.Int (class Add, class Mul)
import Snarky.Circuit.DSL (Snarky)
import Snarky.Circuit.DSL.Monad (class CircuitM)
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Circuit.Kimchi.EndoMul (endo)
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast2, splitFieldVar)
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class HasEndo, class PrimeField, class WeierstrassCurve, fromAffine, scalarMul, toAffine)
import Snarky.Data.EllipticCurve (AffinePoint)

--------------------------------------------------------------------------------
-- | Pure Reference (mirrors Rust IPA verify)
--------------------------------------------------------------------------------

-- | Pure computation of lr_prod from L/R pairs and endo-mapped challenges.
-- |
-- | This mirrors the Rust IPA verification formula exactly:
-- |   lr_prod = sum(chal_inv[i] * L[i] + chal[i] * R[i])
-- |
-- | Where chal[i] is the endo-mapped challenge (full field element, not 128-bit).
-- |
-- | Reference: poly-commitment/src/ipa.rs lines 252-258
-- | The d parameter is the number of IPA rounds (domain log2), enforced >= 1.
lrProdPure
  :: forall @d @d' @f @f' @g
   . Add 1 d' d
  => Reflectable d Int
  => WeierstrassCurve f g
  => FrModule f' g
  => Vector d { l :: AffinePoint f, r :: AffinePoint f }
  -> Vector d f' -- ^ Endo-mapped challenges (from proofBulletproofChallenges FFI)
  -> AffinePoint f
lrProdPure lrPairs chals =
  let

    -- Compute each term: chal_inv * L + chal * R
    terms = map computeTerm $ Vector.zip lrPairs chals

    acc = foldl1 (<>) terms

    -- Convert back to affine
    { x, y } = unsafePartial $ fromJust $ toAffine @f @g acc
  in
    { x, y }
  where
  computeTerm (Tuple { l, r } chal) =
    let
      lProj = fromAffine @f @g l
      rProj = fromAffine @f @g r
    in
      scalarMul (recip chal) lProj <> scalarMul chal rProj

-- | Circuit version of lr_prod computation.
-- |
-- | Takes L/R pairs and endo-mapped challenges (full field elements) and computes:
-- |   lr_prod = sum(chal_inv[i] * L[i] + chal[i] * R[i])
-- |
-- | This can be tested directly against lrProdPure.
-- |
-- | Note: Uses scaleFast2 for scalar multiplication with full field elements.
-- | The nChunks type parameter controls the chunking for scaleFast2 (5 * nChunks = 255).
-- | The d parameter is the number of IPA rounds (domain log2), enforced >= 1.
lrProdCircuit
  :: forall @d @d' @nChunks f t m
   . Add 1 d' d
  => Reflectable d Int
  => Mul 5 nChunks 255
  => Reflectable nChunks Int
  => FieldSizeInBits f 255
  => PrimeField f
  => CircuitM f (KimchiConstraint f) t m
  => Vector d { l :: AffinePoint (FVar f), r :: AffinePoint (FVar f) }
  -> Vector d (FVar f) -- ^ Endo-mapped challenges
  -> Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
lrProdCircuit lrPairs chals = do
  -- Compute challenge inverses in circuit
  chalInvs <- traverse (\c -> recip (pure c)) chals

  -- Compute each term: chal_inv * L + chal * R
  -- Combine inputs with zipWith, then traverse with the effectful computation
  let inputs = Vector.zipWith mkInput lrPairs (Vector.zip chals chalInvs)
  terms <- traverse computeTermCircuit inputs

  -- Sum all terms (safe: d >= 1 enforced by Add 1 d' d)
  let { head, tail } = uncons terms
  foldM (\acc t -> _.p <$> addComplete acc t) head tail
  where
  mkInput { l, r } (Tuple chal chalInv) = { l, r, chal, chalInv }

  computeTermCircuit { l, r, chal, chalInv } = do
    -- Convert challenges to Type2 for scaleFast2
    chalType2 <- splitFieldVar chal
    chalInvType2 <- splitFieldVar chalInv

    -- L * chal_inv + R * chal
    termL <- scaleFast2 @nChunks l chalInvType2
    termR <- scaleFast2 @nChunks r chalType2
    _.p <$> addComplete termL termR

--------------------------------------------------------------------------------
-- | Combine Split Commitments (In-Circuit)
--------------------------------------------------------------------------------

-- | Combine polynomial commitments with a batching scalar using Horner's method.
-- |
-- | Given commitments [c_0, c_1, ..., c_{n-1}] and scalar xi, computes:
-- |   c_0 + xi * c_1 + xi^2 * c_2 + ... + xi^{n-1} * c_{n-1}
-- |
-- | Using Horner's method to only multiply by xi (128-bit scalar):
-- |   c_0 + xi * (c_1 + xi * (c_2 + ... + xi * c_{n-1}))
-- |
-- | This allows using `endo` for efficient scalar multiplication.
-- |
-- | Note: Requires n >= 1 (at least one commitment).
combineSplitCommitments
  :: forall @n @n' f f' t m
   . Reflectable n Int
  => Add 1 n' n
  => FieldSizeInBits f 255
  => HasEndo f f'
  => PrimeField f
  => CircuitM f (KimchiConstraint f) t m
  => FVar f -- ^ xi (scalar challenge, 128 bits)
  -> Vector n (AffinePoint (FVar f)) -- ^ commitments
  -> Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
combineSplitCommitments xi commitments = do
  -- Reverse commitments for Horner's method: start from c_{n-1}
  let
    reversed = reverse commitments
    { head, tail } = uncons reversed

  -- Fold using Horner: acc = endo(acc, xi) + c_i
  foldM step head tail
  where
  step acc c = do
    scaled <- endo acc xi
    _.p <$> addComplete scaled c
