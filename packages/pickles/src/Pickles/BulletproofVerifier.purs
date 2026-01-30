-- | Bulletproof verifier circuits for Pickles.
-- |
-- | This module implements the core IPA (Inner Product Argument) verification
-- | components needed for recursive proof composition.
-- |
-- | Reference: mina's step_verifier.ml `check_bulletproof` function
module Pickles.BulletproofVerifier
  ( -- Main verifier
    checkBulletproof
  -- Components
  , bulletReduce
  , combineSplitCommitments
  -- Pure reference (mirrors Rust IPA verify)
  , lrProdPure
  -- Circuit version (testable against lrProdPure)
  , lrProdCircuit
  -- Types
  , BulletReduceResult
  , CheckBulletproofInput
  , CheckBulletproofOutput
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
import Pickles.Sponge (SpongeM, absorb, absorbPoint, liftSnarky, squeeze, squeezeScalarChallenge)
import Poseidon (class PoseidonField)
import Prim.Int (class Add, class Mul)
import Snarky.Circuit.Curves as EllipticCurve
import Snarky.Circuit.DSL (Snarky)
import Snarky.Circuit.DSL.Monad (class CircuitM)
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Circuit.Kimchi.EndoMul (endo, endoInv)
import Snarky.Circuit.Kimchi.GroupMap (GroupMapParams, groupMapCircuit)
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast2, splitFieldVar)
import Snarky.Circuit.Types (BoolVar, FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class HasEndo, class HasSqrt, class PrimeField, class WeierstrassCurve, fromAffine, scalarMul, toAffine)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.SizedF (SizedF)
import Snarky.Types.Shifted (Type2)

--------------------------------------------------------------------------------
-- | Types
--------------------------------------------------------------------------------

-- | Result of bullet reduce operation
type BulletReduceResult d f =
  { lrProd :: AffinePoint f -- Accumulated L/R product
  , challenges :: Vector d (SizedF 128 f) -- Scalar challenges extracted (128 bits each)
  }

-- | Input to the bulletproof verifier circuit
-- |
-- | Type parameters:
-- | - d: number of IPA rounds (domain log2)
-- | - n: number of polynomial commitments
-- | - f: the field type
type CheckBulletproofInput d n f =
  { xi :: SizedF 128 (FVar f) -- ^ Batching scalar (128 bits)
  , advice ::
      { b :: FVar f -- ^ b = bPoly(chals, zeta) + u * bPoly(chals, zetaOmega)
      , combinedInnerProduct :: FVar f -- ^ Combined evaluation of all polynomials
      }
  , commitments :: Vector n (AffinePoint (FVar f)) -- ^ Polynomial commitments to combine
  , opening ::
      { lr :: Vector d (Tuple (AffinePoint (FVar f)) (AffinePoint (FVar f))) -- ^ L/R pairs
      , delta :: AffinePoint (FVar f) -- ^ Delta commitment from opening proof
      , z1 :: Type2 (FVar f) (BoolVar f) -- ^ Opening proof scalar z1
      , z2 :: Type2 (FVar f) (BoolVar f) -- ^ Opening proof scalar z2
      , sg :: AffinePoint (FVar f) -- ^ Challenge polynomial commitment (deferred)
      }
  , h :: AffinePoint (FVar f) -- ^ SRS H generator
  , groupMapParams :: GroupMapParams f -- ^ BW19 group map parameters
  }

-- | Output of the bulletproof verifier circuit
type CheckBulletproofOutput d f =
  { challenges :: Vector d (SizedF 128 f) -- ^ IPA challenges (for deferred sg verification)
  }

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
-- | Bullet Reduce (In-Circuit)
--------------------------------------------------------------------------------

-- | The L/R reduction loop for IPA verification.
-- |
-- | For each (L, R) pair:
-- | 1. Absorb L.x, L.y, R.x, R.y into the sponge
-- | 2. Squeeze a scalar challenge
-- | 3. Compute term = endoInv(L, chal) + endo(R, chal)
-- | 4. Accumulate into lrProd
-- |
-- | Returns the accumulated lrProd and all challenges.
-- |
-- | Note: Requires d >= 1 (at least one L/R pair). This is always true for
-- | valid IPA proofs since d is the domain log2.
bulletReduce
  :: forall @d @d' @g f f' t m
   . Reflectable d Int
  => Add 1 d' d
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => HasEndo f f'
  => FrModule f' g
  => WeierstrassCurve f g
  => PrimeField f
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Vector d (Tuple (AffinePoint (FVar f)) (AffinePoint (FVar f)))
  -> SpongeM f (KimchiConstraint f) t m (BulletReduceResult d (FVar f))
bulletReduce lrPairs = do
  -- Process each L/R pair, accumulating terms and collecting challenges
  Tuple challenges terms <- Vector.unzip <$> traverse reducePair lrPairs

  -- Sum all terms to get lrProd
  -- uncons is safe here because d >= 1 (enforced by Add 1 d' d constraint)
  let { head, tail } = uncons terms
  lrProd <- liftSnarky $ foldM (\x y -> _.p <$> addComplete x y) head tail

  pure { lrProd, challenges }

  where
  -- Process a single L/R pair
  reducePair
    :: Tuple (AffinePoint (FVar f)) (AffinePoint (FVar f))
    -> SpongeM f (KimchiConstraint f) t m (Tuple (SizedF 128 (FVar f)) (AffinePoint (FVar f)))
  reducePair (Tuple l r) = do
    -- Absorb L and R into the sponge
    absorbPoint l
    absorbPoint r

    -- Squeeze a scalar challenge (128 bits)
    challenge :: SizedF 128 (FVar f) <- squeezeScalarChallenge

    -- Compute term = endoInv(L, chal) + endo(R, chal)
    liftSnarky $ do
      termL <- endoInv @f @f' @g l challenge
      termR <- endo r challenge
      { p: term } <- addComplete termL termR
      pure $ Tuple challenge term

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
  => SizedF 128 (FVar f) -- ^ xi (scalar challenge, 128 bits)
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

--------------------------------------------------------------------------------
-- | Check Bulletproof (Main Verifier Circuit)
--------------------------------------------------------------------------------

-- | The main bulletproof verification circuit.
-- |
-- | Verifies the IPA opening equation:
-- |   c*Q + delta = z1*(sg + b*U) + z2*H
-- |
-- | Where:
-- | - Q = combined_polynomial + cip*U + lr_prod
-- | - U = groupMap(squeeze(sponge)) after absorbing cip
-- | - c = scalar challenge squeezed after absorbing delta
-- |
-- | Returns the challenges for the deferred sg verification.
-- |
-- | Algorithm (from mina's step_verifier.ml):
-- | 1. Absorb combined_inner_product into sponge
-- | 2. u = group_map(squeeze(sponge))
-- | 3. combined_polynomial = combineSplitCommitments(xi, commitments)
-- | 4. (lr_prod, challenges) = bullet_reduce(sponge, lr)
-- | 5. p_prime = combined_polynomial + scaleFast2(u, cip)
-- | 6. q = p_prime + lr_prod
-- | 7. Absorb delta into sponge
-- | 8. c = squeeze_scalar(sponge)
-- | 9. LHS = endo(q, c) + delta
-- | 10. RHS = scaleFast2(sg + scaleFast2(u, b), z1) + scaleFast2(h, z2)
-- | 11. Assert LHS == RHS
-- | 12. Return challenges
checkBulletproof
  :: forall @d @d' @n @n' @nChunks f f' g t m
   . Reflectable d Int
  => Reflectable n Int
  => Add 1 d' d
  => Add 1 n' n
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => Mul 5 nChunks 255
  => Reflectable nChunks Int
  => HasEndo f f'
  => FrModule f' g
  => WeierstrassCurve f g
  => HasSqrt f
  => PrimeField f
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => CheckBulletproofInput d n f
  -> SpongeM f (KimchiConstraint f) t m (CheckBulletproofOutput d (FVar f))
checkBulletproof input = do
  -- Step 1: Absorb combined_inner_product into sponge
  absorb input.advice.combinedInnerProduct

  -- Step 2: u = group_map(squeeze(sponge))
  squeezed <- squeeze
  u <- liftSnarky $ groupMapCircuit input.groupMapParams squeezed

  -- Step 3: combined_polynomial = combineSplitCommitments(xi, commitments)
  combined <- liftSnarky $ combineSplitCommitments @n input.xi input.commitments

  -- Step 4: (lr_prod, challenges) = bullet_reduce(sponge, lr)
  { lrProd, challenges } <- bulletReduce @d @_ @g input.opening.lr

  -- Step 5: p_prime = combined + scaleFast2(u, cip)
  cipType2 <- liftSnarky $ splitFieldVar input.advice.combinedInnerProduct
  uTimesCip <- liftSnarky $ scaleFast2 @nChunks u cipType2
  { p: pPrime } <- liftSnarky $ addComplete combined uTimesCip

  -- Step 6: q = p_prime + lr_prod
  { p: q } <- liftSnarky $ addComplete pPrime lrProd

  -- Step 7: Absorb delta into sponge
  absorbPoint input.opening.delta

  -- Step 8: c = squeeze_scalar(sponge) (128 bits for endo)
  c :: SizedF 128 (FVar f) <- squeezeScalarChallenge
  liftSnarky $ do
    -- Step 9: LHS = endo(q, c) + delta
    qTimesC <- endo q c
    { p: lhs } <- addComplete qTimesC input.opening.delta

    -- Step 10: RHS = scaleFast2(sg + scaleFast2(u, b), z1) + scaleFast2(h, z2)
    bType2 <- splitFieldVar input.advice.b
    uTimesB <- scaleFast2 @nChunks u bType2
    { p: sgPlusUB } <- addComplete input.opening.sg uTimesB
    term1 <- scaleFast2 @nChunks sgPlusUB input.opening.z1
    term2 <- scaleFast2 @nChunks input.h input.opening.z2
    { p: rhs } <- addComplete term1 term2

    -- Step 11: Assert LHS == RHS
    EllipticCurve.assertEqual lhs rhs

    -- Step 12: Return challenges (for deferred sg verification)
    pure { challenges }