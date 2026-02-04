-- | Xi (polyscale) and evalscale correctness checks for PLONK verification.
-- |
-- | This module provides the `xi_correct` and `r_correct` checks from `step_main`:
-- | Verify that the claimed xi (polyscale) and r (evalscale) values were correctly
-- | derived via Fiat-Shamir by replaying the Fr-sponge absorptions and comparing
-- | the squeezed+endo-mapped results against the claimed values.
-- |
-- | Fr-sponge protocol for xi and r:
-- | 1. absorb(fq_digest)           -- Fq-sponge state at zeta derivation
-- | 2. absorb(prev_challenge_digest) -- digest of previous recursion challenges
-- | 3. absorb(ft_eval1)            -- ft poly eval at zeta*omega
-- | 4. absorb(public_evals)        -- public input poly evals at both points
-- | 5. absorb(all_poly_evals)      -- in Kimchi's specific order
-- | 6. squeeze() -> raw_xi_challenge
-- | 7. endo_map(raw_xi_challenge) -> xi
-- | 8. squeeze() -> raw_r_challenge
-- | 9. endo_map(raw_r_challenge) -> r (evalscale)
-- |
-- | Reference: mina/src/lib/pickles/step_verifier.ml (lines 946-954)
module Pickles.PlonkChecks.XiCorrect
  ( XiCorrectInput
  , FrSpongeChallenges
  , xiCorrectCircuit
  , xiCorrectPure
  , frSpongeChallengesPure
  , emptyPrevChallengeDigest
  ) where

import Prelude

import Data.Foldable (traverse_)
import Data.Newtype (unwrap)
import Data.Vector (Vector)
import Pickles.Linearization.FFI (PointEval)
import Pickles.Sponge (class MonadSponge, PureSpongeM, SpongeM, absorb, evalPureSpongeM, initialSponge, liftSnarky, squeezeScalarChallenge, squeezeScalarChallengePure)
import Poseidon (class PoseidonField)
import RandomOracle.Sponge as PureSponge
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky, assertEqual_)
import Snarky.Circuit.Kimchi.EndoScalar (toField, toFieldPure)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Snarky.Data.SizedF (coerceViaBits)

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | Input for the xi/evalscale correctness check.
-- |
-- | The absorption order matches Kimchi's Fr-sponge protocol exactly:
-- | fq_digest, prev_challenge_digest, ft_eval1, public_evals, then all poly evals
-- | in the order: z, selectors (6), witness (15), coefficients (15), sigma (6).
type XiCorrectInput f =
  { -- Initial Fr-sponge inputs (from Fq-sponge / recursion)
    fqDigest :: f -- Fq-sponge digest before Fr-sponge
  , prevChallengeDigest :: f -- digest of previous recursion challenges (zero for base case)
  -- Polynomial evaluations to absorb
  , ftEval1 :: f -- ft poly eval at zeta*omega
  , publicEvals :: PointEval f -- public input poly evals
  , zEvals :: PointEval f -- Z poly evals
  , indexEvals :: Vector 6 (PointEval f) -- selector poly evals (Generic, Poseidon, CompleteAdd, VarBaseMul, EndoMul, EndoMulScalar)
  , witnessEvals :: Vector 15 (PointEval f) -- witness column evals
  , coeffEvals :: Vector 15 (PointEval f) -- coefficient column evals
  , sigmaEvals :: Vector 6 (PointEval f) -- sigma poly evals
  -- Endomorphism coefficient
  , endo :: f
  -- Value to verify
  , claimedXi :: f -- the xi (polyscale/v) value to verify
  }

-- | Result of Fr-sponge challenge derivation.
-- | Contains both xi (polyscale) and r (evalscale) values.
type FrSpongeChallenges f =
  { xi :: f -- polyscale (first squeeze)
  , evalscale :: f -- evalscale/r (second squeeze)
  }

-------------------------------------------------------------------------------
-- | Circuit computation
-------------------------------------------------------------------------------

-- | Verify xi correctness in-circuit and derive both xi and evalscale.
-- |
-- | This circuit stays in `SpongeM` so the caller can continue using the sponge
-- | for subsequent operations (e.g., absorbing combined_inner_product for IPA).
-- |
-- | The sponge should be in its initial state when this is called.
-- |
-- | Operations:
-- | 1. Absorb fq_digest and prev_challenge_digest
-- | 2. Absorb ft_eval1, public_evals, all poly evals
-- | 3. Squeeze and derive xi (polyscale)
-- | 4. Assert xi matches claimed value
-- | 5. Squeeze and derive evalscale (r)
-- | 6. Return both derived values
xiCorrectCircuit
  :: forall f t m
   . PrimeField f
  => PoseidonField f
  => FieldSizeInBits f 255
  => CircuitM f (KimchiConstraint f) t m
  => XiCorrectInput (FVar f)
  -> SpongeM f (KimchiConstraint f) t m (FrSpongeChallenges (FVar f))
xiCorrectCircuit input = do
  -- 1. Absorb fq_digest and prev_challenge_digest
  absorb input.fqDigest
  absorb input.prevChallengeDigest

  -- 2. Absorb ft_eval1
  absorb input.ftEval1

  -- 3. Absorb public evals (zeta, then zeta_omega)
  absorb input.publicEvals.zeta
  absorb input.publicEvals.omegaTimesZeta

  -- 4. Absorb all polynomial evaluations in Kimchi's order
  absorbEvaluations input

  -- 5. Squeeze scalar challenge (128 bits) and derive xi
  rawXi <- squeezeScalarChallenge
  xi <- liftSnarky $ toField rawXi input.endo

  -- 6. Assert equality with claimed xi
  liftSnarky $ assertEqual_ xi input.claimedXi

  -- 7. Squeeze scalar challenge for evalscale (r)
  rawR <- squeezeScalarChallenge
  evalscale <- liftSnarky $ toField rawR input.endo

  pure { xi, evalscale }

-- | Helper: absorb all polynomial evaluations in Kimchi's order.
-- | Order: z, selectors (6), witness (15), coefficients (15), sigma (6)
absorbEvaluations
  :: forall f c t m
   . MonadSponge (FVar f) (SpongeM f c t m)
  => Monad (Snarky c t m)
  => XiCorrectInput (FVar f)
  -> SpongeM f c t m Unit
absorbEvaluations input = do
  -- z polynomial
  absorbPointEval input.zEvals

  -- 6 selector polynomials
  traverse_ absorbPointEval input.indexEvals

  -- 15 witness polynomials
  traverse_ absorbPointEval input.witnessEvals

  -- 15 coefficient polynomials
  traverse_ absorbPointEval input.coeffEvals

  -- 6 sigma polynomials
  traverse_ absorbPointEval input.sigmaEvals

-- | Helper: absorb a PointEval (zeta then zeta_omega)
absorbPointEval
  :: forall f m
   . MonadSponge f m
  => PointEval f
  -> m Unit
absorbPointEval pe = do
  absorb pe.zeta
  absorb pe.omegaTimesZeta

-------------------------------------------------------------------------------
-- | Pure computation (for testing)
-------------------------------------------------------------------------------

-- | Pure version of xi correctness check.
-- | Returns the computed xi for comparison.
xiCorrectPure
  :: forall f
   . PrimeField f
  => PoseidonField f
  => FieldSizeInBits f 255
  => XiCorrectInput f
  -> f
xiCorrectPure input = (frSpongeChallengesPure input).xi

-- | Compute both Fr-sponge challenges (xi and evalscale) from the proof data.
-- |
-- | This implements the full Fr-sponge protocol:
-- | 1. Absorb all inputs (fq_digest, prev_challenge_digest, ft_eval1, evals)
-- | 2. Squeeze for xi (polyscale)
-- | 3. Squeeze for r (evalscale)
-- |
-- | Reference: mina/src/lib/pickles/step_verifier.ml (lines 946-954)
frSpongeChallengesPure
  :: forall f
   . PrimeField f
  => PoseidonField f
  => FieldSizeInBits f 255
  => XiCorrectInput f
  -> FrSpongeChallenges f
frSpongeChallengesPure input =
  evalPureSpongeM initialSponge do
    -- 1. Absorb fq_digest and prev_challenge_digest
    absorb input.fqDigest
    absorb input.prevChallengeDigest

    -- 2. Absorb ft_eval1
    absorb input.ftEval1

    -- 3. Absorb public evals
    absorb input.publicEvals.zeta
    absorb input.publicEvals.omegaTimesZeta

    -- 4. Absorb all polynomial evaluations
    absorbEvaluationsPure input

    -- 5. Squeeze scalar challenge for xi
    rawXi <- squeezeScalarChallengePure
    let xi = unwrap $ toFieldPure (coerceViaBits rawXi) input.endo

    -- 6. Squeeze scalar challenge for r (evalscale)
    rawR <- squeezeScalarChallengePure
    let evalscale = unwrap $ toFieldPure (coerceViaBits rawR) input.endo

    pure { xi, evalscale }

-- | Helper: absorb all polynomial evaluations (pure version)
absorbEvaluationsPure
  :: forall f
   . PoseidonField f
  => XiCorrectInput f
  -> PureSpongeM f Unit
absorbEvaluationsPure input = do
  -- z polynomial
  absorbPointEval input.zEvals

  -- 6 selector polynomials
  traverse_ absorbPointEval input.indexEvals

  -- 15 witness polynomials
  traverse_ absorbPointEval input.witnessEvals

  -- 15 coefficient polynomials
  traverse_ absorbPointEval input.coeffEvals

  -- 6 sigma polynomials
  traverse_ absorbPointEval input.sigmaEvals

-------------------------------------------------------------------------------
-- | Helpers
-------------------------------------------------------------------------------

-- | Compute the prev_challenge_digest for the base case (no previous recursion).
-- | This is the digest of an empty Fr-sponge (squeeze from initial state).
emptyPrevChallengeDigest :: forall f. PoseidonField f => f
emptyPrevChallengeDigest =
  let
    { result } = PureSponge.squeeze (initialSponge :: PureSponge.Sponge f)
  in
    result
