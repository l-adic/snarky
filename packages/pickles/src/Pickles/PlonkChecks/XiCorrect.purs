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
  ( FrSpongeInput
  , XiCorrectInput
  , FrSpongeChallenges
  , frSpongeChallengesPure
  ) where

import Prelude

import Data.Foldable (traverse_)
import Data.Vector (Vector)
import Pickles.Linearization.FFI (PointEval)
import Pickles.Sponge (class MonadSponge, PureSpongeM, absorb, evalPureSpongeM, initialSponge, squeezeScalarChallengePure)
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (SizedF, coerceViaBits)
import Snarky.Circuit.Kimchi (toFieldPure)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | Input for Fr-sponge challenge computation.
-- |
-- | The absorption order matches Kimchi's Fr-sponge protocol exactly:
-- | fq_digest, prev_challenge_digest, ft_eval1, public_evals, then all poly evals
-- | in the order: z, selectors (6), witness (15), coefficients (15), sigma (6).
type FrSpongeInput f =
  { -- Initial Fr-sponge inputs (from Fq-sponge / recursion)
    fqDigest :: f -- Fq-sponge digest before Fr-sponge
  , prevChallengeDigest :: f -- digest of previous recursion challenges (zero for base case)
  -- Polynomial evaluations to absorb
  , ftEval1 :: f -- ft poly eval at zeta*omega
  , publicEvals :: PointEval f -- public input poly evals
  , zEvals :: PointEval f -- Z poly evals
  , indexEvals :: Vector 6 (PointEval f) -- selector poly evals
  , witnessEvals :: Vector 15 (PointEval f) -- witness column evals
  , coeffEvals :: Vector 15 (PointEval f) -- coefficient column evals
  , sigmaEvals :: Vector 6 (PointEval f) -- sigma poly evals
  -- Endomorphism coefficient for scalar challenge expansion
  , endo :: f -- ^ EndoScalar coefficient (= G::endos().1 = endo_r, for challenge expansion)
  }

-- | Input for xi_correct circuit verification.
-- |
-- | Extends FrSpongeInput with the claimed xi value to verify.
-- | Note: `claimedXi` is a 128-bit scalar challenge, NOT a full field element.
-- | The comparison happens on raw 128-bit values, matching OCaml's xi_correct.
type XiCorrectInput f =
  { fqDigest :: f
  , prevChallengeDigest :: f
  , ftEval1 :: f
  , publicEvals :: PointEval f
  , zEvals :: PointEval f
  , indexEvals :: Vector 6 (PointEval f)
  , witnessEvals :: Vector 15 (PointEval f)
  , coeffEvals :: Vector 15 (PointEval f)
  , sigmaEvals :: Vector 6 (PointEval f)
  , endo :: f -- ^ EndoScalar coefficient (= G::endos().1 = endo_r, for challenge expansion)
  -- Value to verify - 128-bit scalar challenge (NOT full field element)
  , claimedXi :: SizedF 128 f
  }

-- | Result of Fr-sponge challenge derivation.
-- | Contains both raw 128-bit scalar challenges and endo-expanded full field values.
-- | Raw values are used for xi_correct/r_correct verification (comparing 128-bit challenges).
-- | Expanded values are used for CIP computation.
type FrSpongeChallenges f =
  { rawXi :: SizedF 128 f -- raw 128-bit xi challenge (for verification)
  , xi :: f -- endo-expanded polyscale (for CIP)
  , rawR :: SizedF 128 f -- raw 128-bit r challenge (for verification)
  , evalscale :: f -- endo-expanded evalscale (for CIP)
  }

-- | Helper: absorb a PointEval (zeta then zeta_omega)
absorbPointEval
  :: forall f m
   . MonadSponge f m
  => PointEval f
  -> m Unit
absorbPointEval pe = do
  absorb pe.zeta
  absorb pe.omegaTimesZeta

frSpongeChallengesPure
  :: forall f
   . PrimeField f
  => PoseidonField f
  => FieldSizeInBits f 255
  => FrSpongeInput f
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

    -- 5. Squeeze scalar challenge for xi (raw 128-bit)
    rawXi <- squeezeScalarChallengePure

    -- 6. Squeeze scalar challenge for r (raw 128-bit)
    rawR <- squeezeScalarChallengePure

    -- 7. Expand to full field via endo for CIP use
    let
      xi = toFieldPure (coerceViaBits rawXi) input.endo
      evalscale = toFieldPure (coerceViaBits rawR) input.endo

    pure { rawXi, xi, rawR, evalscale }

-- | Helper: absorb all polynomial evaluations (pure version)
absorbEvaluationsPure
  :: forall f r
   . PoseidonField f
  => { zEvals :: PointEval f
     , indexEvals :: Vector 6 (PointEval f)
     , witnessEvals :: Vector 15 (PointEval f)
     , coeffEvals :: Vector 15 (PointEval f)
     , sigmaEvals :: Vector 6 (PointEval f)
     | r
     }
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
