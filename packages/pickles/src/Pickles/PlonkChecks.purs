-- | Composed PLONK verification checks.
-- |
-- | This module composes xi_correct and combined_inner_product_correct into a single
-- | circuit that operates entirely in the native circuit field (no cross-field conversions).
-- |
-- | The circuit stays in `SpongeM` to allow the caller to continue using the sponge
-- | state for subsequent operations (e.g., IPA verification).
-- |
-- | Reference: step_main.ml (the verification checks before IPA)
module Pickles.PlonkChecks
  ( PlonkChecksInput
  , PlonkChecksOutput
  , plonkChecksCircuit
  ) where

import Prelude

import Data.Foldable (traverse_)
import Data.Vector (Vector)
import Pickles.Linearization (LinearizationPoly)
import Pickles.Linearization.FFI (PointEval)
import Pickles.PlonkChecks.CombinedInnerProduct (CombinedInnerProductCheckInput, combinedInnerProductCheckCircuit)
import Pickles.Sponge (class MonadSponge, SpongeM, absorb, liftSnarky, squeezeScalarChallenge)
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (class CircuitM, FVar, assertEqual_)
import Snarky.Circuit.Kimchi.EndoScalar (toField)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, class PrimeField)

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | Input for the composed PLONK checks circuit.
-- |
-- | All values are in the native circuit field `f`.
type PlonkChecksInput f =
  { -- Fr-sponge inputs (already absorbed: fqDigest, prevChallengeDigest)
    -- The sponge should be in state ready to absorb ftEval1
    ftEval1 :: f
  , publicEvals :: PointEval f
  , zEvals :: PointEval f
  , indexEvals :: Vector 6 (PointEval f)
  , witnessEvals :: Vector 15 (PointEval f)
  , coeffEvals :: Vector 15 (PointEval f)
  , sigmaEvals :: Vector 6 (PointEval f)
  -- Endo coefficient for scalar challenge conversion
  , endo :: f
  -- Claimed xi to verify
  , claimedXi :: f
  -- For combined inner product computation
  , cipInput :: CombinedInnerProductCheckInput f
  }

-- | Output from PLONK checks, providing values for IPA verification.
-- |
-- | All values are native circuit field elements.
type PlonkChecksOutput f =
  { polyscale :: f -- xi, for combining commitments
  , evalscale :: f -- r, for combining evaluations
  , combinedInnerProduct :: f -- the batched evaluation sum
  }

-------------------------------------------------------------------------------
-- | Circuit
-------------------------------------------------------------------------------

-- | Composed PLONK verification circuit.
-- |
-- | This circuit stays in `SpongeM` so the caller can continue using the sponge
-- | for IPA verification (which needs to squeeze for u, absorb L/R pairs, etc.).
-- |
-- | The sponge should be initialized with fqDigest and prevChallengeDigest
-- | already absorbed before calling this circuit.
-- |
-- | Operations:
-- | 1. Absorb evaluations into Fr-sponge (ftEval1, publicEvals, all poly evals)
-- | 2. Squeeze and derive xi (polyscale)
-- | 3. Assert xi matches claimed value
-- | 4. Squeeze and derive evalscale (r)
-- | 5. Compute combined_inner_product using derived values
-- |
-- | Note: b_correct is NOT done here - it belongs in IPA verification where
-- | the challenge derivation context is clear.
plonkChecksCircuit
  :: forall f f' t m
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => HasEndo f f'
  => CircuitM f (KimchiConstraint f) t m
  => LinearizationPoly f
  -> PlonkChecksInput (FVar f)
  -> SpongeM f (KimchiConstraint f) t m (PlonkChecksOutput (FVar f))
plonkChecksCircuit linPoly input = do
  -- 1. Absorb ftEval1
  absorb input.ftEval1

  -- 2. Absorb public evals (zeta, then zeta_omega)
  absorb input.publicEvals.zeta
  absorb input.publicEvals.omegaTimesZeta

  -- 3. Absorb all polynomial evaluations in Kimchi's order
  -- Order: z, selectors (6), witness (15), coefficients (15), sigma (6)
  absorbPointEval input.zEvals
  traverse_ absorbPointEval input.indexEvals
  traverse_ absorbPointEval input.witnessEvals
  traverse_ absorbPointEval input.coeffEvals
  traverse_ absorbPointEval input.sigmaEvals

  -- 4. Squeeze scalar challenge and derive xi (polyscale)
  rawXi <- squeezeScalarChallenge
  polyscale <- liftSnarky $ toField rawXi input.endo

  -- 5. Assert xi matches claimed value
  liftSnarky $ assertEqual_ polyscale input.claimedXi

  -- 6. Squeeze scalar challenge and derive evalscale (r)
  rawR <- squeezeScalarChallenge
  evalscale <- liftSnarky $ toField rawR input.endo

  -- 7. Compute combined inner product using derived values
  combinedInnerProduct <- liftSnarky $
    combinedInnerProductCheckCircuit linPoly
      { polyscale, evalscale }
      input.cipInput

  pure { polyscale, evalscale, combinedInnerProduct }

-- | Helper: absorb a PointEval (zeta then zeta_omega)
absorbPointEval
  :: forall f m
   . MonadSponge f m
  => PointEval f
  -> m Unit
absorbPointEval pe = do
  absorb pe.zeta
  absorb pe.omegaTimesZeta
