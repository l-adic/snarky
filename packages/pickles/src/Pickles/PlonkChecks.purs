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
  ( -- * Evaluation Types
    AllEvals
  , ChunkedAllEvals
  , extractEvalFields
  , absorbAllEvals
  , absorbPointEval
  , module Pickles.PlonkChecks.Permutation
  ) where

import Prelude

import Data.Array.NonEmpty (NonEmptyArray)
import Data.Foldable (traverse_)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.Linearization.FFI (PointEval)
import Pickles.PlonkChecks.Permutation (PermutationInput)
import Pickles.Sponge (class MonadSponge, absorb)

-------------------------------------------------------------------------------
-- | Evaluation Types
-------------------------------------------------------------------------------

-- | All polynomial evaluations at zeta and zeta*omega.
-- |
-- | These are the witness values needed for PLONK verification.
-- | The sizes match Kimchi's configuration:
-- | - ft polynomial (only at zeta*omega, ftEval0 is computed)
-- | - 6 selector (index) polynomials
-- | - 15 witness columns
-- | - 15 coefficient columns
-- | - 6 sigma polynomials (PERMUTS - 1)
-- |
-- | Each `PointEval` here is the COLLAPSED (single-chunk) form produced
-- | by `Pickles.PlonkChecks.Chunks.collapsePointEval` — chunks recombined
-- | via Horner at `pt^(2^rounds)`. Used by ftEval0, derivePlonk, and any
-- | other code path that consumes a polynomial's value at zeta / zetaw.
-- |
-- | For the COMBINED INNER PRODUCT specifically, the original CHUNKED
-- | evals must be xi-batched (`Pcs_batch.combine_split_evaluations`);
-- | see `ChunkedAllEvals` below.
-- |
-- | Reference: Plonk_types.All_evals in composition_types.ml
type AllEvals f =
  { ftEval1 :: f -- ft polynomial eval at zeta*omega (ftEval0 is computed)
  , publicEvals :: PointEval f
  , zEvals :: PointEval f
  , indexEvals :: Vector 6 (PointEval f)
  , witnessEvals :: Vector 15 (PointEval f)
  , coeffEvals :: Vector 15 (PointEval f)
  , sigmaEvals :: Vector 6 (PointEval f)
  }

-- | The CHUNKED form of `AllEvals`: each polynomial's evaluation at zeta
-- | / zeta·omega is a `NonEmptyArray (PointEval f)` with one entry per
-- | chunk. For an inner proof at num_chunks=1 each array has length 1
-- | (and `combinedInnerProductBatchChunked` collapses to the same result
-- | as the legacy single-eval `combinedInnerProductBatch`); for chunks2
-- | (step num_chunks=2) each polynomial contributes 2 chunks.
-- |
-- | OCaml stores these as `(f array * f array)` per polynomial inside
-- | `Plonk_types.Evals.t` (`wrap.ml:25-26`). The xi-batching
-- | `Pcs_batch.combine_split_evaluations` flattens the chunk arrays and
-- | folds right-to-left with `acc' = chunk + xi * acc`.
type ChunkedAllEvals f =
  { ftEval1 :: f
  , publicEvals :: NonEmptyArray (PointEval f)
  , zEvals :: NonEmptyArray (PointEval f)
  , indexEvals :: Vector 6 (NonEmptyArray (PointEval f))
  , witnessEvals :: Vector 15 (NonEmptyArray (PointEval f))
  , coeffEvals :: Vector 15 (NonEmptyArray (PointEval f))
  , sigmaEvals :: Vector 6 (NonEmptyArray (PointEval f))
  }

-- | Extract the 43 always-present evaluation fields in CIP order:
-- | z(1), index(6), witness(15), coeff(15), sigma(6).
extractEvalFields :: forall f. (PointEval f -> f) -> AllEvals f -> Vector 43 f
extractEvalFields proj evals =
  proj evals.zEvals :<
    map proj evals.indexEvals
      `Vector.append` map proj evals.witnessEvals
      `Vector.append` map proj evals.coeffEvals
      `Vector.append` map proj evals.sigmaEvals

-- | Absorb all polynomial evaluations into the sponge.
-- |
-- | Follows Kimchi's absorption order:
-- | ftEval1, public, z, index (6), witness (15), coeff (15), sigma (6)
absorbAllEvals
  :: forall f m
   . MonadSponge f m
  => AllEvals f
  -> m Unit
absorbAllEvals evals = do
  absorb evals.ftEval1
  absorbPointEval evals.publicEvals
  absorbPointEval evals.zEvals
  traverse_ absorbPointEval evals.indexEvals
  traverse_ absorbPointEval evals.witnessEvals
  traverse_ absorbPointEval evals.coeffEvals
  traverse_ absorbPointEval evals.sigmaEvals

-------------------------------------------------------------------------------
-- | PlonkChecks Types
-------------------------------------------------------------------------------

-- | Input for the composed PLONK checks circuit.
-- |
-- | All values are in the native circuit field `f`.
-- | The sponge should already have fqDigest and prevChallengeDigest absorbed.
-- |
-- | Note: `claimedXi` and `claimedR` are 128-bit scalar challenges, NOT full
-- | field elements. The comparison happens on the raw 128-bit values, then
-- | we convert to full field via endo for use in CIP computation.
-- |
-- | Helper: absorb a PointEval (zeta then zeta_omega)
absorbPointEval
  :: forall f m
   . MonadSponge f m
  => PointEval f
  -> m Unit
absorbPointEval pe = do
  absorb pe.zeta
  absorb pe.omegaTimesZeta

