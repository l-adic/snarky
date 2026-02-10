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
  , absorbAllEvals
  -- * PlonkChecks Circuit
  , PlonkChecksInput
  , PlonkChecksOutput
  , plonkChecksCircuit
  , PlonkArithmeticCheckInput
  , plonkArithmeticCheckCircuit
  ) where

import Prelude

import Data.Foldable (traverse_)
import Data.Vector (Vector)
import Pickles.Linearization (LinearizationPoly)
import Pickles.Linearization.FFI (PointEval)
import Pickles.PlonkChecks.CombinedInnerProduct (CombinedInnerProductCheckInput, combinedInnerProductCheckCircuit)
import Pickles.PlonkChecks.Permutation (PermutationInput, permScalarCircuit)
import Pickles.Sponge (class MonadSponge, SpongeM, absorb, liftSnarky, squeezeScalarChallenge)
import Pickles.Step.Types (ScalarChallenge)
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, assertEq, equals_)
import Snarky.Circuit.Kimchi (toField)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, class PrimeField)

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
-- | Reference: step_verifier.ml - xi_correct compares raw scalar challenges
type PlonkChecksInput f =
  { -- Polynomial evaluations (includes ftEval1)
    allEvals :: AllEvals f
  -- EndoScalar coefficient for scalar challenge expansion (= Wrap_inner_curve.scalar)
  , endo :: f
  -- Claimed xi (polyscale) to verify - 128-bit scalar challenge
  , claimedXi :: ScalarChallenge f
  -- Claimed r (evalscale) to verify - 128-bit scalar challenge
  , claimedR :: ScalarChallenge f
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
-- | 2. Squeeze xi (polyscale) as 128-bit scalar challenge
-- | 3. Assert raw xi matches claimed value (128-bit comparison)
-- | 4. Convert xi to full field via endo for CIP use
-- | 5. Squeeze r (evalscale) as 128-bit scalar challenge
-- | 6. Assert raw r matches claimed value (128-bit comparison)
-- | 7. Convert r to full field via endo for CIP use
-- | 8. Compute combined_inner_product using derived polyscale/evalscale
-- |
-- | Note: b_correct is NOT done here - it belongs in IPA verification where
-- | the challenge derivation context is clear.
-- |
-- | Reference: step_verifier.ml - xi_correct and r comparisons happen on raw
-- | 128-bit scalar challenges, NOT on endo-converted full field elements.
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
  -- 1. Absorb all polynomial evaluations in Kimchi's order
  absorbAllEvals input.allEvals

  -- 2. Squeeze scalar challenge (128-bit) for xi
  rawXi <- squeezeScalarChallenge

  -- 3. Assert raw xi matches claimed value (128-bit comparison)
  -- This is xi_correct from OCaml - compares raw scalar challenges
  liftSnarky $ assertEq rawXi input.claimedXi

  -- 4. Convert to full field via endo for CIP computation
  polyscale <- liftSnarky $ toField rawXi input.endo

  -- 5. Squeeze scalar challenge (128-bit) for evalscale (r)
  rawR <- squeezeScalarChallenge

  -- 6. Assert raw r matches claimed value (128-bit comparison)
  liftSnarky $ assertEq rawR input.claimedR

  -- 7. Convert to full field via endo for CIP computation
  evalscale <- liftSnarky $ toField rawR input.endo

  -- 8. Compute combined inner product using derived values
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

-------------------------------------------------------------------------------
-- | Plonk Arithmetic Check
-------------------------------------------------------------------------------

-- | Input for plonk arithmetic check circuit.
-- |
-- | This check verifies that the claimed `perm` value matches the value
-- | computed from the challenges and evaluations. The `perm` scalar is
-- | the coefficient of z(x) in the linearization polynomial.
-- |
-- | Reference: plonk_checks.ml:450-476 `checked`
type PlonkArithmeticCheckInput f sf =
  { -- | Claimed permutation scalar (shifted)
    claimedPerm :: sf
  -- | Input for computing the actual perm scalar
  , permInput :: PermutationInput f
  }

-- | Check that the claimed perm value matches the computed value.
-- |
-- | This is the PureScript equivalent of `Plonk_checks.checked` in OCaml.
-- | Currently only checks `perm` (the only value checked in OCaml as of now).
-- |
-- | The check:
-- | 1. Computes the actual perm scalar from challenges and evaluations
-- | 2. Unshifts the claimed perm value via the provided `unshift` operation
-- | 3. Returns whether they're equal
-- |
-- | Reference: plonk_checks.ml:450-476
plonkArithmeticCheckCircuit
  :: forall f n t m sf r
   . PrimeField f
  => FieldSizeInBits f n
  => CircuitM f (KimchiConstraint f) t m
  => { unshift :: sf -> FVar f | r }
  -> PlonkArithmeticCheckInput (FVar f) sf
  -> Snarky (KimchiConstraint f) t m (BoolVar f)
plonkArithmeticCheckCircuit ops input = do
  -- Compute actual perm from challenges and evaluations
  actualPerm <- permScalarCircuit input.permInput

  -- Unshift the claimed perm value
  let claimedPermUnshifted = ops.unshift input.claimedPerm

  -- Compare: claimed (unshifted) == actual
  equals_ claimedPermUnshifted actualPerm
