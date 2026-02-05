-- | Witness data for verifying a Wrap proof in the Step circuit.
-- |
-- | When the Step circuit verifies a previous Wrap proof, it needs:
-- | 1. Deferred values (from `UnfinalizedProof` - part of public input)
-- | 2. Polynomial evaluations (private witness)
-- | 3. IPA opening proof components (private witness)
-- |
-- | This module defines the witness types for items 2 and 3.
-- |
-- | Reference: mina/src/lib/pickles/step_verifier.ml (finalize_other_proof)
module Pickles.Step.WrapProofWitness
  ( -- * Polynomial Evaluations
    AllEvals
  -- * IPA Opening Proof
  , LrPair
  , OpeningProof
  -- * Complete Witness
  , WrapProofWitness
  -- * Verifier Data (from verification key)
  , VerifierData
  ) where

import Data.Vector (Vector)
import Pickles.Linearization.FFI (PointEval)
import Snarky.Data.EllipticCurve (AffinePoint)

-------------------------------------------------------------------------------
-- | L/R Pair from IPA
-------------------------------------------------------------------------------

-- | A pair of L and R commitment points from an IPA round.
-- | These are curve points on the commitment curve.
type LrPair f = { l :: AffinePoint f, r :: AffinePoint f }

-------------------------------------------------------------------------------
-- | Polynomial Evaluations
-------------------------------------------------------------------------------

-- | All polynomial evaluations at zeta and zeta*omega.
-- |
-- | These are the witness values needed for PlonkChecks verification.
-- | The sizes match Kimchi's configuration:
-- | - 6 selector (index) polynomials
-- | - 15 witness columns
-- | - 15 coefficient columns
-- | - 6 sigma polynomials (PERMUTS - 1)
-- |
-- | Reference: Plonk_types.All_evals in composition_types.ml
type AllEvals f =
  { publicEvals :: PointEval f
  , zEvals :: PointEval f
  , indexEvals :: Vector 6 (PointEval f)
  , witnessEvals :: Vector 15 (PointEval f)
  , coeffEvals :: Vector 15 (PointEval f)
  , sigmaEvals :: Vector 6 (PointEval f)
  }

-------------------------------------------------------------------------------
-- | IPA Opening Proof
-------------------------------------------------------------------------------

-- | IPA opening proof components.
-- |
-- | These are the values from the proof needed to verify the IPA equation:
-- |   c*Q + delta = z1*(sg + b*u) + z2*H
-- |
-- | Parameters:
-- | - `n`: Number of IPA rounds (16 for standard Pasta SRS)
-- | - `f`: Base field of the commitment curve (circuit field)
-- | - `sf`: Shifted scalar type (Type1 when scalar field < circuit field)
-- |
-- | Reference: poly-commitment/src/ipa.rs OpeningProof struct
type OpeningProof n f sf =
  { lr :: Vector n (LrPair f)
  , sg :: AffinePoint f -- challenge polynomial commitment
  , delta :: AffinePoint f
  , z1 :: sf
  , z2 :: sf
  }

-------------------------------------------------------------------------------
-- | Verifier Data
-------------------------------------------------------------------------------

-- | Data from the verification key needed for proof verification.
-- |
-- | These are typically constants derived from the verifier index:
-- | - shifts: Domain shift values for permutation argument
-- | - endo: Endomorphism coefficient for scalar challenge conversion
-- | - combinedPolynomial: Combined polynomial commitment (computed from vk + xi)
-- | - blindingGenerator: Blinding generator H from SRS
-- |
-- | Note: In practice, some of these may be circuit constants rather than
-- | witness inputs, depending on how the Step circuit is parameterized.
type VerifierData f =
  { shifts :: Vector 7 f
  , endo :: f
  , combinedPolynomial :: AffinePoint f
  , blindingGenerator :: AffinePoint f
  }

-------------------------------------------------------------------------------
-- | Complete Witness
-------------------------------------------------------------------------------

-- | Complete witness data for verifying a Wrap proof in the Step circuit.
-- |
-- | This bundles all the private witness data needed by `finalizeOtherProof`:
-- | - Polynomial evaluations (for PlonkChecks)
-- | - ft polynomial evaluation at zeta*omega
-- | - IPA opening proof components
-- | - Verifier data
-- |
-- | The deferred values (xi, b, combinedInnerProduct, bulletproofChallenges)
-- | come from `UnfinalizedProof` which is part of the public input, not this
-- | witness type.
-- |
-- | Parameters:
-- | - `n`: Number of IPA rounds (16 for standard Pasta SRS)
-- | - `f`: Circuit field (Vesta.ScalarField for Step)
-- | - `sf`: Shifted scalar type for cross-field values
-- |
-- | Reference: step_verifier.ml finalize_other_proof
type WrapProofWitness n f sf =
  { -- Polynomial evaluations
    allEvals :: AllEvals f
  , ftEval1 :: f -- ft polynomial eval at zeta*omega
  -- IPA opening proof
  , openingProof :: OpeningProof n f sf
  -- Verifier data
  , verifierData :: VerifierData f
  }
