-- | Types for single Kimchi proof verification.
-- |
-- | This module defines types for verifying a single Kimchi proof (non-recursive).
-- | The verifier produces a deferred check (sg commitment) that is verified
-- | out-of-circuit via native MSM.
-- |
-- | For recursive composition (folding into accumulators), additional types
-- | will be needed later.
module Pickles.Verifier.Types
  ( -- Verifier input/output
    VerifierInput
  , VerifierOutput
  -- Deferred check
  , DeferredCheck
  -- Proof components
  , ProofMessages
  , OpeningProof
  -- Re-exports
  , module Exports
  ) where

import Data.Vector (Vector)
import Pickles.Linearization.FFI (PointEval)
import Pickles.ScalarChallenge (Challenge, ChallengesMinimal) as Exports
import Snarky.Circuit.Kimchi.EndoScalar (ScalarChallenge) as Exports
import Snarky.Data.EllipticCurve (AffinePoint)

--------------------------------------------------------------------------------
-- | Deferred Check (Output)
--------------------------------------------------------------------------------

-- | The deferred verification obligation from the IPA protocol.
-- |
-- | After in-circuit verification, we output the challenges. The expensive
-- | MSM check (sg = MSM(SRS.g, b_poly_coefficients(challenges))) is performed
-- | out-of-circuit.
-- |
-- | Type parameter d: number of IPA rounds (= bulletproof challenge count)
type DeferredCheck d f =
  { challenges :: Vector d f
  }

--------------------------------------------------------------------------------
-- | Proof Messages (Prover Commitments)
--------------------------------------------------------------------------------

-- | Polynomial commitments sent by the prover.
-- |
-- | These are absorbed into the Fiat-Shamir sponge to derive challenges.
type ProofMessages f =
  { wComm :: Vector 15 (AffinePoint f) -- Wire polynomial commitments
  , zComm :: AffinePoint f -- Permutation polynomial commitment
  , tComm :: AffinePoint f -- Quotient polynomial commitment
  }

--------------------------------------------------------------------------------
-- | Opening Proof
--------------------------------------------------------------------------------

-- | The IPA opening proof.
-- |
-- | Type parameter d: number of IPA rounds
type OpeningProof d f =
  { lr :: Vector d { l :: AffinePoint f, r :: AffinePoint f }
  , delta :: AffinePoint f
  , z1 :: f
  , z2 :: f
  , sg :: AffinePoint f -- Challenge polynomial commitment (verified out-of-circuit)
  }

--------------------------------------------------------------------------------
-- | Verifier Input
--------------------------------------------------------------------------------

-- | Input to the Kimchi verifier circuit.
-- |
-- | Type parameter d: number of IPA rounds (domain log2)
type VerifierInput d f =
  { -- Polynomial commitments from prover
    messages :: ProofMessages f

  -- Polynomial evaluations at zeta and zeta*omega
  , evaluations ::
      { witness :: Vector 15 (PointEval f)
      , coefficient :: Vector 15 f -- Only at zeta
      , sigma :: Vector 6 (PointEval f) -- Permutation sigmas
      , z :: PointEval f -- Permutation polynomial
      , index :: Vector 6 (PointEval f) -- Selector polynomials
      , publicInput :: PointEval f
      , ft :: PointEval f -- Linearization polynomial
      }

  -- Opening proof
  , opening :: OpeningProof d f

  -- Verification key (public parameters)
  , verificationKey ::
      { h :: AffinePoint f -- SRS H generator
      , domainLog2 :: Int -- Domain size as log2
      }
  }

--------------------------------------------------------------------------------
-- | Verifier Output
--------------------------------------------------------------------------------

-- | Output from the Kimchi verifier circuit.
-- |
-- | The circuit verifies the PLONK constraints and IPA equation in-circuit,
-- | then outputs the deferred sg check for out-of-circuit verification.
type VerifierOutput d f =
  { deferredCheck :: DeferredCheck d f
  , sg :: AffinePoint f -- The sg from the proof (to be verified against challenges)
  }
