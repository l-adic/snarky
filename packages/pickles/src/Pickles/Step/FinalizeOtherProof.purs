-- | Finalize another proof's deferred values in the Step circuit.
-- |
-- | When the Step circuit verifies a previous Wrap proof, it calls this
-- | function to verify all the deferred values. This includes:
-- | - xi_correct (scalar challenge matches squeezed value)
-- | - b_correct (challenge polynomial evaluation)
-- | - combined_inner_product_correct
-- | - plonk_checks_passed (permutation check)
-- |
-- | The circuit returns a boolean indicating whether verification passed,
-- | plus the bulletproof challenges extracted from the proof.
-- |
-- | Reference: step_verifier.ml:823-1086 `finalize_other_proof`
module Pickles.Step.FinalizeOtherProof
  ( -- * Types
    FinalizeOtherProofInput
  , FinalizeOtherProofOutput
  -- * Circuit
  , finalizeOtherProofCircuit
  -- * Component Circuits (exported for testing)
  , module PlonkChecks
  , module ChallengeDigest
  , module IPA
  ) where

import Prelude

import Pickles.IPA (bCorrectCircuit, ipaFinalCheckCircuit, type1ScalarOps) as IPA
import Pickles.PlonkChecks (plonkArithmeticCheckCircuit, plonkChecksCircuit) as PlonkChecks
import Pickles.Sponge (SpongeM, absorb)
import Pickles.Step.ChallengeDigest (challengeDigestCircuit) as ChallengeDigest
import Pickles.Step.Types (BulletproofChallenges, UnfinalizedProof)
import Pickles.Step.WrapProofWitness (WrapProofWitness)
import Poseidon (class PoseidonField)
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Snarky.Types.Shifted (Type1)

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | Input for finalizing another proof.
-- |
-- | This combines:
-- | - `unfinalized`: The deferred values from the proof's public input
-- | - `witness`: Private witness data needed for verification
-- |
-- | The `n` parameter is the number of IPA rounds (16 for Pasta curves).
type FinalizeOtherProofInput n f sf b =
  { -- | Unfinalized proof from public input
    unfinalized :: UnfinalizedProof f sf b
  -- | Private witness data
  , witness :: WrapProofWitness n f sf
  }

-- | Output from finalizing another proof.
-- |
-- | Returns:
-- | - `finalized`: Boolean indicating whether all checks passed
-- | - `challenges`: The bulletproof challenges (derived from L/R pairs)
-- |
-- | The caller uses these challenges for computing messages for the next proof.
type FinalizeOtherProofOutput f =
  { finalized :: BoolVar f
  , challenges :: BulletproofChallenges (FVar f)
  }

-------------------------------------------------------------------------------
-- | Circuit
-------------------------------------------------------------------------------

-- | Finalize another proof's deferred values.
-- |
-- | This circuit verifies all the deferred values from a Wrap proof:
-- |
-- | 1. **Absorb sponge state**: Resume the Fiat-Shamir transcript
-- |
-- | 2. **PLONK Checks**: Absorb evaluations, derive xi and r, verify xi_correct
-- |    and compute combined_inner_product
-- |
-- | 3. **Plonk Arithmetic Check**: Verify claimed `perm` matches computed value
-- |
-- | 4. **b_correct**: Verify the challenge polynomial evaluation
-- |
-- | 5. **IPA Final Check**: Verify the IPA equation c*Q + delta = z1*(sg + b*u) + z2*H
-- |
-- | **Current Status**: This is a skeleton implementation that returns success
-- | and dummy challenges. The full implementation needs to wire up all the
-- | component circuits with the correct inputs.
-- |
-- | Reference: step_verifier.ml:823-1086
finalizeOtherProofCircuit
  :: forall n f t m
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => FinalizeOtherProofInput n (FVar f) (Type1 (FVar f)) (BoolVar f)
  -> SpongeM f (KimchiConstraint f) t m (FinalizeOtherProofOutput f)
finalizeOtherProofCircuit { unfinalized, witness: _witness } = do
  let
    deferred = unfinalized.deferredValues

  -- 1. Absorb the sponge digest from before evaluations
  -- This resumes the Fiat-Shamir transcript from where the prover left off
  absorb unfinalized.spongeDigestBeforeEvaluations

  -- TODO: Full implementation needs to:
  -- 2. Run plonkChecksCircuit with proper inputs
  -- 3. Run plonkArithmeticCheckCircuit with proper inputs
  -- 4. Run bCorrectCircuit with proper inputs
  -- 5. Run ipaFinalCheckCircuit with proper inputs
  -- 6. Combine all check results

  -- For now, return success and the challenges from deferred values
  let
    finalized :: BoolVar f
    finalized = const_ one

    challenges :: BulletproofChallenges (FVar f)
    challenges = deferred.bulletproofChallenges

  pure { finalized, challenges }

-------------------------------------------------------------------------------
-- | Helper: Extract field element from scalar challenge
-- | Note: For proper conversion to full field element, use `toField` with endo
-------------------------------------------------------------------------------

-- scalarChallengeToField :: forall f. SizedF 128 (FVar f) -> FVar f
-- scalarChallengeToField (SizedF x) = x
