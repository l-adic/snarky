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
    FinalizeOtherProofParams
  , FinalizeOtherProofInput
  , FinalizeOtherProofOutput
  -- * Circuit
  , finalizeOtherProofCircuit
  -- * Component Circuits (exported for testing)
  , module PlonkChecks
  , module ChallengeDigest
  ) where

import Prelude

import Data.Vector (Vector)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PlonkChecks (absorbAllEvals, plonkChecksCircuit) as PlonkChecks
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

-- | Compile-time parameters for finalizing another proof.
-- |
-- | These come from the verification key / are known at circuit compile time.
-- | In OCaml, `finalize_other_proof` receives `step_domains`, `zk_rows`, and
-- | `endo` as separate parameters.
-- |
-- | - `domain`: Domain generator and shift values for the permutation argument
-- | - `endo`: Endomorphism coefficient for scalar challenge conversion
-- | - `zkRows`: Number of zero-knowledge rows (typically 3)
-- | - `linearizationPoly`: The linearization polynomial for gate constraints
-- |
-- | Reference: step_verifier.ml:823 `finalize_other_proof` parameters
type FinalizeOtherProofParams f =
  { domain :: { generator :: f, shifts :: Vector 7 f }
  , endo :: f
  , zkRows :: Int
  , linearizationPoly :: LinearizationPoly f
  }

-- | Input for finalizing another proof.
-- |
-- | This combines:
-- | - `unfinalized`: The deferred values from the proof's public input
-- | - `witness`: Private witness data (polynomial evaluations only)
type FinalizeOtherProofInput f sf b =
  { -- | Unfinalized proof from public input
    unfinalized :: UnfinalizedProof f sf b
  -- | Private witness data (polynomial evaluations)
  , witness :: WrapProofWitness f
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
-- | Note: IPA final check is NOT part of `finalize_other_proof`. It belongs
-- | in `incrementally_verify_proof` which handles the opening proof.
-- |
-- | **Current Status**: This is a skeleton implementation that returns success
-- | and dummy challenges. The full implementation needs to wire up all the
-- | component circuits with the correct inputs.
-- |
-- | Reference: step_verifier.ml:823-1086
finalizeOtherProofCircuit
  :: forall f t m
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => FinalizeOtherProofParams f
  -> FinalizeOtherProofInput (FVar f) (Type1 (FVar f)) (BoolVar f)
  -> SpongeM f (KimchiConstraint f) t m (FinalizeOtherProofOutput f)
finalizeOtherProofCircuit _params { unfinalized, witness } = do
  let
    deferred = unfinalized.deferredValues

  -- 1. Absorb the sponge digest from before evaluations
  -- This resumes the Fiat-Shamir transcript from where the prover left off
  absorb unfinalized.spongeDigestBeforeEvaluations

  -- 2. Absorb all polynomial evaluations into the Fr-sponge
  -- (includes ftEval1, follows order in plonkChecksCircuit / step_verifier.ml)
  PlonkChecks.absorbAllEvals witness.allEvals

  -- TODO: Full implementation needs to:
  -- 3. Squeeze to derive xi (polyscale) and verify xi_correct
  -- 4. Squeeze to derive evalscale (r)
  -- 5. Compute and verify combined_inner_product
  -- 6. Run plonkArithmeticCheckCircuit (verify perm)
  -- 7. Run bCorrectCircuit
  -- 8. Combine all check results

  -- For now, return success and the challenges from deferred values
  let
    finalized :: BoolVar f
    finalized = const_ one

    challenges :: BulletproofChallenges (FVar f)
    challenges = deferred.bulletproofChallenges

  pure { finalized, challenges }
