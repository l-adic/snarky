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

import Data.Traversable (for)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.IPA (bCorrectCircuit)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PlonkChecks (absorbAllEvals, plonkArithmeticCheckCircuit, plonkChecksCircuit) as PlonkChecks
import Pickles.PlonkChecks.CombinedInnerProduct (CombinedInnerProductCheckInput, combinedInnerProductCheckCircuit)
import Pickles.PlonkChecks.GateConstraints (GateConstraintInput)
import Pickles.PlonkChecks.Permutation (PermutationInput)
import Pickles.Sponge (SpongeM, absorb, liftSnarky, squeezeScalarChallenge)
import Pickles.Step.ChallengeDigest (challengeDigestCircuit) as ChallengeDigest
import Pickles.Step.WrapProofWitness (WrapProofWitness)
import Pickles.Verify.Types (BulletproofChallenges, PlonkExpanded, UnfinalizedProof, expandPlonkMinimalCircuit)
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, and_, const_, equals_, isEqual, mul_)
import Snarky.Circuit.Kimchi (toField)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, class PrimeField)

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
  , endo :: f -- ^ EndoScalar coefficient (= Wrap_inner_curve.scalar = Vesta.endo_scalar for Step)
  , zkRows :: Int
  , linearizationPoly :: LinearizationPoly f
  }

-- | Input for finalizing another proof.
-- |
-- | This combines:
-- | - `unfinalized`: The deferred values from the proof's public input
-- | - `witness`: Private witness data (polynomial evaluations only)
-- | - `prevChallengeDigest`: Digest of previous recursion challenges
type FinalizeOtherProofInput f sf b =
  { -- | Unfinalized proof from public input
    unfinalized :: UnfinalizedProof f sf b
  -- | Private witness data (polynomial evaluations)
  , witness :: WrapProofWitness f
  -- | Digest of previous recursion challenges (zero for base case)
  , prevChallengeDigest :: f
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
-- | 1. **Expand plonk minimal**: Convert raw 128-bit alpha/zeta to full field
-- |
-- | 2. **Fr-sponge**: Absorb evaluations, derive xi and r
-- |
-- | 3. **xi_correct**: Verify squeezed xi matches deferred xi
-- |
-- | 4. **CIP_correct**: Verify combined inner product matches deferred CIP
-- |
-- | 5. **b_correct**: Verify challenge polynomial evaluation
-- |
-- | 6. **perm_correct**: Verify permutation scalar matches deferred perm
-- |
-- | 7. **Combine**: finalized = xi && cip && b && perm
-- |
-- | Note: IPA final check is NOT part of `finalize_other_proof`. It belongs
-- | in `incrementally_verify_proof` which handles the opening proof.
-- |
-- | Reference: step_verifier.ml:823-1086
finalizeOtherProofCircuit
  :: forall f f' t m sf r
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => HasEndo f f'
  => CircuitM f (KimchiConstraint f) t m
  => { unshift :: sf -> FVar f | r }
  -> FinalizeOtherProofParams f
  -> FinalizeOtherProofInput (FVar f) sf (BoolVar f)
  -> SpongeM f (KimchiConstraint f) t m (FinalizeOtherProofOutput f)
finalizeOtherProofCircuit ops params { unfinalized, witness, prevChallengeDigest } = do
  let
    deferred = unfinalized.deferredValues
    endoVar = const_ params.endo

  -- 1. Expand plonk minimal (raw 128-bit alpha/zeta -> full field via endo)
  plonk <- liftSnarky $ expandPlonkMinimalCircuit endoVar deferred.plonk

  -- 2. Absorb the sponge digest from before evaluations
  -- This resumes the Fiat-Shamir transcript from where the prover left off
  absorb unfinalized.spongeDigestBeforeEvaluations

  -- 3. Absorb prev challenge digest
  absorb prevChallengeDigest

  -- 4. Absorb all polynomial evaluations into the Fr-sponge
  PlonkChecks.absorbAllEvals witness.allEvals

  -- 5. Squeeze xi (128-bit scalar challenge)
  rawXi <- squeezeScalarChallenge

  -- 6. xi_correct: compare squeezed xi with claimed xi
  xiCorrect <- liftSnarky $ isEqual rawXi deferred.xi

  -- 7. Squeeze evalscale (r)
  rawR <- squeezeScalarChallenge

  -- 8. Expand xi and r via endo -> polyscale/evalscale
  polyscale <- liftSnarky $ toField rawXi endoVar
  evalscale <- liftSnarky $ toField rawR endoVar

  -- 9. CIP computation + check
  let cipInput = buildCipInput plonk witness params
  computedCIP <- liftSnarky $
    combinedInnerProductCheckCircuit params.linearizationPoly
      { polyscale, evalscale }
      cipInput
  cipCorrect <- liftSnarky $
    equals_ (ops.unshift deferred.combinedInnerProduct) computedCIP

  -- 10. Expand bulletproof challenges (16 x 128-bit -> full field via endo)
  expandedChallenges <- liftSnarky $
    for deferred.bulletproofChallenges \c -> toField c endoVar

  -- 11. b_correct
  zetaOmega <- liftSnarky $ mul_ plonk.zeta (const_ params.domain.generator)
  bOk <- liftSnarky $ bCorrectCircuit
    { challenges: expandedChallenges
    , zeta: plonk.zeta
    , zetaOmega
    , evalscale
    , expectedB: ops.unshift deferred.b
    }

  -- 12. perm_correct
  let permInput = buildPermInput plonk witness params
  permOk <- liftSnarky $ PlonkChecks.plonkArithmeticCheckCircuit ops
    { claimedPerm: deferred.perm, permInput }

  -- 13. Combine all checks
  finalized <- liftSnarky do
    a <- and_ xiCorrect cipCorrect
    b <- and_ bOk permOk
    and_ a b

  let challenges = deferred.bulletproofChallenges

  pure { finalized, challenges }

-------------------------------------------------------------------------------
-- | Helpers
-------------------------------------------------------------------------------

-- | Build the CombinedInnerProductCheckInput from expanded plonk values,
-- | witness evaluations, and compile-time parameters.
buildCipInput
  :: forall f
   . PrimeField f
  => PlonkExpanded (FVar f)
  -> WrapProofWitness (FVar f)
  -> FinalizeOtherProofParams f
  -> CombinedInnerProductCheckInput (FVar f)
buildCipInput plonk witness params =
  { permInput: buildPermInput plonk witness params
  , gateInput: buildGateInput plonk witness
  , publicEvalForFt: witness.publicEvalForFt
  , publicPointEval: witness.allEvals.publicEvals
  , ftEval1: witness.allEvals.ftEval1
  , zEvals: witness.allEvals.zEvals
  , indexEvals: witness.allEvals.indexEvals
  , witnessEvals: witness.allEvals.witnessEvals
  , coeffEvals: witness.allEvals.coeffEvals
  , sigmaEvals: witness.allEvals.sigmaEvals
  }

-- | Build the PermutationInput for the perm_correct check.
buildPermInput
  :: forall f
   . PrimeField f
  => PlonkExpanded (FVar f)
  -> WrapProofWitness (FVar f)
  -> FinalizeOtherProofParams f
  -> PermutationInput (FVar f)
buildPermInput plonk witness params =
  { w: map _.zeta (Vector.take @7 witness.allEvals.witnessEvals)
  , sigma: map _.zeta witness.allEvals.sigmaEvals
  , z: witness.allEvals.zEvals
  , shifts: map const_ params.domain.shifts
  , alpha: plonk.alpha
  , beta: plonk.beta
  , gamma: plonk.gamma
  , zkPolynomial: witness.domainValues.zkPolynomial
  , zetaToNMinus1: witness.domainValues.zetaToNMinus1
  , omegaToMinusZkRows: witness.domainValues.omegaToMinusZkRows
  , zeta: plonk.zeta
  }

-- | Build the GateConstraintInput from evaluations and domain values.
buildGateInput
  :: forall f
   . PrimeField f
  => PlonkExpanded (FVar f)
  -> WrapProofWitness (FVar f)
  -> GateConstraintInput (FVar f)
buildGateInput plonk witness =
  { witnessEvals: witness.allEvals.witnessEvals
  , coeffEvals: map _.zeta witness.allEvals.coeffEvals
  , indexEvals: witness.allEvals.indexEvals
  , alpha: plonk.alpha
  , beta: plonk.beta
  , gamma: plonk.gamma
  , jointCombiner: const_ zero
  , vanishesOnZk: witness.domainValues.vanishesOnZk
  , lagrangeFalse0: witness.domainValues.lagrangeFalse0
  , lagrangeTrue1: witness.domainValues.lagrangeTrue1
  }
