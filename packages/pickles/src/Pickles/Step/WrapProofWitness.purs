-- | Witness data for verifying a Wrap proof in the Step circuit.
-- |
-- | When the Step circuit verifies a previous Wrap proof, `finalize_other_proof`
-- | needs polynomial evaluations as private witness data.
-- |
-- | Opening proof data (L/R pairs, sg, delta, z1, z2) belongs in
-- | `incrementally_verify_proof`, not here. Domain/IPA constants come from
-- | `FinalizeOtherProofParams` (compile-time parameters), not from witness data.
-- |
-- | Reference: mina/src/lib/pickles/step_verifier.ml (finalize_other_proof)
module Pickles.Step.WrapProofWitness
  ( -- * Polynomial Evaluations (re-exported from PlonkChecks)
    module PlonkChecks
  -- * Domain-dependent values
  , DomainValues
  -- * Complete Witness
  , WrapProofWitness
  ) where

import Pickles.PlonkChecks (AllEvals)
import Pickles.PlonkChecks (AllEvals) as PlonkChecks

-------------------------------------------------------------------------------
-- | Domain-dependent values
-------------------------------------------------------------------------------

-- | Domain-dependent values computed from expanded zeta and domain parameters.
-- |
-- | These are deterministic given zeta and domain params. In the full system
-- | they would be computed in-circuit; for now they are passed as witness data.
-- |
-- | Reference: plonk_checks.ml derive_plonk, step_verifier.ml
type DomainValues f =
  { zkPolynomial :: f
  , zetaToNMinus1 :: f
  , omegaToMinusZkRows :: f
  , vanishesOnZk :: f
  , lagrangeFalse0 :: f
  , lagrangeTrue1 :: f
  }

-------------------------------------------------------------------------------
-- | Complete Witness
-------------------------------------------------------------------------------

-- | Witness data for verifying a Wrap proof in the Step circuit.
-- |
-- | Contains the polynomial evaluations, domain-dependent values, and
-- | public input evaluation needed by `finalizeOtherProof`.
-- |
-- | Reference: step_verifier.ml finalize_other_proof
type WrapProofWitness f =
  { allEvals :: AllEvals f
  , domainValues :: DomainValues f
  , publicEvalForFt :: f
  }
