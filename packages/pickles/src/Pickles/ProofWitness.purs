-- | Witness data for `finalizeOtherProof`.
-- |
-- | Contains the polynomial evaluations, domain-dependent values, and
-- | public input evaluation that `finalizeOtherProof` needs as private
-- | witness data. Used by both the Step circuit (verifying Wrap proofs)
-- | and the Wrap circuit (verifying Step proofs).
-- |
-- | Opening proof data (L/R pairs, sg, delta, z1, z2) belongs in
-- | `incrementally_verify_proof`, not here. Domain/IPA constants come from
-- | `FinalizeOtherProofParams` (compile-time parameters), not from witness data.
-- |
-- | Reference: mina/src/lib/pickles/step_verifier.ml (finalize_other_proof)
module Pickles.ProofWitness
  ( -- * Polynomial Evaluations (re-exported from PlonkChecks)
    module PlonkChecks
  -- * Domain-dependent values
  , DomainValues
  -- * Complete Witness
  , ProofWitness
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

-- | Witness data for verifying another proof via `finalizeOtherProof`.
-- |
-- | Contains the polynomial evaluations, domain-dependent values, and
-- | public input evaluation needed by the circuit.
-- |
-- | Reference: step_verifier.ml finalize_other_proof
type ProofWitness f =
  { allEvals :: AllEvals f
  , domainValues :: DomainValues f
  , publicEvalForFt :: f
  }
