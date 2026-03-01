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
  -- * Complete Witness
  , ProofWitness
  ) where

import Pickles.PlonkChecks (AllEvals)
import Pickles.PlonkChecks (AllEvals) as PlonkChecks

-------------------------------------------------------------------------------
-- | Complete Witness
-------------------------------------------------------------------------------

-- | Witness data for verifying another proof via `finalizeOtherProof`.
-- |
-- | Contains the polynomial evaluations needed by the circuit.
-- | Domain-dependent values (zkPolynomial, zetaToNMinus1, omega powers)
-- | are computed in-circuit from the masked domain generator.
-- |
-- | Reference: step_verifier.ml finalize_other_proof
type ProofWitness f =
  { allEvals :: AllEvals f
  }
