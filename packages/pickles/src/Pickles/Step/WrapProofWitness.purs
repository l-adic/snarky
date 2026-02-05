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
  -- * Complete Witness
  , WrapProofWitness
  ) where

import Pickles.PlonkChecks (AllEvals)
import Pickles.PlonkChecks (AllEvals) as PlonkChecks

-------------------------------------------------------------------------------
-- | Complete Witness
-------------------------------------------------------------------------------

-- | Witness data for verifying a Wrap proof in the Step circuit.
-- |
-- | Contains only the polynomial evaluations needed by `finalizeOtherProof`.
-- | This is the only private witness data for `finalize_other_proof` in OCaml.
-- |
-- | Opening proof data (lr, sg, delta, z1, z2) will be used by
-- | `incrementally_verify_proof` when that is implemented separately.
-- |
-- | Reference: step_verifier.ml finalize_other_proof
type WrapProofWitness f = { allEvals :: AllEvals f }
