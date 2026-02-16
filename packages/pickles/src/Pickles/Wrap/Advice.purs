-- | Advisory monad for the Wrap circuit's private witness data.
-- |
-- | In OCaml Pickles (requests.ml), the Wrap circuit uses 8 request types
-- | to obtain private data via snarky's exists/handler mechanism. Below is
-- | the full inventory with status in our implementation:
-- |
-- | IMPLEMENTED (methods on WrapWitnessM):
-- |   Req.Evals          → getEvals         Polynomial evaluations for finalizeOtherProof
-- |   Req.Messages        → getMessages      Protocol commitments (wComm, zComm, tComm) for IVP
-- |   Req.Openings_proof  → getOpeningProof   Opening proof (delta, sg, lr, z1, z2) for IVP
-- |
-- | NOT YET NEEDED:
-- |   Req.Proof_state     Our `unfinalized` (deferredValues + shouldFinalize + spongeDigest)
-- |                       is already public input. In OCaml it's a request because the full
-- |                       Proof_state also carries messages_for_next_step_proof which we
-- |                       handle separately. Revisit when adding that field.
-- |
-- |   Req.Which_branch    Selects which step proof branch is being verified. We only
-- |                       support a single branch (n=1), so this is always 0. Needed
-- |                       when we generalize to multiple step proof branches.
-- |
-- |   Req.Step_accs       Previous step accumulators (sg points). Our sgOld is
-- |                       currently Vector 0 (no previous accumulators). Needed
-- |                       when we implement the full inductive accumulation.
-- |
-- |   Req.Old_bulletproof_challenges
-- |                       Bulletproof challenges from previous wrap proofs. Not yet
-- |                       part of our circuit. Needed for full recursion.
-- |
-- |   Req.Wrap_domain_indices
-- |                       Domain size selection for each proof being wrapped. We use
-- |                       a single fixed domain. Needed when supporting multiple
-- |                       wrap domain sizes.
-- |
-- | Reference: mina/src/lib/pickles/requests.ml (Wrap module)
-- |            mina/src/lib/pickles/wrap_main.ml
module Pickles.Wrap.Advice
  ( class WrapWitnessM
  , getEvals
  , getMessages
  , getOpeningProof
  ) where

import Prelude

import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Effect (Effect)
import Effect.Exception (throw)
import Pickles.ProofWitness (ProofWitness)
import Snarky.Circuit.DSL (F)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Advisory monad for the Wrap circuit.
-- |
-- | Provides private witness data via `exists $ lift $ getXxx unit`.
-- | The Wrap circuit always verifies exactly one Step proof, so
-- | methods return single values (not vectors).
-- |
-- | Parameters:
-- | - `ds`: Step IPA rounds (determines lr vector size in opening proof)
-- | - `m`: Base monad (Effect for compilation, ProverM for proving)
-- | - `f`: Circuit field (Pallas.ScalarField for Wrap)
class Monad m <= WrapWitnessM (ds :: Int) m f where
  -- | Polynomial evaluations and domain values for finalizeOtherProof.
  -- | OCaml: Req.Evals
  getEvals :: Unit -> m (ProofWitness (F f))

  -- | Protocol commitments for IVP verification.
  -- | OCaml: Req.Messages
  getMessages
    :: Unit
    -> m
         { wComm :: Vector 15 (AffinePoint (F f))
         , zComm :: AffinePoint (F f)
         , tComm :: Vector 7 (AffinePoint (F f))
         }

  -- | Full opening proof for IVP verification.
  -- | OCaml: Req.Openings_proof
  getOpeningProof
    :: Unit
    -> m
         { delta :: AffinePoint (F f)
         , sg :: AffinePoint (F f)
         , lr :: Vector ds { l :: AffinePoint (F f), r :: AffinePoint (F f) }
         , z1 :: F f
         , z2 :: F f
         }

-- | Compilation instance: never called, exists only to satisfy the constraint
-- | during `compile` which uses Effect as the base monad.
instance (Reflectable ds Int, PrimeField f) => WrapWitnessM ds Effect f where
  getEvals _ = throw "impossible! getEvals called during compilation"
  getMessages _ = throw "impossible! getMessages called during compilation"
  getOpeningProof _ = throw "impossible! getOpeningProof called during compilation"
