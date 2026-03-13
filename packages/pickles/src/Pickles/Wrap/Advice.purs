-- | Advisory monad for the Wrap circuit's private witness data.
-- |
-- | In OCaml Pickles (requests.ml), the Wrap circuit uses 8 request types
-- | to obtain private data via snarky's exists/handler mechanism.
-- |
-- | Parameters:
-- | - `mpv`: max_proofs_verified (always 2 in Pickles). Determines the size of
-- |          vectors for unfinalized proofs, evals, step accumulators, etc.
-- | - `ds`: Step IPA rounds (determines lr vector size in opening proof)
-- | - `dw`: Wrap IPA rounds (determines bulletproof challenge dimension in unfinalized proof)
-- | - `m`: Base monad (Effect for compilation, ProverM for proving)
-- | - `f`: Circuit field (Pallas.ScalarField for Wrap)
-- |
-- | NOT YET IMPLEMENTED:
-- |   Req.Which_branch    Selects which step proof branch is being verified.
-- |   Req.Wrap_domain_indices  Domain size selection per proof.
-- |
-- | Reference: mina/src/lib/pickles/requests.ml (Wrap module)
-- |            mina/src/lib/pickles/wrap_main.ml
module Pickles.Wrap.Advice
  ( class WrapWitnessM
  , getStepIOFields
  , getEvals
  , getMessages
  , getOpeningProof
  , getUnfinalizedProofs
  , getStepAccs
  , getOldBpChallenges
  ) where

import Prelude

import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Effect (Effect)
import Effect.Exception (throw)
import Pickles.ProofWitness (ProofWitness)
import Pickles.Verify.Types (UnfinalizedProof)
import Snarky.Circuit.DSL (F)
import Snarky.Circuit.Kimchi (Type1, Type2)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Advisory monad for the Wrap circuit.
-- |
-- | Provides private witness data via `exists $ lift $ getXxx unit`.
-- | The Wrap circuit verifies one Step proof but finalizes `mpv` previous
-- | Wrap proofs (padded with dummies when fewer are real).
class Monad m <= WrapWitnessM (mpv :: Int) (ds :: Int) (dw :: Int) m f where
  -- | Step I/O as flat field elements (for publicInputCommit in IVP).
  -- | OCaml: Req.Proof_state (step statement portion)
  getStepIOFields :: Unit -> m (Array (F f))

  -- | Polynomial evaluations for each of `mpv` finalize calls.
  -- | OCaml: Req.Evals (Vector mpv)
  getEvals :: Unit -> m (Vector mpv (ProofWitness (F f)))

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
         , z1 :: Type1 (F f)
         , z2 :: Type1 (F f)
         }

  -- | Unfinalized proofs for each of `mpv` finalize calls.
  -- | OCaml: Req.Proof_state (unfinalized_proofs, Vector mpv)
  getUnfinalizedProofs :: Unit -> m (Vector mpv (UnfinalizedProof dw (F f) (Type2 (F f)) Boolean))

  -- | Previous step accumulators (sg points) for IVP.
  -- | OCaml: Req.Step_accs (Vector mpv)
  getStepAccs :: Unit -> m (Vector mpv (AffinePoint (F f)))

  -- | Old bulletproof challenges from previous wrap proofs.
  -- | OCaml: Req.Old_bulletproof_challenges (Vector mpv (Vector dw f))
  getOldBpChallenges :: Unit -> m (Vector mpv (Vector dw (F f)))

-- | Compilation instance: never called, exists only to satisfy the constraint
-- | during `compile` which uses Effect as the base monad.
instance (Reflectable mpv Int, Reflectable ds Int, Reflectable dw Int, PrimeField f) => WrapWitnessM mpv ds dw Effect f where
  getStepIOFields _ = throw "impossible! getStepIOFields called during compilation"
  getEvals _ = throw "impossible! getEvals called during compilation"
  getMessages _ = throw "impossible! getMessages called during compilation"
  getOpeningProof _ = throw "impossible! getOpeningProof called during compilation"
  getUnfinalizedProofs _ = throw "impossible! getUnfinalizedProofs called during compilation"
  getStepAccs _ = throw "impossible! getStepAccs called during compilation"
  getOldBpChallenges _ = throw "impossible! getOldBpChallenges called during compilation"
