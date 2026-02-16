-- | Advisory monad for the Step circuit's private witness data.
-- |
-- | In OCaml Pickles (requests.ml Step module), the Step circuit uses 9
-- | request types. The types and usage are derived from:
-- |   - mina/src/lib/pickles/requests.ml (Step module, lines 120-141)
-- |   - mina/src/lib/pickles/step_main.ml (lines 281-374, exists calls)
-- |   - mina/src/lib/pickles/per_proof_witness.ml (Proof_with_datas type)
-- |
-- | Request inventory:
-- |
-- |   Req.App_state : statement
-- |     The application-specific input (e.g., Schnorr verification data).
-- |     step_main.ml:281: `exists input_typ ~request:(fun () -> Req.App_state)`
-- |
-- |   Req.Compute_prev_proof_parts : previous_proof_statements -> unit Promise.t
-- |     Triggers async pre-computation of previous proof data before the
-- |     prover requests it. step_main.ml:306: async unit request.
-- |
-- |   Req.Proof_with_datas : Per_proof_witness.Constant.No_app_state.t (per proof)
-- |     The main per-proof witness. Contains (per_proof_witness.ml:52-95):
-- |       - wrap_proof: polynomial commitments, evaluations, opening proof
-- |       - proof_state: deferred_values, sponge_digest, messages_for_next_wrap_proof
-- |       - prev_proof_evals: All_evals from the inner step proof
-- |       - prev_challenges: IPA challenges from each previously verified proof
-- |       - prev_challenge_polynomial_commitments: sg points for each previous proof
-- |     step_main.ml:358: `exists ... ~request:(fun () -> Req.Proof_with_datas)`
-- |
-- |   Req.Wrap_index : Plonk_verification_key_evals.t
-- |     Verification key polynomial commitments for the Wrap circuit being verified.
-- |     step_main.ml:354: `exists ... ~request:(fun () -> Req.Wrap_index)`
-- |
-- |   Req.Unfinalized_proofs : (Unfinalized.t, proofs_verified) Vector.t
-- |     Deferred values + shouldFinalize for each previous proof.
-- |     step_main.ml:367: `exists ... ~request:(fun () -> Req.Unfinalized_proofs)`
-- |
-- |   Req.Messages_for_next_wrap_proof : (Digest.t, max_proofs_verified) Vector.t
-- |     Digests for the next Wrap proof (hash of bp challenges + sg).
-- |     step_main.ml:370: `exists ... ~request:(fun () -> Req.Messages_for_next_wrap_proof)`
-- |
-- |   Req.Wrap_domain_indices : (Proofs_verified.t, proofs_verified) Vector.t
-- |     Domain size selection for each wrapped proof.
-- |     step_main.ml:374: `exists ... ~request:(fun () -> Req.Wrap_domain_indices)`
-- |
-- |   Req.Return_value : return_value -> unit
-- |     Prover-side extraction of the application's return value.
-- |     step_main.ml:293: `exists Typ.unit ~request:...`
-- |
-- |   Req.Auxiliary_value : auxiliary_value -> unit
-- |     Prover-side extraction of auxiliary (private) output.
-- |     step_main.ml:298: `exists Typ.unit ~request:...`
-- |
-- | CURRENT STATUS:
-- |   Our getProofWitnesses provides a subset of Proof_with_datas — just the
-- |   polynomial evaluations and domain values needed by finalizeOtherProof.
-- |   The remaining fields (wrap_proof, proof_state, prev_challenges, etc.)
-- |   are not yet part of our circuit.
module Pickles.Step.Advice
  ( class StepWitnessM
  , getProofWitnesses
  ) where

import Prelude

import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Effect (Effect)
import Effect.Exception (throw)
import Pickles.ProofWitness (ProofWitness)
import Snarky.Circuit.DSL (F)
import Snarky.Curves.Class (class PrimeField)

-- | Advisory monad for the Step circuit.
-- |
-- | Provides private witness data via `exists $ lift $ getXxx unit`.
-- | The Step circuit verifies `n` previous Wrap proofs, so methods
-- | return vectors of size `n`.
-- |
-- | Parameters:
-- | - `n`: Number of previous proofs being verified
-- | - `m`: Base monad (Effect for compilation, StepProverM for proving)
-- | - `f`: Circuit field (Vesta.ScalarField for Step)
class Monad m <= StepWitnessM (n :: Int) m f where
  -- | Per-proof polynomial evaluations and domain values for finalizeOtherProof.
  -- | A subset of OCaml's Req.Proof_with_datas (the prev_proof_evals portion).
  getProofWitnesses :: Unit -> m (Vector n (ProofWitness (F f)))

-- | Compilation instance: never called, exists only to satisfy the constraint
-- | during `compile` which uses Effect as the base monad.
instance (Reflectable n Int, PrimeField f) => StepWitnessM n Effect f where
  getProofWitnesses _ = throw "impossible! getProofWitnesses called during compilation"
