-- | Hash messages for next Step proof.
-- |
-- | Computes a digest of VK commitments + per-proof sg points and bp challenges.
-- | Used in the Step circuit to compute messages_for_next_step_proof.
-- |
-- | Reference: step_verifier.ml hash_messages_for_next_step_proof (lines 1099-1141)
module Pickles.Step.MessageHash
  ( hashMessagesForNextStepProofOpt
  , hashMessagesForNextStepProofPure
  , hashMessagesForNextStepProofPureTraced
  ) where

import Prelude

import Data.Array as Array
import Data.Fin (getFinite)
import Data.Foldable (foldM, for_)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.OptSponge as OptSponge
import Pickles.Sponge (initialSpongeCircuit)
import Pickles.Trace as Trace
import Pickles.VerificationKey (StepVK)
import Poseidon (class PoseidonField, hash)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, label)
import Snarky.Circuit.RandomOracle.Sponge (Sponge)
import Snarky.Circuit.RandomOracle.Sponge as Sponge
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | `wrapVkChunks` is the wrap VK's own chunk count (Dim 2) — this is
-- | the step circuit consuming the wrap VK's per-commitment chunks.
-- | The sponge absorbs each chunk's `(x, y)` in chunk order, mirroring
-- | OCaml `Plonk_verification_key_evals.to_field_elements`.
hashMessagesForNextStepProofOpt
  :: forall n wrapVkChunks d f t m
   . PrimeField f
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => { vkComms ::
         { sigma :: Vector 6 (Vector wrapVkChunks (AffinePoint (FVar f)))
         , sigmaLast :: Vector wrapVkChunks (AffinePoint (FVar f))
         , coeff :: Vector 15 (Vector wrapVkChunks (AffinePoint (FVar f)))
         , index :: Vector 6 (Vector wrapVkChunks (AffinePoint (FVar f)))
         }
     , appStateFields :: Array (FVar f)
     , proofs ::
         Vector n
           { sg :: AffinePoint (FVar f)
           , rawChallenges :: Vector d (FVar f)
           , mask :: BoolVar f
           }
     }
  -> Snarky (KimchiConstraint f) t m { digest :: FVar f, spongeAfterIndex :: Sponge (FVar f) }
hashMessagesForNextStepProofOpt { vkComms, appStateFields, proofs } = do
  let
    absorbPt s { x, y } = do
      s1 <- Sponge.absorb x s
      Sponge.absorb y s1
    absorbChunks = foldM absorbPt

  -- 1. sponge_after_index: absorb all VK fields, one chunk at a time
  spongeAfterIndex <- label "sponge_after_index" do
    let sponge0 = initialSpongeCircuit :: Sponge (FVar f)
    s1 <- foldM absorbChunks sponge0 vkComms.sigma
    s2 <- absorbChunks s1 vkComms.sigmaLast
    s3 <- foldM absorbChunks s2 vkComms.coeff
    foldM absorbChunks s3 vkComms.index

  -- 2. Copy sponge_after_index, absorb app_state with regular sponge
  digest <- label "msg_hash" do
    s1 <- label "msg_hash_absorb_app" $ foldM (flip Sponge.absorb) spongeAfterIndex appStateFields

    -- 3. Switch to opt_sponge for masked sg + bp_challenges (one per proof)
    Tuple msg _ <- label "msg_hash_opt" $ OptSponge.runOptSpongeFromSponge s1 do
      for_ proofs \proof -> do
        OptSponge.optAbsorb (Tuple proof.mask proof.sg.x)
        OptSponge.optAbsorb (Tuple proof.mask proof.sg.y)
        for_ proof.rawChallenges \c ->
          OptSponge.optAbsorb (Tuple proof.mask c)
      OptSponge.optSqueeze
    pure msg

  pure { digest, spongeAfterIndex }

-- | Pure prover-side version of OCaml `Common.hash_messages_for_next_step_proof`
-- | (`mina/src/lib/crypto/pickles/common.ml:45-52`).
-- |
-- | Absorbs the VK commitment coordinates + app_state fields + per-proof
-- | `(sg, expanded bp_challenges)` pairs into a single Poseidon digest
-- | over the step field.
-- |
-- | Caller is responsible for **expanding** the raw bulletproof challenges
-- | to full step-field elements before passing them in — this matches the
-- | `Reduced_messages_for_next_proof_over_same_field.Step.prepare` step
-- | (`reduced_messages_for_next_proof_over_same_field.ml:32-43`), which
-- | maps `Ipa.Step.compute_challenges` over each vector.
-- |
-- | Field absorption order (matches OCaml
-- | `side_loaded_verification_key.index_to_field_elements` → `to_field_elements`):
-- |
-- | 1. `stepVk.sigmaComm` (7 × 2 = 14 fields)
-- | 2. `stepVk.coefficientsComm` (15 × 2 = 30 fields)
-- | 3. `genericComm, psmComm, completeAddComm, mulComm, emulComm,
-- |    endomulScalarComm` (6 × 2 = 12 fields)
-- | 4. `appState` (user-provided field elements)
-- | 5. For each previous proof: `sg.x, sg.y` then all expanded `bpChallenges`
-- |
-- | For `num_chunks = 1` (standard Mina) each VK commitment is a single
-- | Mirrors OCaml `Common.hash_messages_for_next_step_proof`
-- | (`common.ml:45-52`). For each commitment OCaml absorbs
-- | `Array.concat_map x ~f:(fun (x,y) -> [|x;y|])` — i.e. iterates
-- | over chunks and emits `(x, y)` per chunk. At wrapVkChunks=1 that
-- | collapses to two fields per commitment (the legacy unchunked
-- | behaviour); at wrapVkChunks=2+ each commitment contributes
-- | `2 * wrapVkChunks` fields.
-- |
-- | `wrapVkChunks` is the wrap VK's own chunks (Dim 2) — this is the
-- | step circuit absorbing the wrap VK's bytes for the
-- | `messages_for_next_step_proof` digest.
hashMessagesForNextStepProofPure
  :: forall n wrapVkChunks d f
   . PoseidonField f
  => { stepVk :: StepVK wrapVkChunks f
     , appState :: Array f
     , proofs ::
         Vector n
           { sg :: AffinePoint f
           , expandedBpChallenges :: Vector d f
           }
     }
  -> f
hashMessagesForNextStepProofPure { stepVk, appState, proofs } =
  let
    ptFields :: AffinePoint f -> Array f
    ptFields pt = [ pt.x, pt.y ]

    -- Flatten chunks: each commitment contributes `2 * wrapVkChunks` fields.
    chunkedFields :: Vector wrapVkChunks (AffinePoint f) -> Array f
    chunkedFields = Array.concatMap ptFields <<< Vector.toUnfoldable

    vkFields =
      Array.concatMap chunkedFields (Array.fromFoldable stepVk.sigmaComm)
        <> Array.concatMap chunkedFields (Array.fromFoldable stepVk.coefficientsComm)
        <> chunkedFields stepVk.genericComm
        <> chunkedFields stepVk.psmComm
        <> chunkedFields stepVk.completeAddComm
        <> chunkedFields stepVk.mulComm
        <> chunkedFields stepVk.emulComm
        <> chunkedFields stepVk.endomulScalarComm

    proofFields = Array.concatMap
      ( \p ->
          ptFields p.sg
            <> Vector.toUnfoldable p.expandedBpChallenges
      )
      (Array.fromFoldable proofs)
  in
    hash (vkFields <> appState <> proofFields)

-- | Traced variant of `hashMessagesForNextStepProofPure`.
-- |
-- | Computes the same digest but additionally emits one trace line per
-- | input field element (in hashing order) with dot-separated semantic
-- | labels under the `msgForNextStep.*` prefix. The final digest is
-- | emitted as `msgForNextStep.final_digest`.
-- |
-- | Intended for byte-identical diffing against OCaml's
-- | `Common.hash_messages_for_next_step_proof` via a matching trace
-- | helper. Trace labels:
-- |
-- |   msgForNextStep.vk.sigma.{0..6}.{x,y}
-- |   msgForNextStep.vk.coeff.{0..14}.{x,y}
-- |   msgForNextStep.vk.generic.{x,y}
-- |   msgForNextStep.vk.psm.{x,y}
-- |   msgForNextStep.vk.complete_add.{x,y}
-- |   msgForNextStep.vk.mul.{x,y}
-- |   msgForNextStep.vk.emul.{x,y}
-- |   msgForNextStep.vk.endomul_scalar.{x,y}
-- |   msgForNextStep.app_state.{0..}
-- |   msgForNextStep.prev.{i}.sg.{x,y}
-- |   msgForNextStep.prev.{i}.bp_chal.{0..15}
-- |   msgForNextStep.final_digest
hashMessagesForNextStepProofPureTraced
  :: forall n wrapVkChunks d f
   . PoseidonField f
  => PrimeField f
  => Reflectable n Int
  => Reflectable wrapVkChunks Int
  => Reflectable d Int
  => { stepVk :: StepVK wrapVkChunks f
     , appState :: Array f
     , proofs ::
         Vector n
           { sg :: AffinePoint f
           , expandedBpChallenges :: Vector d f
           }
     }
  -> Effect f
hashMessagesForNextStepProofPureTraced inp@{ stepVk, appState, proofs } = do
  -- Trace label format mirrors OCaml `common.ml:103-112` `trace_point_arr`:
  -- single-chunk array → `label.x` / `label.y`; multi-chunk → `label.i.x` /
  -- `label.i.y` per chunk i. This collapses to the legacy unchunked labels
  -- at wrapVkChunks=1 (no behavioural change for non-chunked tests).
  let
    traceChunks :: String -> Vector wrapVkChunks (AffinePoint f) -> Effect Unit
    traceChunks lbl chunks =
      case Vector.toUnfoldable chunks of
        [ pt ] -> do
          Trace.field (lbl <> ".x") pt.x
          Trace.field (lbl <> ".y") pt.y
        cs -> forWithIndex_ cs \j pt -> do
          Trace.field (lbl <> "." <> show j <> ".x") pt.x
          Trace.field (lbl <> "." <> show j <> ".y") pt.y
  -- sigma_comm: 7 chunked commitments
  forWithIndex_ (Array.fromFoldable stepVk.sigmaComm) \i chunks ->
    traceChunks ("msgForNextStep.vk.sigma." <> show i) chunks
  -- coefficients_comm: 15 chunked commitments
  forWithIndex_ (Array.fromFoldable stepVk.coefficientsComm) \i chunks ->
    traceChunks ("msgForNextStep.vk.coeff." <> show i) chunks
  -- 6 individual index comms
  traceChunks "msgForNextStep.vk.generic" stepVk.genericComm
  traceChunks "msgForNextStep.vk.psm" stepVk.psmComm
  traceChunks "msgForNextStep.vk.complete_add" stepVk.completeAddComm
  traceChunks "msgForNextStep.vk.mul" stepVk.mulComm
  traceChunks "msgForNextStep.vk.emul" stepVk.emulComm
  traceChunks "msgForNextStep.vk.endomul_scalar" stepVk.endomulScalarComm
  -- app_state fields
  forWithIndex_ appState \i v ->
    Trace.field ("msgForNextStep.app_state." <> show i) v
  -- per-proof sg + bp_challenges
  forWithIndex_ (Array.fromFoldable proofs) \i p -> do
    Trace.field ("msgForNextStep.prev." <> show i <> ".sg.x") p.sg.x
    Trace.field ("msgForNextStep.prev." <> show i <> ".sg.y") p.sg.y
    forWithIndex_ p.expandedBpChallenges \fj c ->
      Trace.field ("msgForNextStep.prev." <> show i <> ".bp_chal." <> show (getFinite fj)) c
  let digest = hashMessagesForNextStepProofPure inp
  Trace.field "msgForNextStep.final_digest" digest
  pure digest
