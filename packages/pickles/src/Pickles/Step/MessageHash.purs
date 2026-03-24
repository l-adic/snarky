-- | Hash messages for next Step proof.
-- |
-- | Computes a digest of VK commitments + per-proof sg points and bp challenges.
-- | Used in the Step circuit to compute messages_for_next_step_proof.
-- |
-- | Reference: step_verifier.ml hash_messages_for_next_step_proof (lines 1099-1141)
module Pickles.Step.MessageHash
  ( hashMessagesForNextStepProof
  , hashMessagesForNextStepProofOpt
  ) where

import Prelude

import Data.Foldable (foldM, for_)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Pickles.OptSponge as OptSponge
import Pickles.Sponge (initialSpongeCircuit)
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, label)
import Snarky.Circuit.RandomOracle.Sponge (Sponge)
import Snarky.Circuit.RandomOracle.Sponge as Sponge
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Hash messages for next Step proof.
-- |
-- | 1. Compute sponge_after_index by absorbing all VK commitment coordinates
-- | 2. For each proof: absorb sg.x, sg.y, then all bp_challenges
-- | 3. Squeeze digest
-- |
-- | The VK fields are: sigma_comm(7×2) + coefficients_comm(15×2) + 6 index comms(6×2) = 56 fields.
-- | These enter as circuit variables (not constants).
hashMessagesForNextStepProof
  :: forall n d f t m
   . PrimeField f
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => { vkComms ::
         { sigma :: Vector 6 (AffinePoint (FVar f))
         , sigmaLast :: AffinePoint (FVar f)
         , coeff :: Vector 15 (AffinePoint (FVar f))
         , index :: Vector 6 (AffinePoint (FVar f))
         }
     , proofs ::
         Vector n
           { sg :: AffinePoint (FVar f)
           , bpChallenges :: Vector d (FVar f)
           }
     }
  -> Snarky (KimchiConstraint f) t m (FVar f)
hashMessagesForNextStepProof { vkComms, proofs } = do
  let
    absorbPt s { x, y } = do
      s1 <- Sponge.absorb x s
      Sponge.absorb y s1

  -- 1. sponge_after_index: absorb all VK fields
  -- Order matches OCaml index_to_field_elements:
  -- sigma_comm(7) → coefficients_comm(15) → index comms(6)
  spongeAfterIndex <- do
    let sponge0 = initialSpongeCircuit :: Sponge (FVar f)
    -- sigma_comm: first 6 + sigmaLast = 7
    s1 <- foldM absorbPt sponge0 vkComms.sigma
    s2 <- absorbPt s1 vkComms.sigmaLast
    -- coefficients_comm: 15
    s3 <- foldM absorbPt s2 vkComms.coeff
    -- index comms: generic, psm, complete_add, mul, emul, endomul_scalar = 6
    foldM absorbPt s3 vkComms.index

  -- 2. For each proof: absorb sg + bp_challenges
  spongeAfterProofs <- foldM
    ( \s proof -> do
        s1 <- Sponge.absorb proof.sg.x s
        s2 <- Sponge.absorb proof.sg.y s1
        foldM (\s' c -> Sponge.absorb c s') s2 proof.bpChallenges
    )
    spongeAfterIndex
    proofs

  -- 3. Squeeze digest
  { result: digest } <- Sponge.squeeze spongeAfterProofs
  pure digest

-- | Hash messages for next Step proof using opt_sponge for masked fields.
-- |
-- | This is the circuit-equivalent of OCaml's hash_messages_for_next_step_proof_opt
-- | (step_verifier.ml:1190-1236). Used in full verify_one where proofs have a mask.
-- |
-- | 1. Compute sponge_after_index by absorbing all VK commitment coordinates
-- | 2. Copy sponge, absorb app_state with regular sponge (Not_opt)
-- | 3. Switch to opt_sponge for masked sg + bp_challenges (Opt)
-- | 4. Squeeze digest
-- |
-- | Returns both the digest AND sponge_after_index (needed by IVP).
hashMessagesForNextStepProofOpt
  :: forall n d f t m
   . PrimeField f
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => { vkComms ::
         { sigma :: Vector 6 (AffinePoint (FVar f))
         , sigmaLast :: AffinePoint (FVar f)
         , coeff :: Vector 15 (AffinePoint (FVar f))
         , index :: Vector 6 (AffinePoint (FVar f))
         }
     , appState :: FVar f
     , proofs ::
         Vector n
           { sg :: AffinePoint (FVar f)
           , rawChallenges :: Vector d (FVar f)
           , mask :: BoolVar f
           }
     }
  -> Snarky (KimchiConstraint f) t m { digest :: FVar f, spongeAfterIndex :: Sponge (FVar f) }
hashMessagesForNextStepProofOpt { vkComms, appState, proofs } = do
  let
    absorbPt s { x, y } = do
      s1 <- Sponge.absorb x s
      Sponge.absorb y s1

  -- 1. sponge_after_index: absorb all VK fields
  spongeAfterIndex <- label "sponge_after_index" do
    let sponge0 = initialSpongeCircuit :: Sponge (FVar f)
    s1 <- foldM absorbPt sponge0 vkComms.sigma
    s2 <- absorbPt s1 vkComms.sigmaLast
    s3 <- foldM absorbPt s2 vkComms.coeff
    foldM absorbPt s3 vkComms.index

  -- 2. Copy sponge_after_index, absorb app_state with regular sponge
  digest <- label "msg_hash" do
    s1 <- label "msg_hash_absorb_app" $ Sponge.absorb appState spongeAfterIndex

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
