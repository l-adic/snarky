-- | The `messages_for_next_step_proof` digest: the wrap VK's
-- | commitments, the application state, and each previous proof's `sg`
-- | point and bulletproof challenges, absorbed in that order into one
-- | Poseidon sponge.
-- |
-- | Three forms of the same digest — in circuit, out of circuit, and
-- | out of circuit with a trace.
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
import Data.Newtype (unwrap)
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.OptSponge as OptSponge
import Pickles.Sponge (initialSpongeCircuit)
import Pickles.Trace as Trace
import Pickles.Types (ChunkedCommitment)
import Pickles.VerificationKey (StepVK)
import Poseidon (class PoseidonField, hash)
import Snarky.Circuit.DSL (BoolVar, FVar, Snarky, label)
import Snarky.Circuit.RandomOracle.Sponge (Sponge)
import Snarky.Circuit.RandomOracle.Sponge as Sponge
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint(..))

-- | The in-circuit digest, with each proof's contribution gated on its
-- | `mask` through an opt-sponge. Also returns the sponge state after
-- | the VK commitments, which the IVP resumes from.
-- |
-- | Absorption order is fixed by the verifier's transcript: every
-- | commitment chunk by chunk, `x` then `y`, then the app state, then
-- | per proof `sg.x`, `sg.y` and that proof's challenges.
hashMessagesForNextStepProofOpt
  :: forall n wrapVkChunks d f r
   . PrimeField f
  => PoseidonField f
  => { vkComms ::
         { sigma :: Vector 6 (ChunkedCommitment wrapVkChunks (AffinePoint (FVar f)))
         , sigmaLast :: ChunkedCommitment wrapVkChunks (AffinePoint (FVar f))
         , coeff :: Vector 15 (ChunkedCommitment wrapVkChunks (AffinePoint (FVar f)))
         , index :: Vector 6 (ChunkedCommitment wrapVkChunks (AffinePoint (FVar f)))
         }
     , appStateFields :: Array (FVar f)
     , proofs ::
         Vector n
           { sg :: AffinePoint (FVar f)
           , rawChallenges :: Vector d (FVar f)
           , mask :: BoolVar f
           }
     }
  -> Snarky f (KimchiConstraint f) r { digest :: FVar f, spongeAfterIndex :: Sponge (FVar f) }
hashMessagesForNextStepProofOpt { vkComms, appStateFields, proofs } = do
  let
    absorbPt s (AffinePoint { x, y }) = do
      s1 <- Sponge.absorb x s
      Sponge.absorb y s1
    absorbChunks s = foldM absorbPt s <<< unwrap

  spongeAfterIndex <- label "sponge_after_index" do
    let sponge0 = initialSpongeCircuit :: Sponge (FVar f)
    s1 <- foldM absorbChunks sponge0 vkComms.sigma
    s2 <- absorbChunks s1 vkComms.sigmaLast
    s3 <- foldM absorbChunks s2 vkComms.coeff
    foldM absorbChunks s3 vkComms.index

  digest <- label "msg_hash" do
    s1 <- label "msg_hash_absorb_app" $ foldM (flip Sponge.absorb) spongeAfterIndex appStateFields

    Tuple msg _ <- label "msg_hash_opt" $ OptSponge.runOptSpongeFromSponge s1 do
      for_ proofs \proof -> do
        OptSponge.optAbsorb (Tuple proof.mask (unwrap proof.sg).x)
        OptSponge.optAbsorb (Tuple proof.mask (unwrap proof.sg).y)
        for_ proof.rawChallenges \c ->
          OptSponge.optAbsorb (Tuple proof.mask c)
      OptSponge.optSqueeze
    pure msg

  pure { digest, spongeAfterIndex }

-- | The same digest out of circuit, with nothing masked. The
-- | bulletproof challenges arrive already expanded to full step-field
-- | elements; expanding them is the caller's job.
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
    ptFields (AffinePoint pt) = [ pt.x, pt.y ]

    -- Each commitment contributes `2 * wrapVkChunks` fields.
    chunkedFields :: ChunkedCommitment wrapVkChunks (AffinePoint f) -> Array f
    chunkedFields = Array.concatMap ptFields <<< Vector.toUnfoldable <<< unwrap

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

-- | `hashMessagesForNextStepProofPure` with one trace line per input
-- | field element, in hashing order, under the `msgForNextStep.*`
-- | prefix, and the digest as `msgForNextStep.final_digest`.
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
  -- Label format is fixed by the OCaml trace this is diffed against: a
  -- single-chunk commitment is `label.x` / `label.y`, a multi-chunk one
  -- `label.i.x` / `label.i.y` per chunk.
  let
    traceChunks :: String -> ChunkedCommitment wrapVkChunks (AffinePoint f) -> Effect Unit
    traceChunks lbl cc =
      case Vector.toUnfoldable (unwrap cc) of
        [ AffinePoint pt ] -> do
          Trace.field (lbl <> ".x") pt.x
          Trace.field (lbl <> ".y") pt.y
        cs -> forWithIndex_ cs \j (AffinePoint pt) -> do
          Trace.field (lbl <> "." <> show j <> ".x") pt.x
          Trace.field (lbl <> "." <> show j <> ".y") pt.y
  forWithIndex_ (Array.fromFoldable stepVk.sigmaComm) \i chunks ->
    traceChunks ("msgForNextStep.vk.sigma." <> show i) chunks
  forWithIndex_ (Array.fromFoldable stepVk.coefficientsComm) \i chunks ->
    traceChunks ("msgForNextStep.vk.coeff." <> show i) chunks
  traceChunks "msgForNextStep.vk.generic" stepVk.genericComm
  traceChunks "msgForNextStep.vk.psm" stepVk.psmComm
  traceChunks "msgForNextStep.vk.complete_add" stepVk.completeAddComm
  traceChunks "msgForNextStep.vk.mul" stepVk.mulComm
  traceChunks "msgForNextStep.vk.emul" stepVk.emulComm
  traceChunks "msgForNextStep.vk.endomul_scalar" stepVk.endomulScalarComm
  forWithIndex_ appState \i v ->
    Trace.field ("msgForNextStep.app_state." <> show i) v
  forWithIndex_ (Array.fromFoldable proofs) \i p -> do
    Trace.field ("msgForNextStep.prev." <> show i <> ".sg.x") (unwrap p.sg).x
    Trace.field ("msgForNextStep.prev." <> show i <> ".sg.y") (unwrap p.sg).y
    forWithIndex_ p.expandedBpChallenges \fj c ->
      Trace.field ("msgForNextStep.prev." <> show i <> ".bp_chal." <> show (getFinite fj)) c
  let digest = hashMessagesForNextStepProofPure inp
  Trace.field "msgForNextStep.final_digest" digest
  pure digest
