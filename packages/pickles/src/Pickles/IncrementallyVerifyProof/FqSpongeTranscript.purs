-- | The fq-sponge transcript: absorb the commitments, squeeze the plonk
-- | challenges. Two versions, one over a plain sponge for step and one
-- | over an `OptSponge` for wrap; each states its own schedule.
-- |
-- | Both stay in their sponge monad so the caller can keep absorbing,
-- | into the bulletproof check. Both leave the sponge at
-- | `sponge_before_evaluations`, the state right before the digest
-- | squeeze.
module Pickles.IncrementallyVerifyProof.FqSpongeTranscript
  ( FqSpongeInput
  , FqSpongeOutput
  , FqSpongeStepInput
  , FqSpongeStepOutput
  , spongeTranscriptCircuit
  , spongeTranscriptOptCircuit
  , assertPlonkChallenges
  , ivpTrace
  ) where

import Prelude

import Data.Fin (getFinite, unsafeFinite)
import Data.Foldable (for_)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Newtype (unwrap)
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Unsafe (unsafePerformEffect)
import Pickles.DeferredValues (PlonkMinimal)
import Pickles.OptSponge as OptSponge
import Pickles.Sponge (SpongeM, getSponge, labelM, liftSnarky, putSponge)
import Pickles.Sponge as Sponge
import Pickles.Trace as Trace
import Pickles.Types (ChunkedCommitment)
import Poseidon (class PoseidonField)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class BasicSystem, Bool(..), BoolVar, FVar, SizedF, Snarky, assertEq, exists, label, readCVar, true_)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint(..))

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | Commitments enter chunked: `wComm` is 15 polynomials with
-- | `stepChunks` sub-commitments each, `zComm` is one such polynomial,
-- | and `tComm` is the t-poly's flat chunk list, of length
-- | `tCommLen = 7 * stepChunks`.
type FqSpongeInput sgOldN stepChunks tCommLen f =
  { indexDigest :: f
  , sgOld :: Vector sgOldN (AffinePoint f)
  -- The chunked public-input commitment, each chunk absorbed
  -- separately. It reuses `stepChunks` because both counts come from
  -- the same step-domain-over-wrap-SRS ratio.
  , publicComm :: ChunkedCommitment stepChunks (AffinePoint f)
  , wComm :: Vector 15 (ChunkedCommitment stepChunks (AffinePoint f))
  , zComm :: ChunkedCommitment stepChunks (AffinePoint f)
  , tComm :: Vector tCommLen (AffinePoint f)
  }

type FqSpongeOutput f =
  { beta :: SizedF 128 f
  , gamma :: SizedF 128 f
  , alphaChal :: SizedF 128 f
  , zetaChal :: SizedF 128 f
  , digest :: f
  }

-- | The step side's transcript input: everything but `x_hat`, which the
-- | caller computes at its point in `spongeTranscriptCircuit`'s
-- | schedule.
type FqSpongeStepInput sgOldN stepChunks tCommLen f =
  { indexDigest :: f
  , sgOld :: Vector sgOldN (AffinePoint f)
  , wComm :: Vector 15 (ChunkedCommitment stepChunks (AffinePoint f))
  , zComm :: ChunkedCommitment stepChunks (AffinePoint f)
  , tComm :: Vector tCommLen (AffinePoint f)
  }

-- | `FqSpongeOutput` plus the `x_hat` computed inside the schedule.
type FqSpongeStepOutput stepChunks f =
  { xHat :: Vector stepChunks (AffinePoint f)
  , beta :: SizedF 128 f
  , gamma :: SizedF 128 f
  , alphaChal :: SizedF 128 f
  , zetaChal :: SizedF 128 f
  , digest :: f
  }

-- | Trace a circuit value under a label: an `exists` read, no
-- | constraint. The verifiers emit these at fixed points of their
-- | schedules, so the gadgets keep them in place.
ivpTrace
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => String
  -> FVar f
  -> Snarky f c r Unit
ivpTrace labelStr v = do
  _ <- exists do
    val <- readCVar v
    let _ = unsafePerformEffect (Trace.fieldF labelStr val)
    pure val
  pure unit

-- | Assert the four squeezed prechallenges equal the deferred plonk
-- | claims: `β`, `γ`, `α`, `ζ`, in that order.
assertPlonkChallenges
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => FqSpongeOutput (FVar f)
  -> PlonkMinimal (FVar f)
  -> Snarky f c r Unit
assertPlonkChallenges squeezed expected = do
  label "ivp_assert_plonk_beta" $ assertEq squeezed.beta expected.beta
  label "ivp_assert_plonk_gamma" $ assertEq squeezed.gamma expected.gamma
  label "ivp_assert_plonk_alpha" $ assertEq squeezed.alphaChal expected.alpha
  label "ivp_assert_plonk_zeta" $ assertEq squeezed.zetaChal expected.zeta

-- | The step side's transcript over a plain sponge. The schedule is
-- | fixed: absorb the index digest and `sg_old`; run the caller's
-- | `x_hat` computation there, so its rows land between the `sg_old`
-- | and `x_hat` absorbs; absorb `x_hat` and `w_comm`; squeeze `β` and
-- | `γ` as challenges; absorb `z_comm`; squeeze `α` as a scalar
-- | challenge; absorb `t_comm`; squeeze `ζ` likewise; squeeze the
-- | digest from a copy, leaving the sponge at
-- | `sponge_before_evaluations`.
spongeTranscriptCircuit
  :: forall f sgOldN stepChunks tCommLen r cr
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => Reflectable sgOldN Int
  => Reflectable stepChunks Int
  => Reflectable tCommLen Int
  => { endo :: FVar f | r }
  -> FqSpongeStepInput sgOldN stepChunks tCommLen (FVar f)
  -> SpongeM f (KimchiConstraint f) cr (Vector stepChunks (AffinePoint (FVar f)))
  -> SpongeM f (KimchiConstraint f) cr (FqSpongeStepOutput stepChunks (FVar f))
spongeTranscriptCircuit params input computeXHat = do
  liftSnarky $ ivpTrace "ivp.trace.index_digest" input.indexDigest
  labelM "ivp_absorb_index_digest" $ Sponge.absorb input.indexDigest
  labelM "ivp_absorb_sg_old" do
    liftSnarky $ forWithIndex_ input.sgOld \fi (AffinePoint pt) -> do
      let i = getFinite fi
      ivpTrace ("ivp.trace.sg_old." <> show i <> ".x") pt.x
      ivpTrace ("ivp.trace.sg_old." <> show i <> ".y") pt.y
    for_ input.sgOld \(AffinePoint pt) -> do
      labelM "ivp_sg_x" $ Sponge.absorb pt.x
      labelM "ivp_sg_y" $ Sponge.absorb pt.y
  xHat <- computeXHat
  liftSnarky $ forWithIndex_ xHat \fi (AffinePoint pt) -> do
    let i = getFinite fi
    if i == 0 then do
      ivpTrace "ivp.trace.xhat.x" pt.x
      ivpTrace "ivp.trace.xhat.y" pt.y
    else do
      ivpTrace ("ivp.trace.xhat." <> show i <> ".x") pt.x
      ivpTrace ("ivp.trace.xhat." <> show i <> ".y") pt.y
  for_ xHat Sponge.absorbPoint
  liftSnarky $ forWithIndex_ input.wComm \fi cc ->
    forWithIndex_ (unwrap cc) \fj (AffinePoint pt) -> do
      let i = getFinite fi
      let j = getFinite fj
      ivpTrace ("ivp.trace.w_comm." <> show i <> "." <> show j <> ".x") pt.x
      ivpTrace ("ivp.trace.w_comm." <> show i <> "." <> show j <> ".y") pt.y
  for_ input.wComm \cc -> for_ (unwrap cc) Sponge.absorbPoint
  beta <- Sponge.squeezeScalarChallenge params
  liftSnarky $ ivpTrace "ivp.trace.beta_squeezed" (SizedF.toField beta)
  gamma <- Sponge.squeezeScalarChallenge params
  liftSnarky $ ivpTrace "ivp.trace.gamma_squeezed" (SizedF.toField gamma)
  liftSnarky $ forWithIndex_ (unwrap input.zComm) \fj (AffinePoint pt) -> do
    let j = getFinite fj
    ivpTrace ("ivp.trace.zcomm." <> show j <> ".x") pt.x
    ivpTrace ("ivp.trace.zcomm." <> show j <> ".y") pt.y
  for_ (unwrap input.zComm) Sponge.absorbPoint
  alphaChal <- Sponge.squeezeScalar params
  liftSnarky $ ivpTrace "ivp.trace.alpha_squeezed" (SizedF.toField alphaChal)
  liftSnarky $ forWithIndex_ input.tComm \fi (AffinePoint pt) -> do
    let i = getFinite fi
    ivpTrace ("ivp.trace.tcomm." <> show i <> ".x") pt.x
    ivpTrace ("ivp.trace.tcomm." <> show i <> ".y") pt.y
  for_ input.tComm Sponge.absorbPoint
  zetaChal <- Sponge.squeezeScalar params
  liftSnarky $ ivpTrace "ivp.trace.zeta_squeezed" (SizedF.toField zetaChal)
  spongeBeforeEvals <- getSponge
  digest <- Sponge.squeeze
  liftSnarky $ ivpTrace "ivp.trace.digest" digest
  putSponge spongeBeforeEvals
  pure { xHat, beta, gamma, alphaChal, zetaChal, digest }

-- | The wrap side's transcript, over an `OptSponge` so that `sg_old` is
-- | absorbed only where the proofs-verified mask keeps it. The schedule
-- | is `spongeTranscriptCircuit`'s, except that `x_hat` arrives already
-- | computed, as `publicComm`.
spongeTranscriptOptCircuit
  :: forall f sgOldN stepChunks tCommLen r cr
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => { endo :: FVar f | r }
  -> Vector sgOldN (Bool (FVar f)) -- ^ the actual-proofs-verified mask
  -> FqSpongeInput sgOldN stepChunks tCommLen (FVar f)
  -> SpongeM f (KimchiConstraint f) cr (FqSpongeOutput (FVar f))
spongeTranscriptOptCircuit params sgOldMask input = do
  result <- Sponge.liftSnarky do
    Tuple r _ <- OptSponge.runOptSpongeM do
      OptSponge.optAbsorb (Tuple true_ input.indexDigest)
      for_ (Vector.zip sgOldMask input.sgOld) \(Tuple bKeep (AffinePoint sg)) -> do
        let keep = coerce bKeep :: BoolVar f
        OptSponge.optAbsorb (Tuple keep sg.x)
        OptSponge.optAbsorb (Tuple keep sg.y)
      for_ (unwrap input.publicComm) OptSponge.optAbsorbPoint
      for_ input.wComm \chunks -> for_ (unwrap chunks) OptSponge.optAbsorbPoint
      preBetaState <- OptSponge.peekPreSqueezeState
      let
        traceOne lbl v = OptSponge.liftSnarky $ do
          _ <- exists $ do
            val <- readCVar v
            let _ = unsafePerformEffect (Trace.field lbl val)
            pure val
          pure unit
      traceOne "ivp.trace.wrap.before_beta.s0" (Vector.index preBetaState (unsafeFinite @3 0))
      traceOne "ivp.trace.wrap.before_beta.s1" (Vector.index preBetaState (unsafeFinite @3 1))
      traceOne "ivp.trace.wrap.before_beta.s2" (Vector.index preBetaState (unsafeFinite @3 2))
      beta <- OptSponge.optChallenge params.endo
      gamma <- OptSponge.optChallenge params.endo
      for_ (unwrap input.zComm) OptSponge.optAbsorbPoint
      alphaChal <- OptSponge.optScalarChallenge params.endo
      for_ input.tComm OptSponge.optAbsorbPoint
      zetaChal <- OptSponge.optScalarChallenge params.endo
      regularSponge <- OptSponge.toRegularSponge
      pure { beta, gamma, alphaChal, zetaChal, regularSponge }
    pure r
  putSponge result.regularSponge
  -- The digest is squeezed from a copy, so the sponge is left at
  -- `sponge_before_evaluations`.
  spongeBeforeEvals <- getSponge
  digest <- Sponge.squeeze
  putSponge spongeBeforeEvals
  pure { beta: result.beta, gamma: result.gamma, alphaChal: result.alphaChal, zetaChal: result.zetaChal, digest }

