-- | Sponge transcript for proof verification.
-- |
-- | Replays the Fiat-Shamir transcript by absorbing commitments and squeezing
-- | challenges, matching the sequence from kimchi/src/verifier.rs:
-- |   1. absorb VK digest
-- |   2. absorb prev_challenges commitments (empty for base case)
-- |   3. absorb public_comm point
-- |   4. absorb w_comm[0..14] points
-- |   5. squeeze beta
-- |   6. squeeze gamma
-- |   7. absorb z_comm point
-- |   8. squeeze alpha
-- |   9. absorb t_comm points
-- |  10. squeeze zeta
-- |  11. digest (full squeeze)
-- |
-- | Field-polymorphic: works on whichever field the circuit is native to.
-- |
-- | Both versions stay in their sponge monad so the caller can continue
-- | sponge operations (e.g., into check_bulletproof). After the action,
-- | the sponge state is `sponge_before_evaluations` — the state right before
-- | the digest squeeze, matching OCaml's `Sponge.copy` pattern in
-- | step_verifier.ml:559.
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
import Pickles.OptSponge as OptSponge
import Pickles.Sponge (SpongeM, getSponge, labelM, liftSnarky, putSponge)
import Pickles.Sponge as Sponge
import Pickles.Trace as Trace
import Pickles.Types (ChunkedCommitment)
import Pickles.Verify.Types (PlonkMinimal)
import Poseidon (class PoseidonField)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class BasicSystem, Bool(..), BoolVar, FVar, SizedF, Snarky, assertEq, exists, label, readCVar, true_)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint(..))

-------------------------------------------------------------------------------
-- | Statically-sized circuit input for the sponge transcript.
-- | `chunks` is the number of t_comm chunks (= 7 * ceil(domain_size / max_poly_size)).
-------------------------------------------------------------------------------

-- | Polynomial commitments enter chunked: `wComm` is 15 polynomials each
-- | with `stepChunks` sub-commitments, `zComm` is one polynomial with
-- | `stepChunks` sub-commitments. `tComm` is the t-poly's flat chunk list
-- | of length `tCommLen = 7 * stepChunks` (at n=1, tCommLen = 7).
type FqSpongeInput sgOldN stepChunks tCommLen f =
  { indexDigest :: f
  , sgOld :: Vector sgOldN (AffinePoint f)
  -- | Chunked public-input commitment. At nc=1 this is a 1-element
  -- | vector (legacy behavior); at nc>1 each chunk is absorbed
  -- | separately, matching OCaml `Array.iter x_hat ~f:(absorb sponge PC)`
  -- | (wrap_verifier.ml:1042). Reuses `stepChunks` from w_comm/z_comm
  -- | since both derive from the same step-domain-over-wrap-SRS ratio.
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

-- | The step side's transcript input: everything but `x_hat`, which the caller
-- | computes at its point in the schedule (see `spongeTranscriptCircuit`).
type FqSpongeStepInput sgOldN stepChunks tCommLen f =
  { indexDigest :: f
  , sgOld :: Vector sgOldN (AffinePoint f)
  , wComm :: Vector 15 (ChunkedCommitment stepChunks (AffinePoint f))
  , zComm :: ChunkedCommitment stepChunks (AffinePoint f)
  , tComm :: Vector tCommLen (AffinePoint f)
  }

-- | The step side's transcript output: `FqSpongeOutput` plus the `x_hat` computed
-- | inside the schedule.
type FqSpongeStepOutput stepChunks f =
  { xHat :: Vector stepChunks (AffinePoint f)
  , beta :: SizedF 128 f
  , gamma :: SizedF 128 f
  , alphaChal :: SizedF 128 f
  , zetaChal :: SizedF 128 f
  , digest :: f
  }

-- | Trace a circuit value under a label (an `exists` read; no constraint). The
-- | verifiers emit these at fixed points of their schedules, so the gadgets
-- | keep them in place.
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

-- | Assert the four squeezed prechallenges equal the deferred plonk claims
-- | (`step_verifier.ml:706-712`): `β, γ, α, ζ` in that order.
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

-- | The step side's transcript over the plain sponge (OCaml `step_verifier.ml:567-705`,
-- | kimchi `verifier.rs:156-283` with pickles' `sg_old` absorbs after the index
-- | digest): absorb the index digest and `sg_old`; run the caller's `x_hat`
-- | computation at that point, as OCaml does, so its rows land between the
-- | `sg_old` and `x_hat` absorbs; absorb `x_hat` and `w_comm`; squeeze β, γ by
-- | `squeeze_challenge`; absorb `z_comm`; squeeze α by `squeeze_scalar`; absorb
-- | `t_comm`; squeeze ζ by `squeeze_scalar`; squeeze the digest from a copy,
-- | leaving the sponge at `sponge_before_evaluations`.
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

spongeTranscriptOptCircuit
  :: forall f sgOldN stepChunks tCommLen r cr
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => { endo :: FVar f | r }
  -> Vector sgOldN (Bool (FVar f)) -- actual_proofs_verified_mask
  -> FqSpongeInput sgOldN stepChunks tCommLen (FVar f)
  -> SpongeM f (KimchiConstraint f) cr (FqSpongeOutput (FVar f))
spongeTranscriptOptCircuit params sgOldMask input = do
  -- Run the Opt sponge transcript in Snarky (not SpongeM)
  result <- Sponge.liftSnarky do
    Tuple r _ <- OptSponge.runOptSpongeM do
      -- 1. Absorb index digest
      OptSponge.optAbsorb (Tuple true_ input.indexDigest)
      -- 2. Absorb sg_old points with actual_proofs_verified_mask
      -- OCaml: Vector.iter ~f:(absorb sponge PC) sg_old where sg_old = map2 mask sg ~f:(keep, sg)
      for_ (Vector.zip sgOldMask input.sgOld) \(Tuple bKeep (AffinePoint sg)) -> do
        let keep = coerce bKeep :: BoolVar f
        OptSponge.optAbsorb (Tuple keep sg.x)
        OptSponge.optAbsorb (Tuple keep sg.y)
      -- 3. Absorb public_comm chunks. OCaml: `Array.iter x_hat ~f:(absorb
      -- sponge PC)` (wrap_verifier.ml:1042). For nc=1 this is one absorb.
      for_ (unwrap input.publicComm) OptSponge.optAbsorbPoint
      -- 4. Absorb w_comm points (per-polynomial, per-chunk)
      for_ input.wComm \chunks -> for_ (unwrap chunks) OptSponge.optAbsorbPoint
      -- DIAG iter 2aa: dump circuit sponge state before beta squeeze for
      -- direct comparison to kimchi-native ground truth. First divergence
      -- point localizes whether mismatch is in absorb data or sponge math.
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
      -- 5. Squeeze beta (challenge = lowest_128_bits ~constrain_low_bits:true)
      beta <- OptSponge.optChallenge params.endo
      -- 6. Squeeze gamma
      gamma <- OptSponge.optChallenge params.endo
      -- 7. Absorb z_comm chunks
      for_ (unwrap input.zComm) OptSponge.optAbsorbPoint
      -- 8. Squeeze alpha (scalar_challenge = lowest_128_bits ~constrain_low_bits:false)
      alphaChal <- OptSponge.optScalarChallenge params.endo
      -- 9. Absorb t_comm
      for_ input.tComm OptSponge.optAbsorbPoint
      -- 10. Squeeze zeta
      zetaChal <- OptSponge.optScalarChallenge params.endo
      -- 11. Convert to regular sponge for continuation
      regularSponge <- OptSponge.toRegularSponge
      pure { beta, gamma, alphaChal, zetaChal, regularSponge }
    pure r
  -- Set the SpongeM state to sponge_before_evaluations
  putSponge result.regularSponge
  -- Copy sponge before squeezing digest (step_verifier.ml:559)
  spongeBeforeEvals <- getSponge
  -- DIAG: dump the snapshot state we're about to restore to.
  digest <- Sponge.squeeze
  putSponge spongeBeforeEvals
  pure { beta: result.beta, gamma: result.gamma, alphaChal: result.alphaChal, zetaChal: result.zetaChal, digest }

