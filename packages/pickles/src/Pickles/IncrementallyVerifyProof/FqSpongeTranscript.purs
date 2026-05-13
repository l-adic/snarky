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
  , spongeTranscriptOptCircuit
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Foldable (for_)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Unsafe (unsafePerformEffect)
import Pickles.OptSponge as OptSponge
import Pickles.Sponge (SpongeM, getSponge, putSponge)
import Pickles.Sponge as Sponge
import Pickles.Trace as Trace
import Poseidon (class PoseidonField)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, FVar, SizedF, exists, readCVar, true_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint)

-------------------------------------------------------------------------------
-- | Statically-sized circuit input for the sponge transcript.
-- | `chunks` is the number of t_comm chunks (= 7 * ceil(domain_size / max_poly_size)).
-------------------------------------------------------------------------------

-- | Polynomial commitments enter chunked: `wComm` is 15 polynomials each
-- | with `numChunks` sub-commitments, `zComm` is one polynomial with
-- | `numChunks` sub-commitments. `tComm` is the t-poly's flat chunk list
-- | of length `tCommLen = 7 * numChunks` (at n=1, tCommLen = 7).
type FqSpongeInput sgOldN numChunks tCommLen f =
  { indexDigest :: f
  , sgOld :: Vector sgOldN (AffinePoint f)
  -- | Chunked public-input commitment. At nc=1 this is a 1-element
  -- | vector (legacy behavior); at nc>1 each chunk is absorbed
  -- | separately, matching OCaml `Array.iter x_hat ~f:(absorb sponge PC)`
  -- | (wrap_verifier.ml:1042). Reuses `numChunks` from w_comm/z_comm
  -- | since both derive from the same step-domain-over-wrap-SRS ratio.
  , publicComm :: Vector numChunks (AffinePoint f)
  , wComm :: Vector 15 (Vector numChunks (AffinePoint f))
  , zComm :: Vector numChunks (AffinePoint f)
  , tComm :: Vector tCommLen (AffinePoint f)
  }

type FqSpongeOutput f =
  { beta :: SizedF 128 f
  , gamma :: SizedF 128 f
  , alphaChal :: SizedF 128 f
  , zetaChal :: SizedF 128 f
  , digest :: f
  }

spongeTranscriptOptCircuit
  :: forall f sgOldN numChunks tCommLen t m r
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => { endo :: FVar f | r }
  -> Vector sgOldN (Bool (FVar f)) -- actual_proofs_verified_mask
  -> FqSpongeInput sgOldN numChunks tCommLen (FVar f)
  -> SpongeM f (KimchiConstraint f) t m (FqSpongeOutput (FVar f))
spongeTranscriptOptCircuit params sgOldMask input = do
  -- Run the Opt sponge transcript in Snarky (not SpongeM)
  result <- Sponge.liftSnarky do
    Tuple r _ <- OptSponge.runOptSpongeM do
      -- 1. Absorb index digest
      OptSponge.optAbsorb (Tuple true_ input.indexDigest)
      -- 2. Absorb sg_old points with actual_proofs_verified_mask
      -- OCaml: Vector.iter ~f:(absorb sponge PC) sg_old where sg_old = map2 mask sg ~f:(keep, sg)
      for_ (Vector.zip sgOldMask input.sgOld) \(Tuple bKeep sg) -> do
        let keep = coerce bKeep :: BoolVar f
        OptSponge.optAbsorb (Tuple keep sg.x)
        OptSponge.optAbsorb (Tuple keep sg.y)
      -- 3. Absorb public_comm chunks. OCaml: `Array.iter x_hat ~f:(absorb
      -- sponge PC)` (wrap_verifier.ml:1042). For nc=1 this is one absorb.
      for_ input.publicComm OptSponge.optAbsorbPoint
      -- 4. Absorb w_comm points (per-polynomial, per-chunk)
      for_ input.wComm \chunks -> for_ chunks OptSponge.optAbsorbPoint
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
      for_ input.zComm OptSponge.optAbsorbPoint
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

