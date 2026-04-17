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
module Pickles.Verify.FqSpongeTranscript
  ( FqSpongeInput
  , FqSpongeOutput
  , spongeTranscriptCircuit
  , spongeTranscriptOptCircuit
  , spongeTranscriptPure
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Foldable (for_)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Unsafe (unsafePerformEffect)
import Pickles.OptSponge as OptSponge
import Pickles.Sponge (PureSpongeM, SpongeM, getSponge, getSpongeState, putSponge, putSpongeState, squeezeScalarChallenge, squeezeScalarChallengePure)
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

-- | TODO(num_chunks): When num_chunks > 1, each commitment becomes
-- | Vector numChunks (AffinePoint f). The `chunks` parameter here is the
-- | total number of tComm points (currently 7 = num_chunks * 7).
-- | wComm and zComm would similarly need chunking.
type FqSpongeInput sgOldN chunks f =
  { indexDigest :: f
  , sgOld :: Vector sgOldN (AffinePoint f)
  , publicComm :: AffinePoint f
  , wComm :: Vector 15 (AffinePoint f)
  , zComm :: AffinePoint f
  , tComm :: Vector chunks (AffinePoint f)
  }

type FqSpongeOutput f =
  { beta :: SizedF 128 f
  , gamma :: SizedF 128 f
  , alphaChal :: SizedF 128 f
  , zetaChal :: SizedF 128 f
  , digest :: f
  }

-------------------------------------------------------------------------------
-- | Circuit version
-------------------------------------------------------------------------------

-- | Sponge transcript as a Kimchi circuit.
-- |
-- | Stays in SpongeM so the caller can continue into check_bulletproof.
-- | After this action, the sponge is in `sponge_before_evaluations` state
-- | (the digest is squeezed from a copy, then the sponge is restored).
-- |
-- | Reference: step_verifier.ml:515-560
spongeTranscriptCircuit
  :: forall f sgOldN chunks t m r
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => { endo :: FVar f | r }
  -> FqSpongeInput sgOldN chunks (FVar f)
  -> SpongeM f (KimchiConstraint f) t m (FqSpongeOutput (FVar f))
spongeTranscriptCircuit params input = do
  Sponge.absorb input.indexDigest
  for_ input.sgOld Sponge.absorbPoint
  Sponge.absorbPoint input.publicComm
  for_ input.wComm Sponge.absorbPoint
  beta <- squeezeScalarChallenge params
  gamma <- squeezeScalarChallenge params
  Sponge.absorbPoint input.zComm
  alphaChal <- squeezeScalarChallenge params
  for_ input.tComm Sponge.absorbPoint
  zetaChal <- squeezeScalarChallenge params
  -- Copy sponge before squeezing digest (step_verifier.ml:559)
  spongeBeforeEvals <- getSponge
  digest <- Sponge.squeeze
  putSponge spongeBeforeEvals
  pure { beta, gamma, alphaChal, zetaChal, digest }

-------------------------------------------------------------------------------
-- | OptSponge circuit version (matches OCaml's Opt_sponge exactly)
-------------------------------------------------------------------------------

-- | Sponge transcript using OptSponge (conditional absorption with boolean flags).
-- |
-- | Matches OCaml's wrap_verifier IVP which uses Opt_sponge for all absorptions.
-- | Even for Features.none (all flags true_), this generates different constraints
-- | than the regular sponge because OptSponge uses conditional addIn/condPermute.
-- |
-- | Returns the transcript output AND the sponge state (as a regular Sponge)
-- | so the caller can continue into checkBulletproof.
-- | Returns transcript output in SpongeM — the sponge is set to sponge_before_evaluations
-- | state so the caller can continue into checkBulletproof.
spongeTranscriptOptCircuit
  :: forall f sgOldN chunks t m r
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => { endo :: FVar f | r }
  -> Vector sgOldN (Bool (FVar f)) -- actual_proofs_verified_mask
  -> FqSpongeInput sgOldN chunks (FVar f)
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
      -- 3. Absorb public_comm point
      OptSponge.optAbsorbPoint input.publicComm
      -- 4. Absorb w_comm points
      for_ input.wComm OptSponge.optAbsorbPoint
      -- 5. Squeeze beta (challenge = lowest_128_bits ~constrain_low_bits:true)
      beta <- OptSponge.optChallenge params.endo
      -- 6. Squeeze gamma
      gamma <- OptSponge.optChallenge params.endo
      -- 7. Absorb z_comm
      OptSponge.optAbsorbPoint input.zComm
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
  Sponge.liftSnarky do
    let
      dumpS labelStr v = do
        _ <- exists do
          val <- readCVar v
          let _ = unsafePerformEffect (Trace.fieldF labelStr val)
          pure val
        pure unit
    dumpS "ivp.trace.wrap.snapshot.s0" (Vector.index spongeBeforeEvals.state (unsafeFinite @3 0))
    dumpS "ivp.trace.wrap.snapshot.s1" (Vector.index spongeBeforeEvals.state (unsafeFinite @3 1))
    dumpS "ivp.trace.wrap.snapshot.s2" (Vector.index spongeBeforeEvals.state (unsafeFinite @3 2))
  digest <- Sponge.squeeze
  putSponge spongeBeforeEvals
  -- DIAG: dump the sponge state AFTER `putSponge`. Must match snapshot.
  restored <- getSponge
  Sponge.liftSnarky do
    let
      dumpR labelStr v = do
        _ <- exists do
          val <- readCVar v
          let _ = unsafePerformEffect (Trace.fieldF labelStr val)
          pure val
        pure unit
    dumpR "ivp.trace.wrap.restored.s0" (Vector.index restored.state (unsafeFinite @3 0))
    dumpR "ivp.trace.wrap.restored.s1" (Vector.index restored.state (unsafeFinite @3 1))
    dumpR "ivp.trace.wrap.restored.s2" (Vector.index restored.state (unsafeFinite @3 2))
  pure { beta: result.beta, gamma: result.gamma, alphaChal: result.alphaChal, zetaChal: result.zetaChal, digest }

-------------------------------------------------------------------------------
-- | Pure reference implementation
-------------------------------------------------------------------------------

-- | Pure sponge transcript. Same sponge-copy semantics as circuit version.
spongeTranscriptPure
  :: forall f sgOldN chunks
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => FqSpongeInput sgOldN chunks f
  -> PureSpongeM f (FqSpongeOutput f)
spongeTranscriptPure input = do
  Sponge.absorb input.indexDigest
  for_ input.sgOld Sponge.absorbPoint
  Sponge.absorbPoint input.publicComm
  for_ input.wComm Sponge.absorbPoint
  beta <- squeezeScalarChallengePure
  gamma <- squeezeScalarChallengePure
  Sponge.absorbPoint input.zComm
  alphaChal <- squeezeScalarChallengePure
  for_ input.tComm Sponge.absorbPoint
  zetaChal <- squeezeScalarChallengePure
  -- Copy sponge before squeezing digest (step_verifier.ml:559)
  spongeBeforeEvals <- getSpongeState
  digest <- Sponge.squeeze
  putSpongeState spongeBeforeEvals
  pure { beta, gamma, alphaChal, zetaChal, digest }
