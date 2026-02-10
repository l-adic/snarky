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
  , spongeTranscriptPure
  ) where

import Prelude

import Data.Foldable (for_)
import Data.Vector (Vector)
import Pickles.Sponge (PureSpongeM, SpongeM, getSponge, getSpongeState, putSponge, putSpongeState, squeezeScalarChallenge, squeezeScalarChallengePure)
import Pickles.Sponge as Sponge
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (class CircuitM, FVar, SizedF)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint)

-------------------------------------------------------------------------------
-- | Statically-sized circuit input for the sponge transcript.
-- | `chunks` is the number of t_comm chunks (= 7 * ceil(domain_size / max_poly_size)).
-------------------------------------------------------------------------------

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
  :: forall f sgOldN chunks t m
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => FqSpongeInput sgOldN chunks (FVar f)
  -> SpongeM f (KimchiConstraint f) t m (FqSpongeOutput (FVar f))
spongeTranscriptCircuit input = do
  Sponge.absorb input.indexDigest
  for_ input.sgOld Sponge.absorbPoint
  Sponge.absorbPoint input.publicComm
  for_ input.wComm Sponge.absorbPoint
  beta <- squeezeScalarChallenge
  gamma <- squeezeScalarChallenge
  Sponge.absorbPoint input.zComm
  alphaChal <- squeezeScalarChallenge
  for_ input.tComm Sponge.absorbPoint
  zetaChal <- squeezeScalarChallenge
  -- Copy sponge before squeezing digest (step_verifier.ml:559)
  spongeBeforeEvals <- getSponge
  digest <- Sponge.squeeze
  putSponge spongeBeforeEvals
  pure { beta, gamma, alphaChal, zetaChal, digest }

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
