-- | Challenge digest computation for Step circuit.
-- |
-- | When the Step circuit verifies previous Wrap proofs, it computes a
-- | challenge digest by conditionally absorbing old bulletproof challenges
-- | based on which previous proofs are "real" vs "dummy".
-- |
-- | The conditional absorption uses an "optional sponge" pattern: when the
-- | mask is true, absorb the value; when false, leave sponge state unchanged.
-- |
-- | Reference: step_verifier.ml:880-909 (challenge digest computation)
module Pickles.Step.ChallengeDigest
  ( -- * Conditional Sponge Operations
    absorbConditional
  , absorbManyConditional
  -- * Challenge Digest
  , ChallengeDigestInput
  , challengeDigestCircuit
  ) where

import Prelude

import Control.Monad.State.Trans (StateT(..))
import Data.Newtype (wrap)
import Data.Traversable (for_)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Sponge (SpongeM, squeeze)
import Pickles.Verify.Types (BulletproofChallenges)
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, if_)
import Snarky.Circuit.DSL as SizedF
import Snarky.Circuit.RandomOracle.Sponge as CircuitSponge
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)

-------------------------------------------------------------------------------
-- | Conditional Sponge Operations
-------------------------------------------------------------------------------

-- | Conditionally absorb a field element into the sponge.
-- |
-- | When `keep = true`, absorb the value. When `keep = false`, leave the
-- | sponge state unchanged.
-- |
-- | This implements the "optional sponge" pattern from OCaml's `Opt_sponge`.
-- |
-- | In circuit-land, both branches are computed but `if_` selects between:
-- | - New sponge state (after absorption)
-- | - Original sponge state (unchanged)
absorbConditional
  :: forall f t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => BoolVar f
  -> FVar f
  -> SpongeM f (KimchiConstraint f) t m Unit
absorbConditional keep x = wrap $ StateT \oldSponge -> do
  -- Compute what the new state would be after absorption
  newSponge <- CircuitSponge.absorb x oldSponge

  -- Use if_ to conditionally select between new and old state vectors
  -- The spongeState metadata tracks absorb/squeeze mode - we use the
  -- newSponge's spongeState since we're always in "absorbing" mode here.
  resultState <- if_ keep newSponge.state oldSponge.state

  pure $ Tuple unit { state: resultState, spongeState: newSponge.spongeState }

-- | Conditionally absorb many field elements.
-- |
-- | All elements share the same `keep` flag, so either all are absorbed
-- | or none are.
absorbManyConditional
  :: forall f n t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => BoolVar f
  -> Vector n (FVar f)
  -> SpongeM f (KimchiConstraint f) t m Unit
absorbManyConditional keep xs = for_ xs (absorbConditional keep)

-------------------------------------------------------------------------------
-- | Challenge Digest
-------------------------------------------------------------------------------

-- | Input for challenge digest computation.
-- |
-- | This contains:
-- | - `mask`: For each previous proof, whether it's "real" (should be absorbed)
-- | - `oldChallenges`: The bulletproof challenges from each previous proof
-- |
-- | The mask determines which proofs' challenges get absorbed into the sponge.
-- | Dummy proofs (mask = false) don't contribute to the digest.
-- |
-- | Reference: step_verifier.ml:880-909
type ChallengeDigestInput n d f b =
  { -- | Which previous proofs are real (should have challenges absorbed)
    mask :: Vector n b
  , -- | Bulletproof challenges from each previous proof (d challenges each)
    oldChallenges :: Vector n (BulletproofChallenges d f)
  }

-- | Compute the challenge digest from old bulletproof challenges.
-- |
-- | This circuit:
-- | 1. Takes a mask indicating which previous proofs are "real"
-- | 2. For each proof where mask = true, absorbs all bulletproof challenges
-- | 3. Squeezes the sponge to get the final digest
-- |
-- | The caller should initialize the sponge before calling this circuit.
-- | The sponge state after this call can be used for further operations.
-- |
-- | Reference: step_verifier.ml:880-909
-- |
-- | ```ocaml
-- | let challenge_digest =
-- |   let opt_sponge = Opt_sponge.create sponge_params in
-- |   Vector.iter2
-- |     actual_width_mask
-- |     prev_challenges
-- |     ~f:(fun keep chals ->
-- |       Vector.iter chals ~f:(fun chal ->
-- |           Opt_sponge.absorb opt_sponge (keep, chal) ) ) ;
-- |   Opt_sponge.squeeze opt_sponge
-- | ```
challengeDigestCircuit
  :: forall n d f t m
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => ChallengeDigestInput n d (FVar f) (BoolVar f)
  -> SpongeM f (KimchiConstraint f) t m (FVar f)
challengeDigestCircuit { mask, oldChallenges } = do
  -- Absorb challenges from each previous proof based on mask
  for_ (Vector.zip mask oldChallenges) \(Tuple keep chals) ->
    -- For each proof, absorb all scalar challenges
    for_ chals \chal ->
      absorbConditional keep (SizedF.toField chal)

  -- Squeeze to get the digest
  squeeze
