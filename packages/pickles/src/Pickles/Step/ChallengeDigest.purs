-- | Challenge digest computation for Step circuit.
-- |
-- | When the Step circuit verifies previous Wrap proofs, it computes a
-- | challenge digest by conditionally absorbing old bulletproof challenges
-- | based on which previous proofs are "real" vs "dummy".
-- |
-- | Uses OptSponge which tracks sponge position as a circuit boolean,
-- | matching OCaml's `Opt_sponge` exactly.
-- |
-- | Reference: step_verifier.ml:880-909 (challenge digest computation)
module Pickles.Step.ChallengeDigest
  ( ChallengeDigestInput
  , challengeDigestCircuit
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldMap)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.OptSponge as OptSponge
import Pickles.Verify.Types (BulletproofChallenges)
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky)
import Snarky.Circuit.DSL as SizedF
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)

-- | Input for challenge digest computation.
-- |
-- | - `mask`: For each previous proof, whether it's "real" (should be absorbed)
-- | - `oldChallenges`: The bulletproof challenges from each previous proof
-- |
-- | Reference: step_verifier.ml:880-909
type ChallengeDigestInput n d f b =
  { mask :: Vector n b
  , oldChallenges :: Vector n (BulletproofChallenges d f)
  }

-- | Compute the challenge digest from old bulletproof challenges.
-- |
-- | Uses OptSponge to conditionally absorb challenges based on a mask,
-- | matching OCaml's constraint structure exactly.
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
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => ChallengeDigestInput n d (FVar f) (BoolVar f)
  -> Snarky (KimchiConstraint f) t m (FVar f)
challengeDigestCircuit { mask, oldChallenges } =
  let
    pending = Array.fromFoldable $ foldMap
      ( \(Tuple keep chals) ->
          map (Tuple keep <<< SizedF.toField) (Array.fromFoldable chals)
      )
      (Vector.zip mask oldChallenges)
  in
    OptSponge.squeeze OptSponge.create pending
