-- | Hash messages for the next Wrap proof.
-- |
-- | Computes `hash(padding_challenges, expanded_challenges, sg.x, sg.y)` where:
-- | - `padding_challenges` are dummy expanded challenges (prepended for padding)
-- | - `expanded_challenges` are the real bulletproof challenges expanded via endo
-- | - `sg` is the challenge polynomial commitment from the opening proof
-- |
-- | The serialization order follows OCaml's `wrap_hack.ml`:
-- | `[dummy_chals..., real_chals..., sg.x, sg.y]`
-- |
-- | For n=1 proof verified, padding extends to 2 vectors by prepending 1 dummy.
-- |
-- | Reference: mina/src/lib/pickles/wrap_hack.ml:45-59
module Pickles.Wrap.MessageHash
  ( hashMessagesForNextWrapProof
  , hashMessagesForNextWrapProofPureGeneral
  , hashMessagesForNextWrapProofCircuit'
  , dummyPaddingSpongeStates
  ) where

import Prelude

import Data.Foldable (class Foldable, for_)
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.Sponge (SpongeM, absorb, absorbMany, getSpongeState, initialSponge, labelM, runPureSpongeM, squeeze)
import Pickles.Sponge as Pickles.Sponge
import Poseidon (class PoseidonField, hash)
import RandomOracle.Sponge (Sponge)
import Snarky.Circuit.DSL (class CircuitM, FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Pure version: hash messages for next Wrap proof.
-- |
-- | Used out-of-circuit by the test infrastructure / prover to compute
-- | the expected hash value for the WrapStatement public input.
hashMessagesForNextWrapProof
  :: forall d f
   . PoseidonField f
  => Reflectable d Int
  => { sg :: AffinePoint f
     , expandedChallenges :: Vector d f
     , dummyChallenges :: Vector d f
     }
  -> f
hashMessagesForNextWrapProof { sg, expandedChallenges, dummyChallenges } =
  let
    -- Serialization: [dummy_chals..., real_chals..., sg.x, sg.y]
    fields =
      Vector.toUnfoldable dummyChallenges
        <> Vector.toUnfoldable expandedChallenges
        <> [ sg.x, sg.y ]
  in
    hash fields

-- | General pure version of OCaml `Wrap_hack.hash_messages_for_next_wrap_proof`
-- | (`mina/src/lib/crypto/pickles/wrap_hack.ml:46-59`).
-- |
-- | Accepts the challenges **already padded** (caller is responsible for
-- | prepending dummies to reach `Wrap_hack.Padded_length.n = 2`). Each inner
-- | vector is an expanded wrap-field bp-challenge vector of length `d`.
-- |
-- | Serialization order matches OCaml `Messages_for_next_wrap_proof.to_field_elements`:
-- | flatten all padded challenge vectors, then append `sg.x`, `sg.y`.
hashMessagesForNextWrapProofPureGeneral
  :: forall n d f
   . PoseidonField f
  => { sg :: AffinePoint f
     , paddedChallenges :: Vector n (Vector d f)
     }
  -> f
hashMessagesForNextWrapProofPureGeneral { sg, paddedChallenges } =
  let
    outer :: Array (Vector d f)
    outer = Vector.toUnfoldable paddedChallenges

    flatChals :: Array f
    flatChals = outer >>= (Vector.toUnfoldable :: Vector d f -> Array f)
  in
    hash (flatChals <> [ sg.x, sg.y ])

hashMessagesForNextWrapProofCircuit'
  :: forall outer d f t m
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Foldable outer
  => Reflectable d Int
  => { sg :: AffinePoint (FVar f)
     , allChallenges :: outer (Vector d (FVar f))
     }
  -> SpongeM f (KimchiConstraint f) t m (FVar f)
hashMessagesForNextWrapProofCircuit' { sg, allChallenges } = labelM "hash-messages-for-next-wrap-proof" do
  -- Absorb all challenge vectors in order (flattened)
  for_ allChallenges \chals ->
    Pickles.Sponge.absorbMany chals
  -- Absorb sg point
  absorb sg.x
  absorb sg.y
  -- Squeeze digest
  squeeze

-- | Pre-computed sponge states after absorbing 0, 1, or 2 dummy challenge
-- | vectors. Used to start the message hash sponge from a checkpoint,
-- | avoiding in-circuit Poseidon gates for dummy absorption.
-- |
-- | Index i = sponge state after absorbing i dummy vectors.
-- | For max_proofs_verified = n, use index (MaxProofsVerified - n).
-- |
-- | Reference: mina/src/lib/crypto/pickles/wrap_hack.ml:96-110
dummyPaddingSpongeStates
  :: forall d f
   . PoseidonField f
  => Reflectable d Int
  => Vector d f
  -> Vector 3 (Sponge f)
dummyPaddingSpongeStates dummyChallenges =
  let
    go sponge = runPureSpongeM sponge do
      absorbMany dummyChallenges
      getSpongeState
    Tuple _ s0 = runPureSpongeM (initialSponge :: Sponge f) getSpongeState
    Tuple _ s1 = go s0
    Tuple _ s2 = go s1
  in
    -- Indexed by n (number of real challenge vectors provided):
    -- index 0 = n=0 (2 dummies absorbed), index 1 = n=1, index 2 = n=2 (fresh sponge)
    s2 :< s1 :< s0 :< Vector.nil
