-- | The messages-for-next-wrap-proof digest: a pure form, a circuit
-- | form, and the sponge checkpoints that keep padding out of circuit.
-- |
-- | Absorption order is fixed by the verifier's transcript: the padded
-- | challenge vectors, flattened, then `sg.x`, then `sg.y`.
module Pickles.Wrap.MessageHash
  ( hashMessagesForNextWrapProofPureGeneral
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
import Snarky.Circuit.DSL (FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint(..))

-- | The messages-for-next-wrap-proof digest, computed out of circuit.
-- | The challenges must already be padded to `PaddedLength` by the
-- | caller; each inner vector is one expanded bullet-proof challenge
-- | stack of length `d`.
hashMessagesForNextWrapProofPureGeneral
  :: forall n d f
   . PoseidonField f
  => { sg :: AffinePoint f
     , paddedChallenges :: Vector n (Vector d f)
     }
  -> f
hashMessagesForNextWrapProofPureGeneral { sg: AffinePoint sg, paddedChallenges } =
  let
    outer = Vector.toUnfoldable paddedChallenges

    flatChals = outer >>= (Vector.toUnfoldable)
  in
    hash (flatChals <> [ sg.x, sg.y ])

hashMessagesForNextWrapProofCircuit'
  :: forall outer d f r
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => Foldable outer
  => Reflectable d Int
  => { sg :: AffinePoint (FVar f)
     , allChallenges :: outer (Vector d (FVar f))
     }
  -> SpongeM f (KimchiConstraint f) r (FVar f)
hashMessagesForNextWrapProofCircuit' { sg: AffinePoint sg, allChallenges } = labelM "hash-messages-for-next-wrap-proof" do
  for_ allChallenges \chals ->
    Pickles.Sponge.absorbMany chals
  absorb sg.x
  absorb sg.y
  squeeze

-- | Sponge checkpoints indexed by `n`, the number of real challenge
-- | vectors a slot supplies: entry `n` is the state after absorbing
-- | `PaddedLength - n` dummies. Starting the message hash from one of
-- | these keeps the dummy absorption out of the circuit.
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
    Tuple _ s0 = runPureSpongeM (initialSponge) getSpongeState
    Tuple _ s1 = go s0
    Tuple _ s2 = go s1
  in
    -- Reversed into index-by-`n` order: entry 0 has both dummies
    -- absorbed, entry 2 is the fresh sponge.
    s2 :< s1 :< s0 :< Vector.nil
