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
  , hashMessagesForNextWrapProofCircuit
  ) where

import Prelude

import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Sponge (SpongeM, absorb, squeeze)
import Pickles.Sponge as Pickles.Sponge
import Poseidon (class PoseidonField, hash)
import Snarky.Circuit.DSL (class CircuitM, FVar, const_)
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

-- | Circuit version: hash messages for next Wrap proof.
-- |
-- | Uses the Poseidon sponge in-circuit to absorb all field elements
-- | and squeeze the digest.
hashMessagesForNextWrapProofCircuit
  :: forall d f t m
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Reflectable d Int
  => { sg :: AffinePoint (FVar f)
     , expandedChallenges :: Vector d (FVar f)
     , dummyChallenges :: Vector d f -- compile-time constants
     }
  -> SpongeM f (KimchiConstraint f) t m (FVar f)
hashMessagesForNextWrapProofCircuit { sg, expandedChallenges, dummyChallenges } = do
  -- Absorb dummy challenges (constants, lifted to circuit variables)
  Pickles.Sponge.absorbMany (map const_ dummyChallenges)
  -- Absorb real expanded challenges
  Pickles.Sponge.absorbMany expandedChallenges
  -- Absorb sg point
  absorb sg.x
  absorb sg.y
  -- Squeeze digest
  squeeze
