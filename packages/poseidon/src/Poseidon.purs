-- | Poseidon hash function for zkSNARK-friendly hashing.
-- |
-- | Poseidon is an algebraic hash function designed for efficiency inside
-- | arithmetic circuits. It operates over prime fields and uses a sponge
-- | construction with the following components:
-- |
-- | - **S-box**: x^7 (provides non-linearity)
-- | - **MDS matrix**: Maximum Distance Separable matrix for diffusion
-- | - **Round constants**: Field-specific constants for each round
-- |
-- | This implementation uses the Kimchi parameters (55 full rounds, state
-- | width 3) for compatibility with Mina Protocol.
-- |
-- | ```purescript
-- | import Poseidon (hash)
-- | import Snarky.Curves.Pallas as Pallas
-- |
-- | digest :: Pallas.BaseField
-- | digest = hash [field1, field2, field3]
-- | ```
module Poseidon
  ( module Poseidon.Class
  ) where

import Poseidon.Class (class PoseidonField, applyMds, fullRound, getMdsMatrix, getNumRounds, getRoundConstants, hash, sbox)