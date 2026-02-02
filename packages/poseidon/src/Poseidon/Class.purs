-- | Type class and operations for Poseidon hash.
-- |
-- | Provides the building blocks for Poseidon hashing:
-- |
-- | - Low-level operations (`sbox`, `applyMds`, `fullRound`) for building
-- |   custom circuits
-- | - High-level `hash` function for direct use
-- | - Access to Kimchi-specific constants (`getRoundConstants`, `getMdsMatrix`)
module Poseidon.Class
  ( class PoseidonField
  , sbox
  , applyMds
  , fullRound
  , getRoundConstants
  , getNumRounds
  , getMdsMatrix
  , hash
  ) where

import Prelude

import Data.Vector (Vector)
import Poseidon.FFI.Pallas as PallasFFI
import Poseidon.FFI.Vesta as VestaFFI
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Type.Proxy (Proxy)

-- | Fields that support Poseidon hashing.
-- |
-- | Instances are provided for `Pallas.BaseField` and `Vesta.BaseField`,
-- | using Kimchi-compatible parameters.
class PrimeField f <= PoseidonField f where
  -- | The S-box substitution: `sbox x = x^7`.
  -- |
  -- | This is the non-linear component of Poseidon.
  sbox :: f -> f

  -- | Multiply the 3-element state by the MDS matrix.
  -- |
  -- | Provides diffusion in the permutation.
  applyMds :: Vector 3 f -> Vector 3 f

  -- | Execute one full Poseidon round.
  -- |
  -- | A full round applies: S-box → Add round constants → MDS matrix.
  fullRound :: Vector 3 f -> Int -> Vector 3 f

  -- | Get the round constants for round `i` (0 to 54 for Kimchi).
  getRoundConstants :: Proxy f -> Int -> Vector 3 f

  -- | Get the total number of rounds (55 for Kimchi).
  getNumRounds :: Proxy f -> Int

  -- | Get the 3×3 MDS matrix.
  getMdsMatrix :: Proxy f -> Vector 3 (Vector 3 f)

  -- | Hash a variable-length array of field elements.
  -- |
  -- | Uses sponge construction internally.
  hash :: Array f -> f

-- | Poseidon over the Pallas base field (= Vesta scalar field).
instance PoseidonField Pallas.BaseField where
  sbox = PallasFFI.sbox
  applyMds = PallasFFI.applyMds
  fullRound = PallasFFI.fullRound
  getRoundConstants _ = PallasFFI.getRoundConstants
  getNumRounds _ = PallasFFI.getNumRounds unit
  getMdsMatrix _ = PallasFFI.getMdsMatrix unit
  hash = PallasFFI.hash

-- | Poseidon over the Vesta base field (= Pallas scalar field).
instance PoseidonField Vesta.BaseField where
  sbox = VestaFFI.sbox
  applyMds = VestaFFI.applyMds
  fullRound = VestaFFI.fullRound
  getRoundConstants _ = VestaFFI.getRoundConstants
  getNumRounds _ = VestaFFI.getNumRounds unit
  getMdsMatrix _ = VestaFFI.getMdsMatrix unit
  hash = VestaFFI.hash