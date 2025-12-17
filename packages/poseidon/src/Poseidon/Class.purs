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
import Type.Proxy (Proxy)

import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Poseidon.FFI.Pallas as PallasFFI
import Poseidon.FFI.Vesta as VestaFFI

-- ============================================================================
-- POSEIDON TYPE CLASS
-- ============================================================================

-- | Type class for fields that support Poseidon operations
class PoseidonField f where
  -- | S-box operation (x^7)
  sbox :: f -> f

  -- | Apply MDS matrix to 3-element state
  applyMds :: Array f -> Array f

  -- | Execute one full Poseidon round
  fullRound :: Array f -> Int -> Array f

  -- | Get round constants for a specific round (0-54 for Kimchi)
  getRoundConstants :: Proxy f -> Int -> Array f

  -- | Get total number of rounds (55 for Kimchi)
  getNumRounds :: Proxy f -> Int

  -- | Get the 3x3 MDS matrix
  getMdsMatrix :: Proxy f -> Array (Array f)

  -- | Hash variable-length input
  hash :: Array f -> f

-- ============================================================================
-- PALLAS INSTANCE
-- ============================================================================

instance PoseidonField Pallas.BaseField where
  sbox = PallasFFI.sbox
  applyMds = PallasFFI.applyMds
  fullRound = PallasFFI.fullRound
  getRoundConstants _ = PallasFFI.getRoundConstants
  getNumRounds _ = PallasFFI.getNumRounds unit
  getMdsMatrix _ = PallasFFI.getMdsMatrix unit
  hash = PallasFFI.hash

-- ============================================================================
-- VESTA INSTANCE
-- ============================================================================

instance PoseidonField Vesta.BaseField where
  sbox = VestaFFI.sbox
  applyMds = VestaFFI.applyMds
  fullRound = VestaFFI.fullRound
  getRoundConstants _ = VestaFFI.getRoundConstants
  getNumRounds _ = VestaFFI.getNumRounds unit
  getMdsMatrix _ = VestaFFI.getMdsMatrix unit
  hash = VestaFFI.hash