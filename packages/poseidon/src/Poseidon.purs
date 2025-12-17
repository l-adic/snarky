module Poseidon
  ( -- Pallas Poseidon
    pallasPoseidonSbox
  , pallasPoseidonApplyMds
  , pallasPoseidonFullRound
  , pallasPoseidonGetRoundConstants
  , pallasPoseidonGetNumRounds
  , pallasPoseidonGetMdsMatrix
  , pallasPoseidonHash
  -- Vesta Poseidon
  , vestaPoseidonSbox
  , vestaPoseidonApplyMds
  , vestaPoseidonFullRound
  , vestaPoseidonGetRoundConstants
  , vestaPoseidonGetNumRounds
  , vestaPoseidonGetMdsMatrix
  , vestaPoseidonHash
  ) where

import Prelude

import Snarky.Curves.Pasta (PallasBaseField, VestaBaseField)

-- ============================================================================
-- PALLAS POSEIDON FFI
-- ============================================================================

foreign import _pallasPoseidonSbox :: PallasBaseField -> PallasBaseField
foreign import _pallasPoseidonApplyMds :: Array PallasBaseField -> Array PallasBaseField
foreign import _pallasPoseidonFullRound :: Array PallasBaseField -> Int -> Array PallasBaseField
foreign import _pallasPoseidonGetRoundConstants :: Int -> Array PallasBaseField
foreign import _pallasPoseidonGetNumRounds :: Unit -> Int
foreign import _pallasPoseidonGetMdsMatrix :: Unit -> Array (Array PallasBaseField)
foreign import _pallasPoseidonHash :: Array PallasBaseField -> PallasBaseField

-- ============================================================================
-- VESTA POSEIDON FFI
-- ============================================================================

foreign import _vestaPoseidonSbox :: VestaBaseField -> VestaBaseField
foreign import _vestaPoseidonApplyMds :: Array VestaBaseField -> Array VestaBaseField
foreign import _vestaPoseidonFullRound :: Array VestaBaseField -> Int -> Array VestaBaseField
foreign import _vestaPoseidonGetRoundConstants :: Int -> Array VestaBaseField
foreign import _vestaPoseidonGetNumRounds :: Unit -> Int
foreign import _vestaPoseidonGetMdsMatrix :: Unit -> Array (Array VestaBaseField)
foreign import _vestaPoseidonHash :: Array VestaBaseField -> VestaBaseField

-- ============================================================================
-- PALLAS POSEIDON WRAPPERS
-- ============================================================================

-- | S-box operation for Pallas base field (x^7)
pallasPoseidonSbox :: PallasBaseField -> PallasBaseField
pallasPoseidonSbox = _pallasPoseidonSbox

-- | Apply MDS matrix to 3-element state
pallasPoseidonApplyMds :: Array PallasBaseField -> Array PallasBaseField
pallasPoseidonApplyMds = _pallasPoseidonApplyMds

-- | Execute one full Poseidon round
pallasPoseidonFullRound :: Array PallasBaseField -> Int -> Array PallasBaseField
pallasPoseidonFullRound = _pallasPoseidonFullRound

-- | Get round constants for a specific round (0-54 for Kimchi)
pallasPoseidonGetRoundConstants :: Int -> Array PallasBaseField
pallasPoseidonGetRoundConstants = _pallasPoseidonGetRoundConstants

-- | Get total number of rounds (55 for Kimchi)
pallasPoseidonGetNumRounds :: Int
pallasPoseidonGetNumRounds = _pallasPoseidonGetNumRounds unit

-- | Get the 3x3 MDS matrix
pallasPoseidonGetMdsMatrix :: Array (Array PallasBaseField)
pallasPoseidonGetMdsMatrix = _pallasPoseidonGetMdsMatrix unit

-- | Hash variable-length input
pallasPoseidonHash :: Array PallasBaseField -> PallasBaseField
pallasPoseidonHash = _pallasPoseidonHash

-- ============================================================================
-- VESTA POSEIDON WRAPPERS
-- ============================================================================

-- | S-box operation for Vesta base field (x^7)
vestaPoseidonSbox :: VestaBaseField -> VestaBaseField
vestaPoseidonSbox = _vestaPoseidonSbox

-- | Apply MDS matrix to 3-element state
vestaPoseidonApplyMds :: Array VestaBaseField -> Array VestaBaseField
vestaPoseidonApplyMds = _vestaPoseidonApplyMds

-- | Execute one full Poseidon round
vestaPoseidonFullRound :: Array VestaBaseField -> Int -> Array VestaBaseField
vestaPoseidonFullRound = _vestaPoseidonFullRound

-- | Get round constants for a specific round (0-54 for Kimchi)
vestaPoseidonGetRoundConstants :: Int -> Array VestaBaseField
vestaPoseidonGetRoundConstants = _vestaPoseidonGetRoundConstants

-- | Get total number of rounds (55 for Kimchi)
vestaPoseidonGetNumRounds :: Int
vestaPoseidonGetNumRounds = _vestaPoseidonGetNumRounds unit

-- | Get the 3x3 MDS matrix
vestaPoseidonGetMdsMatrix :: Array (Array VestaBaseField)
vestaPoseidonGetMdsMatrix = _vestaPoseidonGetMdsMatrix unit

-- | Hash variable-length input
vestaPoseidonHash :: Array VestaBaseField -> VestaBaseField
vestaPoseidonHash = _vestaPoseidonHash

