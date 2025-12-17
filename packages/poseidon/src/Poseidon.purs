module Poseidon
  ( module Poseidon.Class
  , pallasPoseidonSbox
  , pallasPoseidonApplyMds
  , pallasPoseidonFullRound
  , pallasPoseidonGetRoundConstants
  , pallasPoseidonGetNumRounds
  , pallasPoseidonGetMdsMatrix
  , pallasPoseidonHash
  , vestaPoseidonSbox
  , vestaPoseidonApplyMds
  , vestaPoseidonFullRound
  , vestaPoseidonGetRoundConstants
  , vestaPoseidonGetNumRounds
  , vestaPoseidonGetMdsMatrix
  , vestaPoseidonHash
  ) where

import Prelude
import Type.Proxy (Proxy(..))
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Poseidon.Class (class PoseidonField, applyMds, fullRound, getMdsMatrix, getNumRounds, getRoundConstants, hash, sbox)
import Poseidon.FFI.Pallas as PallasFFI
import Poseidon.FFI.Vesta as VestaFFI

-- ============================================================================
-- CONVENIENCE FUNCTIONS
-- ============================================================================

pallasPoseidonSbox :: Pallas.BaseField -> Pallas.BaseField
pallasPoseidonSbox = PallasFFI.sbox

pallasPoseidonApplyMds :: Array Pallas.BaseField -> Array Pallas.BaseField
pallasPoseidonApplyMds = PallasFFI.applyMds

pallasPoseidonFullRound :: Array Pallas.BaseField -> Int -> Array Pallas.BaseField
pallasPoseidonFullRound = PallasFFI.fullRound

pallasPoseidonGetRoundConstants :: Int -> Array Pallas.BaseField
pallasPoseidonGetRoundConstants = getRoundConstants (Proxy :: Proxy Pallas.BaseField)

pallasPoseidonGetNumRounds :: Int
pallasPoseidonGetNumRounds = getNumRounds (Proxy :: Proxy Pallas.BaseField)

pallasPoseidonGetMdsMatrix :: Array (Array Pallas.BaseField)
pallasPoseidonGetMdsMatrix = getMdsMatrix (Proxy :: Proxy Pallas.BaseField)

pallasPoseidonHash :: Array Pallas.BaseField -> Pallas.BaseField
pallasPoseidonHash = PallasFFI.hash

vestaPoseidonSbox :: Vesta.BaseField -> Vesta.BaseField
vestaPoseidonSbox = VestaFFI.sbox

vestaPoseidonApplyMds :: Array Vesta.BaseField -> Array Vesta.BaseField
vestaPoseidonApplyMds = VestaFFI.applyMds

vestaPoseidonFullRound :: Array Vesta.BaseField -> Int -> Array Vesta.BaseField
vestaPoseidonFullRound = VestaFFI.fullRound

vestaPoseidonGetRoundConstants :: Int -> Array Vesta.BaseField
vestaPoseidonGetRoundConstants = getRoundConstants (Proxy :: Proxy Vesta.BaseField)

vestaPoseidonGetNumRounds :: Int
vestaPoseidonGetNumRounds = getNumRounds (Proxy :: Proxy Vesta.BaseField)

vestaPoseidonGetMdsMatrix :: Array (Array Vesta.BaseField)
vestaPoseidonGetMdsMatrix = getMdsMatrix (Proxy :: Proxy Vesta.BaseField)

vestaPoseidonHash :: Array Vesta.BaseField -> Vesta.BaseField
vestaPoseidonHash = VestaFFI.hash

