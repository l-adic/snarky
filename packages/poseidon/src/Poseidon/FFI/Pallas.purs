module Poseidon.FFI.Pallas where

import Prelude (Unit)
import Snarky.Curves.Pallas as Pallas

-- ============================================================================
-- PALLAS POSEIDON FFI
-- ============================================================================

foreign import sbox :: Pallas.BaseField -> Pallas.BaseField
foreign import applyMds :: Array Pallas.BaseField -> Array Pallas.BaseField
foreign import fullRound :: Array Pallas.BaseField -> Int -> Array Pallas.BaseField
foreign import getRoundConstants :: Int -> Array Pallas.BaseField
foreign import getNumRounds :: Unit -> Int
foreign import getMdsMatrix :: Unit -> Array (Array Pallas.BaseField)
foreign import hash :: Array Pallas.BaseField -> Pallas.BaseField