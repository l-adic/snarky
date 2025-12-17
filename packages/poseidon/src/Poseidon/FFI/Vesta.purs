module Poseidon.FFI.Vesta where

import Prelude (Unit)
import Snarky.Curves.Vesta as Vesta

-- ============================================================================
-- VESTA POSEIDON FFI
-- ============================================================================

foreign import sbox :: Vesta.BaseField -> Vesta.BaseField
foreign import applyMds :: Array Vesta.BaseField -> Array Vesta.BaseField
foreign import fullRound :: Array Vesta.BaseField -> Int -> Array Vesta.BaseField
foreign import getRoundConstants :: Int -> Array Vesta.BaseField
foreign import getNumRounds :: Unit -> Int
foreign import getMdsMatrix :: Unit -> Array (Array Vesta.BaseField)
foreign import hash :: Array Vesta.BaseField -> Vesta.BaseField