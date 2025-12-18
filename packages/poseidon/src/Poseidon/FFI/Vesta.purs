module Poseidon.FFI.Vesta where

import Prelude (Unit)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.Vector (Vector)


foreign import sbox :: Vesta.BaseField -> Vesta.BaseField
foreign import applyMds :: Vector 3 Vesta.BaseField -> Vector 3 Vesta.BaseField
foreign import fullRound :: Vector 3 Vesta.BaseField -> Int -> Vector 3 Vesta.BaseField
foreign import getRoundConstants :: Int -> Vector 3 Vesta.BaseField
foreign import getNumRounds :: Unit -> Int
foreign import getMdsMatrix :: Unit -> Vector 3 (Vector 3 Vesta.BaseField)
foreign import hash :: Array Vesta.BaseField -> Vesta.BaseField