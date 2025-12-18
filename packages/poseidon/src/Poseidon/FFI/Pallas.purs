module Poseidon.FFI.Pallas where

import Prelude (Unit)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.Vector (Vector)

foreign import sbox :: Pallas.BaseField -> Pallas.BaseField
foreign import applyMds :: Vector 3 Pallas.BaseField -> Vector 3 Pallas.BaseField
foreign import fullRound :: Vector 3 Pallas.BaseField -> Int -> Vector 3 Pallas.BaseField
foreign import getRoundConstants :: Int -> Vector 3 Pallas.BaseField
foreign import getNumRounds :: Unit -> Int
foreign import getMdsMatrix :: Unit -> Vector 3 (Vector 3 Pallas.BaseField)
foreign import hash :: Array Pallas.BaseField -> Pallas.BaseField