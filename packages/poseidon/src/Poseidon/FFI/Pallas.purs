-- | FFI bindings for Poseidon over the Pallas base field.
-- |
-- | These functions call into Rust implementations with Kimchi-compatible
-- | parameters. Use `Poseidon.Class` for the polymorphic interface.
module Poseidon.FFI.Pallas where

import Data.Vector (Vector)
import Prelude (Unit)
import Snarky.Curves.Pallas as Pallas

-- | S-box: x^7
foreign import sbox :: Pallas.BaseField -> Pallas.BaseField

-- | Apply the 3×3 MDS matrix.
foreign import applyMds :: Vector 3 Pallas.BaseField -> Vector 3 Pallas.BaseField

-- | Execute full round `i`: S-box → round constants → MDS.
foreign import fullRound :: Vector 3 Pallas.BaseField -> Int -> Vector 3 Pallas.BaseField

-- | Get the 3 round constants for round `i`.
foreign import getRoundConstants :: Int -> Vector 3 Pallas.BaseField

-- | Total number of rounds (55).
foreign import getNumRounds :: Unit -> Int

-- | The 3×3 MDS matrix.
foreign import getMdsMatrix :: Unit -> Vector 3 (Vector 3 Pallas.BaseField)

-- | Poseidon sponge hash of an array.
foreign import hash :: Array Pallas.BaseField -> Pallas.BaseField