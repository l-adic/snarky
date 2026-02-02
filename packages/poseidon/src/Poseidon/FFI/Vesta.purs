-- | FFI bindings for Poseidon over the Vesta base field.
-- |
-- | These functions call into Rust implementations with Kimchi-compatible
-- | parameters. Use `Poseidon.Class` for the polymorphic interface.
module Poseidon.FFI.Vesta where

import Data.Vector (Vector)
import Prelude (Unit)
import Snarky.Curves.Vesta as Vesta

-- | S-box: x^7
foreign import sbox :: Vesta.BaseField -> Vesta.BaseField

-- | Apply the 3×3 MDS matrix.
foreign import applyMds :: Vector 3 Vesta.BaseField -> Vector 3 Vesta.BaseField

-- | Execute full round `i`: S-box → round constants → MDS.
foreign import fullRound :: Vector 3 Vesta.BaseField -> Int -> Vector 3 Vesta.BaseField

-- | Get the 3 round constants for round `i`.
foreign import getRoundConstants :: Int -> Vector 3 Vesta.BaseField

-- | Total number of rounds (55).
foreign import getNumRounds :: Unit -> Int

-- | The 3×3 MDS matrix.
foreign import getMdsMatrix :: Unit -> Vector 3 (Vector 3 Vesta.BaseField)

-- | Poseidon sponge hash of an array.
foreign import hash :: Array Vesta.BaseField -> Vesta.BaseField