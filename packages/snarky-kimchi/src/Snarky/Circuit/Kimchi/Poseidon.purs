module Snarky.Circuit.Kimchi.Poseidon
  ( poseidonHash
  ) where

import Prelude

import Data.Newtype (unwrap)
import Data.Traversable (traverse)
import Poseidon as Poseidon
import Snarky.Circuit.DSL (Snarky, exists, readCVar)
import Snarky.Circuit.DSL.Monad (class CircuitM)
import Snarky.Circuit.Types (F(..), FVar)
import Snarky.Curves.Pasta (PallasBaseField)
import Snarky.Data.Vector (Vector)
import Snarky.Data.Vector as Vector

-- | Compute Poseidon hash using the reference implementation
-- | This creates a simplified circuit that witnesses the result
poseidonHash
  :: forall c t m
   . CircuitM PallasBaseField c t m
  => Vector 3 (FVar PallasBaseField) -- Fixed-size 3-element input for now
  -> Snarky t m (FVar PallasBaseField) -- Hash result
poseidonHash inputState = do
  -- Witness the hash result using reference FFI
  result <- exists do
    -- Read all input state values using traverseWithIndex
    stateValues <- traverse readCVar inputState
    -- Call the reference Poseidon hash implementation
    let
      inputs = map unwrap (Vector.unVector stateValues)
      hashResult = Poseidon.pallasPoseidonHash inputs
    pure (F hashResult)

  pure result