-- | Test-only FFI wrappers for Rust Poseidon/Sponge (Vesta)
-- | These are used to verify our PureScript implementations match Rust exactly
module Test.RandomOracle.FFI.Vesta where

import Data.Vector (Vector)
import Effect (Effect)
import Prelude (Unit)
import Snarky.Curves.Vesta as Vesta

-- | Permute function for testing sponge permutation
foreign import permute :: Vector 3 Vesta.BaseField -> Vector 3 Vesta.BaseField

-- | Opaque sponge handle wrapping Rust ArithmeticSponge
foreign import data VestaSponge :: Type

-- | Create a new sponge (thin wrapper around ArithmeticSponge::new)
foreign import spongeCreate :: Effect VestaSponge

-- | Absorb a single element into the sponge (mutates in place)
foreign import spongeAbsorb :: VestaSponge -> Vesta.BaseField -> Effect Unit

-- | Squeeze a single element from the sponge (mutates in place)
foreign import spongeSqueeze :: VestaSponge -> Effect Vesta.BaseField
