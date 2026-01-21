-- | Test-only FFI wrappers for Rust Poseidon/Sponge (Pallas)
-- | These are used to verify our PureScript implementations match Rust exactly
module Test.RandomOracle.FFI.Pallas where

import Data.Vector (Vector)
import Effect (Effect)
import Prelude (Unit)
import Snarky.Curves.Pallas as Pallas

-- | Permute function for testing sponge permutation
foreign import permute :: Vector 3 Pallas.BaseField -> Vector 3 Pallas.BaseField

-- | Opaque sponge handle wrapping Rust ArithmeticSponge
foreign import data PallasSponge :: Type

-- | Create a new sponge (thin wrapper around ArithmeticSponge::new)
foreign import spongeCreate :: Effect PallasSponge

-- | Absorb a single element into the sponge (mutates in place)
foreign import spongeAbsorb :: PallasSponge -> Pallas.BaseField -> Effect Unit

-- | Squeeze a single element from the sponge (mutates in place)
foreign import spongeSqueeze :: PallasSponge -> Effect Pallas.BaseField
