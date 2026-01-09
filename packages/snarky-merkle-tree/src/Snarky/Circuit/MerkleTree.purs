module Snarky.Circuit.MerkleTree where

import Snarky.Circuit.DSL.Bits (packPure, unpackPure)
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Data.Vector (Vector)

newtype Address f = Address
  (forall r. (forall n . FieldSizeInBits f n => Vector n Boolean -> r) -> r)

mkAddress :: forall f n. FieldSizeInBits f n => f -> Address f
mkAddress f = Address (\k -> k (unpackPure f))

unAddress :: forall f. Address f -> f
unAddress (Address k) = k packPure