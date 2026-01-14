-- | Random Oracle implementation based on Poseidon sponge.
-- |
-- | This module provides a hash-based random oracle construction that
-- | mirrors the Mina protocol's random oracle implementation.
module RandomOracle
  ( State
  , hash
  , hashWithInit
  , update
  , digest
  , initialState
  ) where

import Prelude

import Data.Array (foldl, index, length, (..))
import Data.Fin (unsafeFinite)
import Data.Maybe (fromMaybe)
import Data.Vector (Vector)
import Data.Vector as Vector
import Poseidon.Class (class PoseidonField)
import RandomOracle.Sponge (permute)

-- | The sponge state type
type State f = Vector 3 f

-- | The digest type (single field element)
type Digest :: Type -> Type
type Digest f = f

-- | The rate of the sponge (how many elements can be absorbed per permutation)
rate :: Int
rate = 2

-- | Initial state: all zeros
initialState :: forall f. Semiring f => State f
initialState = Vector.generate (const zero)

-- | Chunk input array into rate-sized blocks with zero padding
toBlocks :: forall f. Semiring f => Array f -> Array (Vector 2 f)
toBlocks fieldElems =
  let
    n = length fieldElems
    numBlocks = if n == 0 then 1 else (n + rate - 1) / rate
    fillBlock blockIdx pos =
      let
        globalPos = (rate * blockIdx) + pos
      in
        fromMaybe zero (index fieldElems globalPos)
    createBlock idx =
      fillBlock idx 0 Vector.:< fillBlock idx 1 Vector.:< Vector.nil
  in
    map createBlock (0 .. (numBlocks - 1))

-- | Add a block of field elements to the state (XOR / field addition)
addBlock :: forall f. Semiring f => State f -> Vector 2 f -> State f
addBlock st block =
  let
    b0 = Vector.index block (unsafeFinite 0)
    b1 = Vector.index block (unsafeFinite 1)
    s0 = Vector.index st (unsafeFinite 0)
    s1 = Vector.index st (unsafeFinite 1)
    s2 = Vector.index st (unsafeFinite 2)
  in
    (s0 + b0) Vector.:< (s1 + b1) Vector.:< s2 Vector.:< Vector.nil

-- | Sponge operation: absorb blocks with permutation
sponge :: forall f. PoseidonField f => (State f -> State f) -> Array (Vector 2 f) -> State f -> State f
sponge perm blocks st =
  foldl (\state block -> perm (addBlock state block)) st blocks

-- | Update the state with new input
update :: forall f. PoseidonField f => State f -> Array f -> State f
update st inputs = sponge permute (toBlocks inputs) st

-- | Extract the digest from the state (first element)
digest :: forall f. State f -> Digest f
digest st = Vector.index st (unsafeFinite 0)

-- | Hash an array of field elements with default initial state
hash :: forall f. PoseidonField f => Array f -> Digest f
hash inputs = digest (update initialState inputs)

-- | Hash an array of field elements with custom initial state
hashWithInit :: forall f. PoseidonField f => State f -> Array f -> Digest f
hashWithInit init inputs = digest (update init inputs)
