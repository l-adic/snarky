-- | Circuit (checked) version of the Random Oracle.
-- |
-- | This module provides random oracle operations that work within
-- | the circuit/constraint system. Unlike the pure version, inputs
-- | must have statically known sizes.
module Snarky.Circuit.RandomOracle
  ( poseidonPermutation
  , hash
  , hash2
  , update
  ) where

import Prelude

import Data.Traversable (traverse)
import Data.Foldable (foldM)
import Data.Fin (getFinite, unsafeFinite)
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Data.Vector as Vector
import Poseidon.Class (class PoseidonField, fullRound)
import Prim.Int (class Mul)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (add_, const_)
import Snarky.Circuit.DSL (Snarky, addConstraint, exists, readCVar)
import Snarky.Circuit.DSL.Monad (class CircuitM)
import Snarky.Circuit.Types (F(..), FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint(KimchiPoseidon))
import Snarky.Curves.Class (class PrimeField)

-- | Run a single Poseidon permutation and return the FULL final state.
-- |
-- | Unlike the standard poseidon circuit which returns position 2,
-- | this returns all 3 elements of the final state, which is needed
-- | for the sponge construction (which squeezes from position 0).
poseidonPermutation
  :: forall f t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Vector 3 (FVar f)
  -> Snarky (KimchiConstraint f) t m (Vector 3 (FVar f))
poseidonPermutation initState = do
  state <- exists do
    initialValues <- traverse readCVar initState
    let
      rounds = Vector.generate (\i -> \st -> fullRound st (getFinite i))
      roundOutputs = Vector.scanl (\st roundFn -> roundFn st) (coerce initialValues) rounds
      allStates = (coerce initialValues) Vector.:< roundOutputs
    pure (map (map F) allStates)
  addConstraint $ KimchiPoseidon { state }
  -- Return the full final state (round 55)
  pure $ Vector.index state (unsafeFinite 55)

-- | Initial state for the sponge: all zeros
initialState :: forall f. PrimeField f => Vector 3 (FVar f)
initialState = Vector.generate (const (const_ zero))

-- | Add a block of 2 elements to the sponge state (positions 0 and 1)
addBlock
  :: forall f
   . PrimeField f
  => Vector 3 (FVar f)
  -> Vector 2 (FVar f)
  -> Vector 3 (FVar f)
addBlock state block =
  let
    s0 = Vector.index state (unsafeFinite 0)
    s1 = Vector.index state (unsafeFinite 1)
    s2 = Vector.index state (unsafeFinite 2)
    b0 = Vector.index block (unsafeFinite 0)
    b1 = Vector.index block (unsafeFinite 1)
  in
    (s0 `add_` b0) Vector.:< (s1 `add_` b1) Vector.:< s2 Vector.:< Vector.nil

-- | Update the sponge state with a single block and permute.
-- |
-- | This is the core sponge operation: add block to rate positions, then permute.
updateBlock
  :: forall f t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Vector 3 (FVar f)
  -> Vector 2 (FVar f)
  -> Snarky (KimchiConstraint f) t m (Vector 3 (FVar f))
updateBlock state block = do
  let stateWithBlock = addBlock state block
  poseidonPermutation stateWithBlock

-- | Hash exactly 2 field elements.
-- |
-- | This is the most common case: hash(a, b).
hash2
  :: forall f t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => FVar f
  -> FVar f
  -> Snarky (KimchiConstraint f) t m (FVar f)
hash2 a b = do
  let
    block :: Vector 2 (FVar f)
    block = a Vector.:< b Vector.:< Vector.nil
  finalState <- updateBlock initialState block
  -- Squeeze from position 0 (standard sponge)
  pure $ Vector.index finalState (unsafeFinite 0)

-- | Update state with a vector of inputs (must be even length for simplicity).
-- |
-- | The input vector is chunked into rate-sized blocks (2 elements each),
-- | and each block is absorbed with a permutation.
update
  :: forall f t m n @nBlocks
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Reflectable nBlocks Int
  => Reflectable 2 Int
  => Mul 2 nBlocks n -- n = 2 * nBlocks (even length inputs)
  => Vector 3 (FVar f)
  -> Vector n (FVar f)
  -> Snarky (KimchiConstraint f) t m (Vector 3 (FVar f))
update initState inputs = do
  let
    blocks :: Vector nBlocks (Vector 2 (FVar f))
    blocks = Vector.chunks @2 inputs

    -- Convert to array for monadic folding
    blocksArray :: Array (Vector 2 (FVar f))
    blocksArray = Vector.toUnfoldable blocks
  -- Fold over blocks, updating state with each
  foldM updateBlock initState blocksArray

-- | Hash a vector of field elements (must be even length).
-- |
-- | Example usage:
-- | ```
-- | result <- hash @4 inputs  -- hash 4 elements
-- | ```
hash
  :: forall f t m n @nBlocks
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Reflectable nBlocks Int
  => Reflectable 2 Int
  => Mul 2 nBlocks n
  => Vector n (FVar f)
  -> Snarky (KimchiConstraint f) t m (FVar f)
hash inputs = do
  finalState <- update @nBlocks initialState inputs
  -- Squeeze from position 0
  pure $ Vector.index finalState (unsafeFinite 0)