-- | Sparse Merkle Tree - Circuit implementation
-- |
-- | This module provides circuit-level operations for sparse Merkle trees,
-- | allowing zero-knowledge proofs of tree membership and updates.
-- |
-- | The key function is `checkAndUpdate`, which:
-- | 1. Verifies that a given witness is valid for the old root
-- | 2. Computes the new root after updating the value at an address
module Snarky.Circuit.MerkleTree.Sparse
  ( impliedRoot
  , get
  , checkAndUpdate
  , update
  , module Sized
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Foldable (foldM)
import Data.Maybe (Maybe(..))
import Data.MerkleTree.Hashable (class MerkleHashable, hash, mergeCircuit)
import Data.MerkleTree.Sized (AddressVar(..), Path(..)) as Sized
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import Poseidon.Class (class PoseidonField)
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky, assertEqual_, exists, if_, read)
import Snarky.Circuit.MerkleTree (class MerkleRequestM, getElement, getPath, setValue)
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)

-- | Compute the implied root from an address, value hash, and path
-- |
-- | This is the core verification primitive: given a leaf's position (address),
-- | its hash, and the sibling hashes along the path to root, compute
-- | what the root hash would be.
impliedRoot
  :: forall t m f d
   . Reflectable d Int
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Sized.AddressVar d f
  -> Digest (FVar f)
  -> Sized.Path d (Digest (FVar f))
  -> Snarky (KimchiConstraint f) t m (Digest (FVar f))
impliedRoot (Sized.AddressVar addr) initialHash (Sized.Path path) =
  foldM
    ( \(Digest acc) (Tuple b (Digest h)) -> do
        -- If bit is 1, we're on the right, so sibling (h) is on left
        l <- if_ b h acc
        r <- if_ b acc h
        mergeCircuit (Digest l) (Digest r)
    )
    initialHash
    (Vector.zip addr path)

-- | Get an element from the sparse tree, verifying its membership
-- |
-- | This witnesses the element and its path, then verifies the path
-- | computes to the expected root.
get
  :: forall t m f d v var
   . Reflectable d Int
  => PoseidonField f
  => MerkleRequestM m f v d var
  => CircuitM f (KimchiConstraint f) t m
  => MerkleHashable var (Snarky (KimchiConstraint f) t m (Digest (FVar f)))
  => Sized.AddressVar d f
  -> Digest (FVar f)
  -> Snarky (KimchiConstraint f) t m var
get addr (Digest root_) = do
  { value, path } <- exists do
    a <- read addr
    lift $ getElement @_ @f @v @d a
  h <- hash $ Just value
  impliedRoot addr h path >>= \(Digest d) ->
    assertEqual_ root_ d
  pure value

-- | Check that a witness is valid for the old root, then compute the new root
-- |
-- | This is the core "set" operation for sparse trees in a circuit.
-- |
-- | Arguments:
-- | - addr: The address being updated
-- | - oldValueHash: Hash of the value currently at this address
-- | - newValueHash: Hash of the new value to set
-- | - path: Witness (sibling hashes) for the address
-- | - oldRoot: The expected current root
-- |
-- | Returns: The new root after the update
-- |
-- | Fails (constraint unsatisfiable) if the witness doesn't produce oldRoot
checkAndUpdate
  :: forall t m f d
   . Reflectable d Int
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Sized.AddressVar d f
  -> Digest (FVar f)
  -> Digest (FVar f)
  -> Sized.Path d (Digest (FVar f))
  -> Digest (FVar f)
  -> Snarky (KimchiConstraint f) t m (Digest (FVar f))
checkAndUpdate addr oldValueHash newValueHash path (Digest oldRoot_) = do
  -- Verify the old value produces the old root
  impliedRoot addr oldValueHash path >>= \(Digest d) ->
    assertEqual_ oldRoot_ d
  -- Compute new root with the same path but new value hash
  impliedRoot addr newValueHash path

-- | Update an element when you already have both old and new values
-- |
-- | This function:
-- | 1. Witnesses only the path (not the element)
-- | 2. Verifies the old element hashes to the given root
-- | 3. Updates the underlying tree state via setValue
-- | 4. Computes and returns the new root
update
  :: forall t m f d v var
   . Reflectable d Int
  => PoseidonField f
  => MerkleRequestM m f v d var
  => MerkleHashable var (Snarky (KimchiConstraint f) t m (Digest (FVar f)))
  => CircuitM f (KimchiConstraint f) t m
  => Sized.AddressVar d f
  -> Digest (FVar f)
  -> var
  -> var
  -> Snarky (KimchiConstraint f) t m (Digest (FVar f))
update addr (Digest root_) prev next = do
  -- Witness only the path
  path <- exists do
    a <- read addr
    lift $ getPath @m @_ @v @d a
  -- Hash old element and verify against root
  prevHash <- hash $ Just prev
  impliedRoot addr prevHash path >>= \(Digest d) ->
    assertEqual_ root_ d
  -- Update the tree with the new value
  _ <- exists do
    a <- read addr
    n <- read @v next
    lift $ setValue @_ @f @v @d a n
  -- Hash new element and compute new root
  nextHash <- hash $ Just next
  impliedRoot addr nextHash path
