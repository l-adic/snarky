module Snarky.Circuit.MerkleTree
  ( class MerkleRequestM
  , getElement
  , getPath
  , setValue
  , get
  , impliedRoot
  , fetchAndUpdate
  , update
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Foldable (foldM)
import Data.Maybe (Maybe(..))
import Data.MerkleTree.Hashable (class MerkleHashable, hash, mergeCircuit)
import Data.MerkleTree.Sized (Address, AddressVar(..), Path(..))
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import Poseidon.Class (class PoseidonField)
import Snarky.Circuit.DSL (class CheckedType, class CircuitM, class CircuitType, F, FVar, Snarky, assertEqual_, exists, if_, read)
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)

class
  ( Monad m
  , MerkleHashable v (Digest (F f))
  , CircuitType f v var
  ) <=
  MerkleRequestM m f v (d :: Int) var
  | v f -> var
  , var -> f
  , m -> v where
  getElement :: Address d -> m { value :: v, path :: Path d (Digest (F f)) }
  getPath :: Address d -> m (Path d (Digest (F f)))
  setValue :: Address d -> v -> m Unit

get
  :: forall t m f d v var
   . Reflectable d Int
  => PoseidonField f
  => MerkleRequestM m f v d var
  => CircuitM f (KimchiConstraint f) t m
  => CheckedType f (KimchiConstraint f) t m var
  => MerkleHashable var (Snarky (KimchiConstraint f) t m (Digest (FVar f)))
  => AddressVar d f
  -> Digest (FVar f)
  -> Snarky (KimchiConstraint f) t m var
get addr (Digest root) = do
  { value, path } <- exists do
    a <- read addr
    lift $ getElement @_ @_ @v @d a
  h <- hash $ Just value
  impliedRoot addr h path >>= \(Digest d) ->
    assertEqual_ root d
  pure value

-- | Fetch an element, apply a modification, and update the tree.
-- |
-- | This function:
-- | 1. Witnesses the current element and path
-- | 2. Verifies the old element hashes to the given root
-- | 3. Applies the modification function to get the new element
-- | 4. Updates the underlying tree state via setValue
-- | 5. Computes and returns the new root along with old and new elements
fetchAndUpdate
  :: forall t m f d v var
   . Reflectable d Int
  => PoseidonField f
  => MerkleRequestM m f v d var
  => MerkleHashable var (Snarky (KimchiConstraint f) t m (Digest (FVar f)))
  => CircuitM f (KimchiConstraint f) t m
  => CheckedType f (KimchiConstraint f) t m var
  => AddressVar d f
  -> Digest (FVar f)
  -> (var -> Snarky (KimchiConstraint f) t m var)
  -> Snarky (KimchiConstraint f) t m
       { root :: Digest (FVar f)
       , old :: var
       , new :: var
       }
fetchAndUpdate addr (Digest root) f = do
  -- Get element and path as witnesses
  { value: prev, path } <- exists do
    a <- read addr
    lift $ getElement @m @_ @v @d a
  -- Hash old element and verify against root
  prevHash <- hash $ Just prev
  impliedRoot addr prevHash path >>= \(Digest d) ->
    assertEqual_ root d
  -- Apply modification function
  next <- f prev
  -- Update the tree with the new value
  _ <- exists do
    a <- read addr
    n <- read @v next
    lift $ setValue @_ @f @v @d a n
  -- Hash new element and compute new root
  nextHash <- hash $ Just next
  newRoot <- impliedRoot addr nextHash path
  pure { root: newRoot, old: prev, new: next }

-- | Update an element when you already have both old and new values.
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
  => AddressVar d f
  -> Digest (FVar f)
  -> var
  -> var
  -> Snarky (KimchiConstraint f) t m (Digest (FVar f))
update addr (Digest root) prev next = do
  -- Witness only the path
  path <- exists do
    a <- read addr
    lift $ getPath @m @_ @v @d a
  -- Hash old element and verify against root
  prevHash <- hash $ Just prev
  impliedRoot addr prevHash path >>= \(Digest d) ->
    assertEqual_ root d
  -- Update the tree with the new value
  _ <- exists do
    a <- read addr
    n <- read @v next
    lift $ setValue @_ @f @v @d a n
  -- Hash new element and compute new root
  nextHash <- hash $ Just next
  impliedRoot addr nextHash path

impliedRoot
  :: forall t m f d
   . Reflectable d Int
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => AddressVar d f
  -> Digest (FVar f)
  -> Path d (Digest (FVar f))
  -> Snarky (KimchiConstraint f) t m (Digest (FVar f))
impliedRoot (AddressVar addr) initialHash (Path path) =
  foldM
    ( \(Digest acc) (Tuple b (Digest h)) -> do
        l <- if_ b h acc
        r <- if_ b acc h
        mergeCircuit (Digest l) (Digest r)
    )
    initialHash
    (Vector.zip addr path)