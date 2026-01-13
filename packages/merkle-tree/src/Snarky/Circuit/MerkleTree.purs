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
import Data.MerkleTree.Hashable (class MerkleHashable)
import Data.MerkleTree.Sized (class Hashable, class MergeHash, Address, AddressVar(..), Path(..), hash, merge)
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, assertEqual_, exists, if_, read)
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Circuit.Types (class CheckedType, class CircuitType)

class
  ( Monad m
  , MerkleHashable v (Digest (F f))
  , CircuitType f v var
  , CheckedType var c
  ) <=
  MerkleRequestM m f v c (d :: Int) var
  | v f -> var
  , c -> f where
  getElement :: Address d -> m { value :: v, path :: Path d (Digest (F f)) }
  getPath :: Address d -> m (Path d (Digest (F f)))
  setValue :: Address d -> v -> m Unit

get
  :: forall t m f c d v vvar
   . Reflectable d Int
  => MerkleRequestM m f v c d vvar
  => Hashable vvar (Digest (FVar f))
  => CircuitM f c t m
  => AddressVar d f
  -> Digest (FVar f)
  -> Snarky c t m vvar
get addr (Digest root) = do
  { value, path } <- exists do
    a <- read addr
    lift $ getElement @_ @_ @v @c @d a
  let
    h = hash $ Just value
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
  :: forall t m f c d @v vvar
   . Reflectable d Int
  => MerkleRequestM m f v c d vvar
  => Hashable vvar (Digest (FVar f))
  => CircuitM f c t m
  => AddressVar d f
  -> Digest (FVar f)
  -> (vvar -> Snarky c t m vvar)
  -> Snarky c t m
       { root :: Digest (FVar f)
       , old :: vvar
       , new :: vvar
       }
fetchAndUpdate addr (Digest root) f = do
  -- Get element and path as witnesses
  { value: prev, path } <- exists do
    a <- read addr
    lift $ getElement @m @_ @v @c @d a
  -- Hash old element and verify against root
  let prevHash = hash $ Just prev
  impliedRoot addr prevHash path >>= \(Digest d) ->
    assertEqual_ root d
  -- Apply modification function
  next <- f prev
  -- Update the tree with the new value
  _ <- exists do
    a <- read addr
    n <- read @v next
    lift $ setValue @_ @_ @v @c @d a n
  -- Hash new element and compute new root
  let nextHash = hash $ Just next
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
  :: forall t m f c d @v vvar
   . Reflectable d Int
  => MerkleRequestM m f v c d vvar
  => Hashable vvar (Digest (FVar f))
  => CircuitM f c t m
  => AddressVar d f
  -> Digest (FVar f)
  -> vvar
  -> vvar
  -> Snarky c t m (Digest (FVar f))
update addr (Digest root) prev next = do
  -- Witness only the path
  path <- exists do
    a <- read addr
    lift $ getPath @m @_ @v @c @d a
  -- Hash old element and verify against root
  let prevHash = hash $ Just prev
  impliedRoot addr prevHash path >>= \(Digest d) ->
    assertEqual_ root d
  -- Update the tree with the new value
  _ <- exists do
    a <- read addr
    n <- read @v next
    lift $ setValue @_ @_ @v @c @d a n
  -- Hash new element and compute new root
  let nextHash = hash $ Just next
  impliedRoot addr nextHash path

impliedRoot
  :: forall t m f c d
   . Reflectable d Int
  => MergeHash (Digest (FVar f))
  => CircuitM f c t m
  => AddressVar d f
  -> Digest (FVar f)
  -> Path d (Digest (FVar f))
  -> Snarky c t m (Digest (FVar f))
impliedRoot (AddressVar addr) hash (Path path) =
  foldM
    ( \(Digest acc) (Tuple b (Digest h)) -> do
        l <- if_ b h acc
        r <- if_ b acc h
        pure $ merge (Digest l) (Digest r)
    )
    hash
    (Vector.zip addr path)