module Data.MerkleTree.Sized
  ( MerkleTree(..)
  , Address(..)
  , Path(..)
  , create
  , size
  , add_
  , addMany
  , get
  , getPath
  , impliedRoot
  , getFreePath
  , freeRoot
  , impliedFreeRoot
  , root
  , toUnfoldable
  , module ReExports
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (length)
import Data.List (List)
import Data.Maybe (Maybe(..))
import Data.MerkleTree (FreeHash)
import Data.MerkleTree as MT
import Data.MerkleTree.Hashable (class Hashable, class MergeHash, class MerkleHashable, FreeHash(..), defaultHash, hash, merge) as ReExports
import Data.MerkleTree.Hashable (class MergeHash, class MerkleHashable)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Unfoldable (class Unfoldable)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Exception.Unsafe (unsafeThrow)
import JS.BigInt (BigInt)
import JS.BigInt as BigInt
import Safe.Coerce (coerce)
import Type.Proxy (Proxy(..))

newtype MerkleTree (d :: Int) hash a = MerkleTree (MT.MerkleTree hash a)

-- Create a new merkle tree with a single element at address 0 in a sparse tree of depth d
create
  :: forall d hash a
   . Reflectable d Int
  => MerkleHashable a hash
  => a
  -> MerkleTree d hash a
create value =
  let
    targetDepth = reflectType $ Proxy @d
    result = MT.leftTree targetDepth value
  in
    MerkleTree $ MT.MerkleTree
      { tree: result.tree
      , depth: targetDepth -- Always the fixed depth
      , count: one
      }

size :: forall d hash a. MerkleTree d hash a -> BigInt
size (MerkleTree (MT.MerkleTree { count })) = count

add_
  :: forall d hash a
   . MerkleHashable a hash
  => MerkleTree d hash a
  -> a
  -> MerkleTree d hash a
add_ (MerkleTree mt@(MT.MerkleTree t)) value =
  if t.count >= BigInt.shl one (BigInt.fromInt t.depth) then unsafeThrow "Cannot add_, tree exceeded maximum size"
  else MerkleTree $ MT.add_ mt value

addMany
  :: forall d hash a
   . Reflectable d Int
  => MerkleHashable a hash
  => MerkleTree d hash a
  -> List a
  -> MerkleTree d hash a
addMany _tree@(MerkleTree mt@(MT.MerkleTree t)) xs =
  let
    fixedDepth = reflectType $ Proxy @d
    maxCap = BigInt.shl one (BigInt.fromInt fixedDepth)
    newCount = t.count + BigInt.fromInt (length xs)
  in
    if newCount > maxCap then
      unsafeThrow "Cannot addMany, would exceed maximum capacity"
    else
      -- Now that setDirty and addressBits are fixed, use efficient dynamic tree addMany
      MerkleTree $ MT.addMany mt xs

newtype Address (d :: Int) = Address BigInt

get
  :: forall d hash a
   . MerkleTree d hash a
  -> Address d
  -> Maybe a
get t a = MT.get (coerce t :: MT.MerkleTree hash a) (coerce a)

newtype Path d hash = Path (Vector d hash)

getPath
  :: forall d hash a
   . Reflectable d Int
  => MerkleHashable a hash
  => MerkleTree d hash a
  -> Address d
  -> Maybe (Path d hash)
getPath t (Address a) =
  let
    mpath = MT.getPath (coerce t :: MT.MerkleTree hash a) (MT.Address a)
  in
    mpath <#> \path ->
      case Vector.toVector (Array.fromFoldable path) of
        Nothing -> unsafeThrow $ "Expected Merkle path of length " <> show (reflectType $ Proxy @d)
        Just p -> Path p

impliedRoot
  :: forall d hash
   . MergeHash hash
  => Address d
  -> hash
  -> Path d hash
  -> hash
impliedRoot (Address addr0) entryHash (Path path0) =
  MT.impliedRoot (MT.Address addr0) entryHash (Vector.toUnfoldable path0)

-- Get free hash path
getFreePath
  :: forall d hash a
   . Reflectable d Int
  => MerkleTree d hash a
  -> Address d
  -> Maybe (Path d (FreeHash a))
getFreePath (MerkleTree t) (Address addr0) =
  MT.getFreePath t (MT.Address addr0) <#> \path ->
    case Vector.toVector (Array.fromFoldable path) of
      Nothing -> unsafeThrow $ "Expected Merkle path of length " <> show (reflectType $ Proxy @d)
      Just p -> Path p

-- Get free hash of root
freeRoot :: forall d hash a. MerkleTree d hash a -> FreeHash a
freeRoot (MerkleTree t) = MT.freeRoot t

-- Compute free root from value and path  
impliedFreeRoot
  :: forall d a
   . Address d
  -> a
  -> Path d (FreeHash a)
  -> FreeHash a
impliedFreeRoot (Address addr0) value (Path path0) =
  MT.impliedFreeRoot (MT.Address addr0) value (Vector.toUnfoldable path0)

-- Get root hash
root :: forall d hash a. MerkleTree d hash a -> hash
root (MerkleTree t) = MT.root t

-- Convert to list of elements
toUnfoldable :: forall d hash a f. Unfoldable f => MerkleTree d hash a -> f a
toUnfoldable (MerkleTree t) = MT.toUnfoldable t