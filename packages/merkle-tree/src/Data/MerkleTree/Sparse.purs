-- | Sparse Merkle Tree - Off-chain implementation
-- |
-- | A sparse Merkle tree is a fixed-depth tree where most leaves are empty.
-- | Only explicitly set values are stored; all other positions are treated
-- | as having the "empty" hash. This allows setting values at arbitrary
-- | addresses within the tree's capacity without storing all 2^depth leaves.
-- |
-- | Key properties:
-- | - Fixed depth determined at creation time
-- | - Arbitrary addresses can be set (not just append-only)
-- | - Empty subtrees use pre-computed "default" hashes
-- | - Efficient storage: only non-empty leaves are stored
module Data.MerkleTree.Sparse
  ( SparseMerkleTree
  , empty
  , set
  , unsafeSet
  , get
  , root
  , getWitness
  , impliedRoot
  , depth
  , size
  , toUnfoldable
  , module Sized
  ) where

import Prelude

import Data.Array as Array
import Data.List (List(..), (:))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.MerkleTree (ithBit)
import Data.MerkleTree.Hashable (class MergeHash, class MerkleHashable, defaultHash, hash, merge)
import Data.MerkleTree.Sized (Address(..), Path(..)) as Sized
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple (Tuple(..))
import Data.Unfoldable (class Unfoldable)
import Data.Vector as Vector
import JS.BigInt (BigInt)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafeCrashWith)
import Type.Proxy (Proxy(..))

-- | Sparse Merkle tree with fixed depth
-- |
-- | Stores:
-- | - `values`: Map from address (BigInt) to value
-- | - `emptyHashes`: Pre-computed hashes for empty subtrees at each level (size d+1)
-- |   - emptyHashes[0] = hash(Nothing) -- empty leaf
-- |   - emptyHashes[i+1] = merge(emptyHashes[i], emptyHashes[i])
data SparseMerkleTree (d :: Int) hash a = SparseMerkleTree
  { values :: Map BigInt a
  , emptyHashes :: Array hash
  }

-- | Create an empty sparse merkle tree of the given depth
empty
  :: forall d hash a
   . Reflectable d Int
  => MerkleHashable a hash
  => SparseMerkleTree d hash a
empty =
  let
    treeDepth = reflectType (Proxy @d)
  in
    SparseMerkleTree
      { values: Map.empty
      , emptyHashes: computeEmptyHashes @a treeDepth
      }

-- | Compute empty hashes for all levels 0..depth
-- | emptyHashes[i] is the hash of an empty subtree of depth i
computeEmptyHashes
  :: forall @a hash
   . MerkleHashable a hash
  => Int
  -> Array hash
computeEmptyHashes treeDepth =
  let
    h0 = defaultHash @a

    go :: Int -> hash -> Array hash -> Array hash
    go i prevHash acc =
      if i > treeDepth then acc
      else go (i + 1) (merge prevHash prevHash) (Array.snoc acc (merge prevHash prevHash))
  in
    go 1 h0 [ h0 ]

-- | Get the depth of the tree
depth
  :: forall d hash a
   . Reflectable d Int
  => SparseMerkleTree d hash a
  -> Int
depth _ = reflectType (Proxy @d)

-- | Get the number of set values
size
  :: forall d hash a
   . SparseMerkleTree d hash a
  -> Int
size (SparseMerkleTree { values }) = Map.size values

-- | Set a value at the given address
-- |
-- | Unlike the dense tree, this can set at any address within the tree's capacity.
-- | Returns Nothing if the address is out of bounds (>= 2^depth)
set
  :: forall d hash a
   . Reflectable d Int
  => MerkleHashable a hash
  => Sized.Address d
  -> a
  -> SparseMerkleTree d hash a
  -> Maybe (SparseMerkleTree d hash a)
set (Sized.Address addr) value tree@(SparseMerkleTree state) =
  let
    treeDepth = depth tree
    maxAddr = BigInt.shl one (BigInt.fromInt treeDepth)
  in
    if addr < zero || addr >= maxAddr then Nothing
    else Just $ SparseMerkleTree state { values = Map.insert addr value state.values }

-- | Set a value at the given address, partial on out-of-bounds
unsafeSet
  :: forall d hash a
   . Partial
  => Reflectable d Int
  => MerkleHashable a hash
  => Sized.Address d
  -> a
  -> SparseMerkleTree d hash a
  -> SparseMerkleTree d hash a
unsafeSet addr value tree =
  case set addr value tree of
    Just t -> t

-- | Get a value at the given address
-- |
-- | Returns Nothing if the address is not set (not the same as out-of-bounds)
get
  :: forall d hash a
   . SparseMerkleTree d hash a
  -> Sized.Address d
  -> Maybe a
get (SparseMerkleTree { values }) (Sized.Address addr) = Map.lookup addr values

-- | Compute the root hash of the sparse tree
-- |
-- | This is computed by building up from all leaves, using empty hashes
-- | for positions that don't have values set.
root
  :: forall d hash a
   . Reflectable d Int
  => MerkleHashable a hash
  => SparseMerkleTree d hash a
  -> hash
root tree@(SparseMerkleTree state) =
  let
    treeDepth = depth tree
  in
    if treeDepth == 0 then
      -- Special case: depth 0 tree has a single leaf at address 0
      case Map.lookup zero state.values of
        Nothing -> defaultHash @a
        Just v -> hash (Just v)
    else
      computeRoot @a treeDepth state.values state.emptyHashes

-- | Check if a subtree has any values in the given address range
-- | addr is the leftmost address, subDepth is the height (so range is [addr, addr + 2^subDepth))
-- | Uses Map.lookupGE for O(log n) lookup instead of O(n) scan
hasValuesInRange :: forall a. Map BigInt a -> BigInt -> Int -> Boolean
hasValuesInRange values addr subDepth =
  let
    rangeSize = BigInt.shl one (BigInt.fromInt subDepth)
    endAddr = addr + rangeSize
  in
    -- Find smallest key >= addr, check if it's < endAddr
    case Map.lookupGE addr values of
      Just { key } -> key < endAddr
      Nothing -> false

-- | Compute root by building up the tree level by level
-- | Optimized to use pre-computed empty hashes for empty subtrees
computeRoot
  :: forall @a hash
   . MerkleHashable a hash
  => Int
  -> Map BigInt a
  -> Array hash
  -> hash
computeRoot treeDepth values emptyHashes =
  let
    -- Get the empty hash for a subtree of given depth
    emptyHash :: Int -> hash
    emptyHash d = case Array.index emptyHashes d of
      Just h -> h
      Nothing -> unsafeCrashWith $ "computeRoot: Invalid depth " <> show d <> ", array length " <> show (Array.length emptyHashes)

    -- Compute hash of subtree rooted at given address with given subtree depth
    -- addr is the leftmost address covered by this subtree
    -- subDepth is the height of this subtree (0 = leaf level)
    computeSubtree :: BigInt -> Int -> hash
    computeSubtree addr subDepth =
      -- First check if this subtree has any values at all
      if not (hasValuesInRange values addr subDepth) then
        -- Empty subtree - use pre-computed hash
        emptyHash subDepth
      else if subDepth == 0 then
        -- Leaf level with a value
        case Map.lookup addr values of
          Nothing -> emptyHash 0
          Just v -> hash @a (Just v)
      else
        -- Internal node with at least one value somewhere below
        let
          halfSize = BigInt.shl one (BigInt.fromInt (subDepth - 1))
          leftAddr = addr
          rightAddr = addr + halfSize
          leftHash = computeSubtree leftAddr (subDepth - 1)
          rightHash = computeSubtree rightAddr (subDepth - 1)
        in
          merge leftHash rightHash
  in
    computeSubtree zero treeDepth

-- | Get the witness (Merkle path) for an address
-- |
-- | The witness consists of the sibling hashes needed to verify
-- | that a value at the given address produces the root.
-- |
-- | For empty addresses, returns the path with appropriate empty hashes.
getWitness
  :: forall d hash a
   . Reflectable d Int
  => MerkleHashable a hash
  => Sized.Address d
  -> SparseMerkleTree d hash a
  -> Sized.Path d hash
getWitness (Sized.Address addr) tree@(SparseMerkleTree state) =
  let
    treeDepth = depth tree

    -- Get the empty hash for a subtree of given depth
    emptyHash :: Int -> hash
    emptyHash d = case Array.index state.emptyHashes d of
      Just h -> h
      Nothing -> unsafeCrashWith $ "getWitness: Invalid depth " <> show d <> ", array length " <> show (Array.length state.emptyHashes)

    -- Compute hash of subtree rooted at given address with given subtree depth
    -- Optimized to use pre-computed empty hashes for empty subtrees
    computeSubtree :: BigInt -> Int -> hash
    computeSubtree subAddr subDepth =
      -- First check if this subtree has any values at all
      if not (hasValuesInRange state.values subAddr subDepth) then
        -- Empty subtree - use pre-computed hash
        emptyHash subDepth
      else if subDepth == 0 then
        case Map.lookup subAddr state.values of
          Nothing -> emptyHash 0
          Just v -> hash @a (Just v)
      else
        let
          halfSize = BigInt.shl one (BigInt.fromInt (subDepth - 1))
          leftAddr = subAddr
          rightAddr = subAddr + halfSize
          leftHash = computeSubtree leftAddr (subDepth - 1)
          rightHash = computeSubtree rightAddr (subDepth - 1)
        in
          merge leftHash rightHash

    -- Build path from leaf to root
    -- At each level, we need the sibling's hash
    -- We append (snoc) to build in leaf-to-root order
    buildPath :: Int -> BigInt -> Array hash -> Array hash
    buildPath level currentAddr acc =
      if level == treeDepth then acc
      else
        let
          -- At this level, determine if we're on the left or right
          goRight = ithBit addr level
          -- Size of subtree at this level
          subtreeSize = BigInt.shl one (BigInt.fromInt level)
          -- Find the sibling address
          siblingAddr =
            if goRight then currentAddr - subtreeSize
            else currentAddr + subtreeSize
          -- Compute sibling hash
          siblingHash = computeSubtree siblingAddr level
          -- Next level's base address
          nextAddr = if goRight then siblingAddr else currentAddr
        in
          buildPath (level + 1) nextAddr (Array.snoc acc siblingHash)

    pathArray = buildPath 0 addr []
  in
    case Vector.toVector @d pathArray of
      Nothing -> unsafeCrashWith $ "Invalid path length: expected " <> show treeDepth <> " but got " <> show (Array.length pathArray)
      Just v -> Sized.Path v

-- | Compute the implied root from a value hash and its witness
-- |
-- | Given an address, the hash of the value at that address, and the witness path,
-- | compute what the root hash would be.
impliedRoot
  :: forall d hash
   . MergeHash hash
  => Sized.Address d
  -> hash
  -> Sized.Path d hash
  -> hash
impliedRoot (Sized.Address addr0) entryHash (Sized.Path path0) =
  let
    go :: hash -> Int -> List hash -> hash
    go acc _ Nil = acc
    go acc i (h : hs) =
      -- If bit i is set, we're on the right, so sibling (h) is on left
      if ithBit addr0 i then
        go (merge h acc) (i + 1) hs
      else
        go (merge acc h) (i + 1) hs
  in
    go entryHash 0 (Vector.toUnfoldable path0)

-- | Convert the sparse tree to a foldable of (address, value) pairs
toUnfoldable
  :: forall d hash a f
   . Unfoldable f
  => SparseMerkleTree d hash a
  -> f { address :: Sized.Address d, value :: a }
toUnfoldable (SparseMerkleTree { values }) =
  Array.toUnfoldable $ map (\(Tuple k v) -> { address: Sized.Address k, value: v }) (Map.toUnfoldable values :: Array _)
