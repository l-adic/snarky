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
  , Address(..)
  , Path(..)
  , empty
  , set
  , set_
  , get
  , root
  , getWitness
  , impliedRoot
  , depth
  , size
  , toUnfoldable
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (class Foldable)
import Data.List (List(..), (:))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.MerkleTree.Hashable (class MergeHash, class MerkleHashable, defaultHash, hash, merge)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Traversable (class Traversable)
import Data.Tuple (Tuple(..))
import Data.Unfoldable (class Unfoldable)
import Data.Vector (Vector)
import Data.Vector as Vector
import JS.BigInt (BigInt)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafeCrashWith)
import Type.Proxy (Proxy(..))

-- | Address in a sparse tree, constrained by depth
newtype Address (d :: Int) = Address BigInt

derive newtype instance Eq (Address d)
derive newtype instance Ord (Address d)
derive newtype instance Show (Address d)

-- | Path of sibling hashes from leaf to root
newtype Path d hash = Path (Vector d hash)

derive instance Functor (Path d)

derive instance Foldable (Path d)

derive instance Traversable (Path d)

-- | Sparse Merkle tree with fixed depth
-- |
-- | Stores:
-- | - `values`: Map from address (BigInt) to value
-- | - `emptyHashes`: Pre-computed hashes for empty subtrees at each level
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
    -- Compute empty hashes for each level
    -- Level 0: hash of empty leaf
    -- Level i+1: merge of two empty subtrees of level i
    emptyHashesArr = computeEmptyHashes @a treeDepth
  in
    SparseMerkleTree
      { values: Map.empty
      , emptyHashes: emptyHashesArr
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
    -- Empty leaf hash
    h0 = defaultHash @a

    -- Build array iteratively
    go :: Int -> hash -> Array hash -> Array hash
    go i prevHash acc =
      if i > treeDepth then acc
      else
        let
          nextHash = merge prevHash prevHash
        in
          go (i + 1) nextHash (Array.snoc acc nextHash)
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
  => Address d
  -> a
  -> SparseMerkleTree d hash a
  -> Maybe (SparseMerkleTree d hash a)
set (Address addr) value tree@(SparseMerkleTree state) =
  let
    treeDepth = depth tree
    maxAddr = BigInt.shl one (BigInt.fromInt treeDepth)
  in
    if addr < zero || addr >= maxAddr then Nothing
    else Just $ SparseMerkleTree state { values = Map.insert addr value state.values }

-- | Set a value at the given address, throwing on out-of-bounds
set_
  :: forall d hash a
   . Reflectable d Int
  => MerkleHashable a hash
  => Address d
  -> a
  -> SparseMerkleTree d hash a
  -> SparseMerkleTree d hash a
set_ addr value tree =
  case set addr value tree of
    Nothing -> unsafeCrashWith "Address out of bounds"
    Just t -> t

-- | Get a value at the given address
-- |
-- | Returns Nothing if the address is not set (not the same as out-of-bounds)
get
  :: forall d hash a
   . SparseMerkleTree d hash a
  -> Address d
  -> Maybe a
get (SparseMerkleTree { values }) (Address addr) = Map.lookup addr values

-- | Check if i-th bit is set (0-indexed from least significant)
ithBit :: BigInt -> Int -> Boolean
ithBit n i = BigInt.and (BigInt.shr n (BigInt.fromInt i)) one == one

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

-- | Compute root by building up the tree level by level
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
      if subDepth == 0 then
        -- Leaf level
        case Map.lookup addr values of
          Nothing -> emptyHash 0
          Just v -> hash @a (Just v)
      else
        -- Internal node - check if subtree has any values
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
  => Address d
  -> SparseMerkleTree d hash a
  -> Path d hash
getWitness (Address addr) tree@(SparseMerkleTree state) =
  let
    treeDepth = depth tree

    -- Get the empty hash for a subtree of given depth
    emptyHash :: Int -> hash
    emptyHash d = case Array.index state.emptyHashes d of
      Just h -> h
      Nothing -> unsafeCrashWith $ "getWitness: Invalid depth " <> show d <> ", array length " <> show (Array.length state.emptyHashes)

    -- Compute hash of subtree rooted at given address with given subtree depth
    computeSubtree :: BigInt -> Int -> hash
    computeSubtree subAddr subDepth =
      if subDepth == 0 then
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
      Just v -> Path v

-- | Compute the implied root from a value hash and its witness
-- |
-- | Given an address, the hash of the value at that address, and the witness path,
-- | compute what the root hash would be.
impliedRoot
  :: forall d hash
   . MergeHash hash
  => Address d
  -> hash
  -> Path d hash
  -> hash
impliedRoot (Address addr0) entryHash (Path path0) =
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
  -> f { address :: Address d, value :: a }
toUnfoldable (SparseMerkleTree { values }) =
  Array.toUnfoldable $ map (\(Tuple k v) -> { address: Address k, value: v }) (Map.toUnfoldable values :: Array _)
