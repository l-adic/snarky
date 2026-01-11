module Data.MerkleTree
  ( MerkleTree(..)
  , NonEmptyTree(..)
  , Tree(..)
  , Address(..)
  , Path
  , depth
  , create
  , leftTree
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

import Partial.Unsafe (unsafeCrashWith)
import Data.Array as Array
import Data.Foldable (class Foldable)
import Data.List (List(..), (:))
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Traversable (class Traversable)
import Data.Unfoldable (class Unfoldable, class Unfoldable1)
import JS.BigInt (BigInt)
import JS.BigInt as BigInt
import Data.MerkleTree.Hashable (class MerkleHashable, class MergeHash, FreeHash(..), hash, merge, defaultHash)
import Data.MerkleTree.Hashable (class MerkleHashable, class MergeHash, class Hashable, FreeHash(..), hash, merge, defaultHash) as ReExports

-- Address uses BigInt to handle large tree depths
newtype Address = Address BigInt

derive newtype instance Show Address

data Tree hash a
  = Empty
  | NonEmpty (NonEmptyTree hash a)

data NonEmptyTree hash a
  = Leaf hash a
  | Node hash (Tree hash a) (Tree hash a)

-- The main merkle tree type
data MerkleTree hash a = MerkleTree
  { tree :: NonEmptyTree hash a
  , depth :: Int
  , count :: BigInt
  }

nextAvailableAddress :: forall hash a. MerkleTree hash a -> Address
nextAvailableAddress (MerkleTree { count }) = Address count

-- Helper to get hash of a tree
treeHash
  :: forall hash a
   . MerkleHashable a hash
  => Tree hash a
  -> hash
treeHash = case _ of
  Empty -> defaultHash @a
  NonEmpty t -> nonEmptyHash t

-- Helper to get hash of non-empty tree
nonEmptyHash
  :: forall hash a
   . NonEmptyTree hash a
  -> hash
nonEmptyHash = case _ of
  Leaf h _ -> h
  Node h _ _ -> h

-- Get the depth of the tree
depth :: forall hash a. MerkleTree hash a -> Int
depth (MerkleTree t) = t.depth

-- Create a new merkle tree with a single element
create
  :: forall hash a
   . MerkleHashable a hash
  => a
  -> MerkleTree hash a
create value =
  MerkleTree
    { tree: Leaf (hash (Just value)) value
    , depth: 0
    , count: one
    }

-- Check if the i-th bit of n is set (0-indexed)
ithBit
  :: BigInt
  -> Int
  -> Boolean
ithBit n i = BigInt.and (BigInt.shr n (BigInt.fromInt i)) one == one

-- Create a left-leaning tree of given depth with element at leftmost position
leftTree
  :: forall hash a
   . MerkleHashable a hash
  => Int
  -> a
  -> { hash :: hash, tree :: NonEmptyTree hash a }
leftTree targetDepth v =
  let
    leafHash = hash @a (Just v)

    go :: Int -> hash -> NonEmptyTree hash a -> { hash :: hash, tree :: NonEmptyTree hash a }
    go i h acc =
      if i == targetDepth then
        { hash: h, tree: acc }
      else
        let
          h' = merge h (defaultHash @a)
          tree' = Node h' (NonEmpty acc) Empty
        in
          go (i + 1) h' tree'
  in
    go 0 leafHash (Leaf leafHash v)

-- Add an element to the tree
add_
  :: forall hash a
   . MerkleHashable a hash
  => MerkleTree hash a
  -> a
  -> MerkleTree hash a
add_ mt@(MerkleTree t) value =
  if t.count == BigInt.shl one (BigInt.fromInt t.depth) then
    -- Tree is full, need to increase depth
    let
      result = leftTree t.depth value
      hl = nonEmptyHash t.tree
      hr = result.hash
    in
      MerkleTree
        { tree: Node (merge hl hr) (NonEmpty t.tree) (NonEmpty result.tree)
        , count: t.count + BigInt.fromInt 1
        , depth: t.depth + 1
        }
  else
    let
      tree' = insert t.tree (BigInt.shl one (BigInt.fromInt (t.depth - 1))) (nextAvailableAddress mt) value
    in
      -- Insert at position count
      MerkleTree t
        { tree = tree'
        , count = t.count + one
        }

-- Insert element at given address using mask for navigation
-- NB: the unsafeCrashWith here is justified because we
-- generate fresh addresses.
insert
  :: forall hash a
   . MerkleHashable a hash
  => NonEmptyTree hash a
  -> BigInt -- mask
  -> Address -- address
  -> a -- value to insert
  -> NonEmptyTree hash a
insert tree0 mask0 (Address address) v =
  let
    go :: BigInt -> Tree hash a -> NonEmptyTree hash a
    go mask tree =
      if mask == zero then
        case tree of
          Empty -> Leaf (hash (Just v)) v
          NonEmpty _ -> unsafeCrashWith "impossible: cannot insert new leaf in occupied slot"
      else
        let
          goLeft = BigInt.and mask address == zero
          mask' = BigInt.shr mask one
        in
          case tree of
            Empty ->
              if goLeft then
                let
                  tl' = go mask' Empty
                in
                  Node (merge (nonEmptyHash tl') (defaultHash @a)) (NonEmpty tl') Empty
              else
                let
                  tr' = go mask' Empty
                in
                  Node (merge (defaultHash @a) (nonEmptyHash tr')) Empty (NonEmpty tr')
            NonEmpty (Node _ tl tr) ->
              if goLeft then
                let
                  tl' = go mask' tl
                in
                  Node (merge (nonEmptyHash tl') (treeHash tr)) (NonEmpty tl') tr
              else
                let
                  tr' = go mask' tr
                in
                  Node (merge (treeHash tl) (nonEmptyHash tr')) tl (NonEmpty tr')
            NonEmpty (Leaf _ _) ->
              unsafeCrashWith "impossible: cannot insert past leaf"
  in
    go mask0 (NonEmpty tree0)

-- Add many elements efficiently, ie just add them to the tree
-- then re-merkelize at the end
addMany
  :: forall hash a
   . MerkleHashable a hash
  => MerkleTree hash a
  -> List a
  -> MerkleTree hash a
addMany _tree xs =
  let
    dirtyTree = List.foldl addOneDirty _tree xs
  in
    merkelize dirtyTree

  where
  -- Add one element without computing hashes
  addOneDirty
    :: MerkleTree hash a
    -> a
    -> MerkleTree hash a
  addOneDirty mt@(MerkleTree t) z =
    if t.count == BigInt.shl one (BigInt.fromInt t.depth) then
      -- Tree is full, create new level
      let
        tr = leftTreeDirty (defaultHash @a) t.depth z
      in
        MerkleTree
          { tree: Node (defaultHash @a) (NonEmpty t.tree) (NonEmpty tr)
          , count: t.count + one
          , depth: t.depth + 1
          }
    else
      -- Set at current count position
      MerkleTree t
        { tree = setDirty (defaultHash @a) t.tree (addressBits t.depth (nextAvailableAddress mt)) z
        , count = t.count + one
        }
    where

    -- Convert integer address to bit path
    addressBits
      :: Int
      -> Address
      -> Array Boolean
    addressBits treeDepth (Address addr) =
      Array.fromFoldable $ map (ithBit addr) (List.reverse $ List.range 0 (treeDepth - 1))

    -- Create left tree without computing hashes
    leftTreeDirty :: hash -> Int -> a -> NonEmptyTree hash a
    leftTreeDirty default targetDepth value =
      let
        go i acc =
          if i == targetDepth then acc
          else go (i + 1) (Node default (NonEmpty acc) Empty)
      in
        go 0 (Leaf default value)

    -- Set value at address without computing hashes
    setDirty :: hash -> NonEmptyTree hash a -> Array Boolean -> a -> NonEmptyTree hash a
    setDirty default tree addr x = go tree (Array.toUnfoldable addr)
      where
      go :: NonEmptyTree hash a -> List Boolean -> NonEmptyTree hash a
      go currentTree path =
        case path of
          Nil -> Leaf default x
          goRight : rest ->
            case currentTree of
              -- If we hit a Leaf but still have bits to process, we must 
              -- "push" the existing leaf down and create new Node structure
              Leaf _ _ ->
                if goRight then
                  Node default Empty (NonEmpty (go (Leaf default x) rest))
                else
                  Node default (NonEmpty (go (Leaf default x) rest)) Empty
              Node _ l r ->
                if goRight then
                  Node default l (NonEmpty (go (fromTreeWithDefault r) rest))
                else
                  Node default (NonEmpty (go (fromTreeWithDefault l) rest)) r

      fromTreeWithDefault :: Tree hash a -> NonEmptyTree hash a
      fromTreeWithDefault = case _ of
        Empty -> Leaf default x -- Fill empty with new value
        NonEmpty _t -> _t

  -- Recompute all hashes in tree
  merkelize
    :: MerkleTree hash a
    -> MerkleTree hash a
  merkelize (MerkleTree t) =
    let
      default = hash @a Nothing

      recomputeTree :: Tree hash a -> Tree hash a
      recomputeTree = case _ of
        Empty -> Empty
        NonEmpty nonEmptyTree -> NonEmpty (recomputeNonEmpty nonEmptyTree)

      recomputeNonEmpty :: NonEmptyTree hash a -> NonEmptyTree hash a
      recomputeNonEmpty = case _ of
        Leaf _ x -> Leaf (hash @a (Just x)) x
        Node _ l r ->
          let
            l' = recomputeTree l
            r' = recomputeTree r
            lHash = case l' of
              Empty -> default
              NonEmpty lt -> nonEmptyHash lt
            rHash = case r' of
              Empty -> default
              NonEmpty rt -> nonEmptyHash rt
          in
            Node (merge lHash rHash) l' r'
    in
      MerkleTree t { tree = recomputeNonEmpty t.tree }

-- Get element at address
get
  :: forall hash a
   . MerkleTree hash a
  -> Address
  -> Maybe a
get (MerkleTree t) (Address addr0) =
  let
    go :: Tree hash a -> Int -> Maybe a
    go Empty _ = Nothing
    go (NonEmpty tree) i = goNonEmpty tree i

    goNonEmpty :: NonEmptyTree hash a -> Int -> Maybe a
    goNonEmpty tree i =
      case tree of
        Node _ l r ->
          let
            goRight = ithBit addr0 i
          in
            if goRight then go r (i - 1) else go l (i - 1)
        Leaf _ x -> Just x
  in
    goNonEmpty t.tree (t.depth - 1)

newtype Path hash = Path (List hash)

derive newtype instance (Eq hash) => Eq (Path hash)
derive newtype instance (Show hash) => Show (Path hash)

derive instance Functor Path
derive instance Foldable Path
derive instance Traversable Path
derive newtype instance Unfoldable1 Path
derive newtype instance Unfoldable Path

-- Get the path from leaf to root
getPath
  :: forall hash a
   . MerkleHashable a hash
  => MerkleTree hash a
  -> Address
  -> Maybe (Path hash)
getPath (MerkleTree t) (Address addr0) =
  let
    go :: List hash -> NonEmptyTree hash a -> Int -> Maybe (List hash)
    go acc tree i =
      if i < 0 then Just acc
      else
        let
          goRight = ithBit addr0 i
        in
          case tree of
            Leaf _ _ -> Just acc -- We've reached the leaf, return accumulated path
            Node _ l r ->
              if goRight then
                case r of
                  Empty -> Nothing
                  NonEmpty tr' -> go (treeHash l : acc) tr' (i - 1)
              else
                case l of
                  Empty -> Nothing
                  NonEmpty tl' -> go (treeHash r : acc) tl' (i - 1)
  in
    Path <$> go Nil t.tree (t.depth - 1)

-- Compute root from a value and path
impliedRoot
  :: forall hash
   . MergeHash hash
  => Address
  -> hash
  -> Path hash
  -> hash
impliedRoot (Address addr0) entryHash (Path path0) =
  let
    go :: hash -> Int -> List hash -> hash
    go acc _ Nil = acc
    go acc i (h : hs) =
      if ithBit addr0 i then
        go (merge h acc) (i + 1) hs
      else
        go (merge acc h) (i + 1) hs
  in
    go entryHash 0 path0

-- Get free hash path
getFreePath
  :: forall hash a
   . MerkleTree hash a
  -> Address
  -> Maybe (Path (FreeHash a))
getFreePath (MerkleTree t) (Address addr0) =
  let
    go :: List (FreeHash a) -> NonEmptyTree hash a -> Int -> Maybe (List (FreeHash a))
    go acc tree i =
      if i < 0 then Just acc
      else
        let
          goRight = ithBit addr0 i
        in
          case tree of
            Leaf _ _ -> Just acc -- We've reached the leaf, return accumulated path
            Node _ l r ->
              if goRight then
                case r of
                  Empty -> Nothing
                  NonEmpty tr' -> go (treeFreeHash l : acc) tr' (i - 1)
              else
                case l of
                  Empty -> Nothing
                  NonEmpty tl' -> go (treeFreeHash r : acc) tl' (i - 1)
  in
    Path <$> go Nil t.tree (t.depth - 1)

-- Helper to convert tree to free hash
treeFreeHash
  :: forall hash a
   . Tree hash a
  -> FreeHash a
treeFreeHash = case _ of
  Empty -> HashEmpty
  NonEmpty t -> nonEmptyFreeHash t

-- Helper to convert non-empty tree to free hash
nonEmptyFreeHash
  :: forall hash a
   . NonEmptyTree hash a
  -> FreeHash a
nonEmptyFreeHash = case _ of
  Leaf _ x -> HashValue x
  Node _ l r -> Merge (treeFreeHash l) (treeFreeHash r)

-- Get free hash of root
freeRoot :: forall hash a. MerkleTree hash a -> FreeHash a
freeRoot (MerkleTree t) = nonEmptyFreeHash t.tree

-- Compute free root from value and path  
impliedFreeRoot
  :: forall a
   . Address
  -> a
  -> Path (FreeHash a)
  -> FreeHash a
impliedFreeRoot (Address addr0) value (Path path0) =
  let
    go :: FreeHash a -> Int -> List (FreeHash a) -> FreeHash a
    go acc _ Nil = acc
    go acc i (h : hs) =
      if ithBit addr0 i then
        go (Merge h acc) (i + 1) hs
      else
        go (Merge acc h) (i + 1) hs
  in
    go (HashValue value) 0 path0

-- Get root hash
root :: forall hash a. MerkleTree hash a -> hash
root (MerkleTree t) = nonEmptyHash t.tree

-- Convert to list of elements
toUnfoldable :: forall hash a f. Unfoldable f => MerkleTree hash a -> f a
toUnfoldable (MerkleTree t) = List.toUnfoldable $ toListTree (NonEmpty t.tree)

-- Helper to convert tree to list
toListTree :: forall hash a. Tree hash a -> List a
toListTree = case _ of
  Empty -> Nil
  NonEmpty (Leaf _ x) -> x : Nil
  NonEmpty (Node _ l r) -> toListTree l <> toListTree r

-- Helper to check tree
checkTree
  :: forall hash a
   . MerkleHashable a hash
  => Eq hash
  => Tree hash a
  -> Maybe hash
checkTree = case _ of
  Empty -> Just (defaultHash @a)
  NonEmpty t -> checkNonEmpty t

-- Helper to check non-empty tree
checkNonEmpty
  :: forall hash a
   . MerkleHashable a hash
  => Eq hash
  => NonEmptyTree hash a
  -> Maybe hash
checkNonEmpty = case _ of
  Leaf h x ->
    let
      expected = hash @a (Just x)
    in
      if h == expected then Just h
      else Nothing
  Node h l r -> do
    lh <- checkTree l
    rh <- checkTree r
    let
      expected = merge lh rh
    if h == expected then Just h else Nothing