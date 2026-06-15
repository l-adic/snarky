-- | A Merkle *mask* — PureScript translation of Mina's
-- | `sparse_ledger_lib/sparse_ledger.ml`.
-- |
-- | Unlike `Data.MerkleTree.Sparse` (a full ledger that treats unpopulated
-- | subtrees as empty via one global `emptyHashes` per level), a mask is a
-- | *partial* tree: only the touched leaves are kept, and every off-path
-- | subtree is collapsed to its real frontier hash (`Hash`). Because those
-- | `Hash` nodes carry the actual hashes from the source tree, the mask
-- | reproduces the full ledger's root under `get`/`set` — that's what makes it
-- | a self-contained per-transaction witness.
-- |
-- | Mirrors OCaml `Tree.t = Account | Hash | Node of hash * t * t` (the `Node`
-- | caches its own hash, so `treeHash` is O(1) and `set` recomputes only the
-- | touched spine). Traversal matches OCaml `ith_bit idx i = (idx lsr i) land 1`
-- | — the MSB is the root-level direction, the LSB the leaf.
module Data.MerkleTree.Sparse.Mask
  ( Tree(..)
  , SparseLedger(..)
  , treeHash
  , ofHash
  , merkleRoot
  , get
  , set
  , getPath
  , findIndex
  , addPath
  , fromSubset
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust)
import Data.MerkleTree (ithBit)
import Data.MerkleTree.Hashable (class MerkleHashable, hashLeaf, merge)
import Data.MerkleTree.Sized (Address(..), Path(..))
import Data.MerkleTree.Sparse (SparseMerkleTree)
import Data.MerkleTree.Sparse as Full
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import Foreign (ForeignError(..), fail)
import Partial.Unsafe (unsafePartial)
import Simple.JSON (class ReadForeign, class WriteForeign, readImpl, writeImpl)
import Type.Proxy (Proxy(..))

-- | Mina `Tree.t`. A leaf carries `Maybe a` so an empty-but-touched slot
-- | (receiver-account creation) is representable and settable rather than
-- | collapsed. `Node` caches its subtree hash.
data Tree hash a
  = Account (Maybe a)
  | Hash hash
  | Node hash (Tree hash a) (Tree hash a)

-- | Mina `T.t = { indexes; depth; tree }`. `depth` is the phantom `d`;
-- | `indexes` maps an account id (here a public key) to its leaf address, so a
-- | worker can resolve `getAccountId` against the mask alone.
newtype SparseLedger d hash key a = SparseLedger
  { indexes :: Map key (Address d)
  , tree :: Tree hash a
  }

-- Transport codecs: a tagged form for the recursive tree, and `indexes` as an
-- array of key/address pairs (its key is not a JSON string).
instance (WriteForeign hash, WriteForeign a) => WriteForeign (Tree hash a) where
  writeImpl = case _ of
    Account ma -> writeImpl { tag: "account", value: ma }
    Hash h -> writeImpl { tag: "hash", value: h }
    Node h l r -> writeImpl { tag: "node", hash: h, left: l, right: r }

instance (ReadForeign hash, ReadForeign a) => ReadForeign (Tree hash a) where
  readImpl f = do
    tagged :: { tag :: String } <- readImpl f
    case tagged.tag of
      "account" -> (\(r :: { value :: Maybe a }) -> Account r.value) <$> readImpl f
      "hash" -> (\(r :: { value :: hash }) -> Hash r.value) <$> readImpl f
      "node" ->
        (\(r :: { hash :: hash, left :: Tree hash a, right :: Tree hash a }) -> Node r.hash r.left r.right) <$> readImpl f
      other -> fail (ForeignError ("Tree: unknown tag " <> other))

instance (Ord key, WriteForeign key, WriteForeign hash, WriteForeign a) => WriteForeign (SparseLedger d hash key a) where
  writeImpl (SparseLedger r) = writeImpl
    { indexes: (Map.toUnfoldable r.indexes :: Array (Tuple key (Address d))) <#> \(Tuple k v) -> { key: k, address: v }
    , tree: r.tree
    }

instance (Ord key, ReadForeign key, ReadForeign hash, ReadForeign a) => ReadForeign (SparseLedger d hash key a) where
  readImpl f = do
    r :: { indexes :: Array { key :: key, address :: Address d }, tree :: Tree hash a } <- readImpl f
    pure $ SparseLedger
      { indexes: Map.fromFoldable (r.indexes <#> \i -> Tuple i.key i.address)
      , tree: r.tree
      }

-- | O(1) subtree hash (OCaml `hash`): a cached `Node`/`Hash`, or the leaf hash.
treeHash :: forall hash a. MerkleHashable a hash => Tree hash a -> hash
treeHash = case _ of
  Account ma -> hashLeaf ma
  Hash h -> h
  Node h _ _ -> h

-- | A fully-collapsed mask: just the root hash (OCaml `of_hash`). The starting
-- | point for `addPath`/`fromSubset`.
ofHash :: forall d hash key a. hash -> SparseLedger d hash key a
ofHash h = SparseLedger { indexes: Map.empty, tree: Hash h }

merkleRoot :: forall d hash key a. MerkleHashable a hash => SparseLedger d hash key a -> hash
merkleRoot (SparseLedger { tree }) = treeHash tree

-- | OCaml `find_index_exn` (total here).
findIndex :: forall d hash key a. Ord key => key -> SparseLedger d hash key a -> Maybe (Address d)
findIndex k (SparseLedger { indexes }) = Map.lookup k indexes

--------------------------------------------------------------------------------
-- Traversal. OCaml descends `go (depth - 1) tree`, `go_right = ith_bit idx i`,
-- bottoming out at `i < 0` (the leaf). So bit `depth-1` (MSB) is the root
-- direction and bit 0 (LSB) the leaf.

-- | OCaml `get_exn` (returns `Nothing` instead of raising).
get :: forall d hash key a. Reflectable d Int => Address d -> SparseLedger d hash key a -> Maybe a
get (Address idx) (SparseLedger { tree }) = go (reflectType (Proxy @d) - 1) tree
  where
  go i = case _ of
    Account ma | i < 0 -> ma
    Node _ l r | i >= 0 -> go (i - 1) (if ithBit idx i then r else l)
    _ -> Nothing

-- | OCaml `set_exn`: rebuild the touched spine, recomputing each `Node`'s
-- | cached hash bottom-up via `merge` — shared ancestors of two touched leaves
-- | stay consistent automatically (no stale paths).
set
  :: forall d hash key a
   . Reflectable d Int
  => MerkleHashable a hash
  => Address d
  -> a
  -> SparseLedger d hash key a
  -> SparseLedger d hash key a
set (Address idx) acct (SparseLedger sl) =
  SparseLedger sl { tree = go (reflectType (Proxy @d) - 1) sl.tree }
  where
  go i tree
    | i < 0 = case tree of
        Account _ -> Account (Just acct)
        _ -> tree
    | otherwise = case tree of
        Node _ l r ->
          let
            Tuple l' r' =
              if ithBit idx i then Tuple l (go (i - 1) r)
              else Tuple (go (i - 1) l) r
          in
            Node (merge (treeHash l') (treeHash r')) l' r'
        _ -> tree

-- | OCaml `path_exn`, returning the bare sibling hashes (leaf→root); the L/R
-- | direction is recoverable from the address, matching
-- | `Data.MerkleTree.Sparse.impliedRoot`.
getPath
  :: forall d hash key a
   . Reflectable d Int
  => MerkleHashable a hash
  => Address d
  -> SparseLedger d hash key a
  -> Path d hash
getPath (Address idx) (SparseLedger { tree }) =
  Path (unsafePartial (fromJust (Vector.toVector @d (go [] (reflectType (Proxy @d) - 1) tree))))
  where
  go acc i = case _ of
    Node _ l r | i >= 0 ->
      if ithBit idx i then go (Array.cons (treeHash l) acc) (i - 1) r
      else go (Array.cons (treeHash r) acc) (i - 1) l
    _ -> acc

--------------------------------------------------------------------------------
-- Extraction (OCaml `add_path` / `of_ledger_subset`).

-- | Insert one account at `addr` into the mask, un-collapsing `Hash` nodes
-- | along its path using the provided sibling hashes (leaf→root). Existing
-- | `Node`s keep their cached hash (their value is unchanged — we only refine a
-- | collapsed sibling deeper); newly built spine nodes recompute via `merge`.
-- | OCaml `add_path` / `add_path_impl`.
addPath
  :: forall d hash key a
   . Reflectable d Int
  => MerkleHashable a hash
  => Ord key
  => Address d
  -> Maybe key
  -> Maybe a
  -> Path d hash
  -> SparseLedger d hash key a
  -> SparseLedger d hash key a
addPath addr mkey macc (Path siblings) (SparseLedger sl) =
  SparseLedger
    { indexes: case mkey of
        Just k -> Map.insert k addr sl.indexes
        Nothing -> sl.indexes
    , tree: go (reflectType (Proxy @d) - 1) sl.tree
    }
  where
  Address idx = addr
  sibArr = Vector.toUnfoldable siblings
  sib i = unsafePartial (Array.unsafeIndex sibArr i) -- path[i], leaf = 0

  -- descend existing structure; reuse cached `Node` hashes, un-collapse `Hash`
  go i tree
    | i < 0 = Account macc
    | otherwise = case tree of
        Node h l r ->
          if ithBit idx i then Node h l (go (i - 1) r)
          else Node h (go (i - 1) l) r
        Hash h ->
          -- un-collapse THIS node, reusing its hash `h`; the chosen child is
          -- built fresh from the path tail, the sibling is the path hash.
          let
            sibT = Hash (sib i)
            child = buildSpine (i - 1)
            Tuple l r = if ithBit idx i then Tuple sibT child else Tuple child sibT
          in
            Node h l r
        Account _ -> Account macc

  -- build a fresh Node spine from level `i` down to the leaf, recomputing hashes
  buildSpine i
    | i < 0 = Account macc
    | otherwise =
        let
          sibT = Hash (sib i)
          child = buildSpine (i - 1)
          Tuple l r = if ithBit idx i then Tuple sibT child else Tuple child sibT
        in
          Node (merge (treeHash l) (treeHash r)) l r

-- | Build a mask from a full sparse tree by overlaying the witnesses of a set
-- | of touched addresses (each tagged with its account id for the index map).
-- | OCaml `Sparse_ledger.of_ledger_subset_exn`.
fromSubset
  :: forall d hash key a
   . Reflectable d Int
  => MerkleHashable a hash
  => Ord key
  => SparseMerkleTree d hash a
  -> Array (Tuple (Address d) (Maybe key))
  -> SparseLedger d hash key a
fromSubset full =
  foldl
    ( \acc (Tuple addr mkey) ->
        addPath addr mkey (Full.get full addr) (Full.getWitness addr full) acc
    )
    (ofHash (Full.root full))
