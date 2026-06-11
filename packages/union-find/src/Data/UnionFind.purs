-- | Union-Find (Disjoint Set Union) data structure.
-- |
-- | This module provides an efficient implementation of the union-find data
-- | structure for tracking equivalence classes. It supports two primary
-- | operations:
-- |
-- | - `find`: Determine which equivalence class an element belongs to
-- | - `union`: Merge two equivalence classes into one
-- |
-- | The implementation uses path compression and union by rank for
-- | near-constant amortized time complexity.
-- |
-- | ```purescript
-- | import Data.UnionFind (emptyUnionFind, find, union, connected)
-- |
-- | example :: Boolean
-- |   union 1 2
-- |   union 2 3
-- |   connected 1 3  -- true: 1 and 3 are in the same equivalence class
-- | ```
module Data.UnionFind
  ( find
  , union
  , connected
  , equivalenceClasses
  , UnionFindData(..)
  , emptyUnionFind
  ) where

import Prelude

import Data.Array as Array
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype)
import Data.Tuple (Tuple(..))

-- | Find the representative (root) of an element's equivalence class,
-- | with path compression. Elements in the same equivalence class return
-- | the same representative. If the element hasn't been seen before, it
-- | becomes its own representative (a singleton equivalence class).
find :: forall a. Ord a => a -> UnionFindData a -> Tuple a (UnionFindData a)
find x uf@(UnionFindData st) = case Map.lookup x st.parent of
  Nothing ->
    Tuple x $ UnionFindData st
      { parent = Map.insert x x st.parent
      , rank = Map.insert x 0 st.rank
      }
  Just p
    | p == x -> Tuple x uf
    | otherwise ->
        let
          Tuple root (UnionFindData st') = find p uf
        in
          -- Path compression
          Tuple root $ UnionFindData st' { parent = Map.insert x root st'.parent }

-- | Merge the equivalence classes containing two elements (union by rank).
-- | After `union x y`, `find x` and `find y` return the same representative.
union :: forall a. Ord a => a -> a -> UnionFindData a -> UnionFindData a
union x y uf0 =
  let
    Tuple rootX uf1 = find x uf0
    Tuple rootY uf2@(UnionFindData st) = find y uf1
  in
    if rootX == rootY then uf2
    else
      let
        rankX = fromMaybe 0 $ Map.lookup rootX st.rank
        rankY = fromMaybe 0 $ Map.lookup rootY st.rank
      in
        if rankX < rankY then UnionFindData st { parent = Map.insert rootX rootY st.parent }
        else if rankX > rankY then UnionFindData st { parent = Map.insert rootY rootX st.parent }
        else UnionFindData st
          { parent = Map.insert rootY rootX st.parent
          , rank = Map.insert rootX (rankX + 1) st.rank
          }

-- | Check if two elements are in the same equivalence class.
-- |
-- | ```purescript
-- |   union 1 2
-- |   c1 <- connected 1 2  -- true
-- |   c2 <- connected 1 3  -- false
-- |   pure { c1, c2 }
-- | ```
connected :: forall a. Ord a => a -> a -> UnionFindData a -> Tuple Boolean (UnionFindData a)
connected x y uf0 =
  let
    Tuple rootX uf1 = find x uf0
    Tuple rootY uf2 = find y uf1
  in
    Tuple (rootX == rootY) uf2

-- | Pure helper to find root without path compression (used by `equivalenceClasses`).
findRootPure :: forall a. Ord a => Map a a -> a -> a
findRootPure parentMap element =
  case Map.lookup element parentMap of
    Nothing -> element -- Element is its own root if not in map
    Just parent ->
      if parent == element then element -- Found root
      else findRootPure parentMap parent -- Recurse

-- | Extract all equivalence classes from the union-find structure.
-- |
-- | Returns an array of arrays, where each inner array contains all elements
-- | in the same equivalence class. This is a pure function that doesn't
-- | perform path compression.
-- |
-- | ```purescript
-- | finalState = execState (union 1 2 *> union 2 3 *> union 4 5) emptyUnionFind
-- | equivalenceClasses finalState
-- | -- [[1, 2, 3], [4, 5]] (order may vary)
-- | ```
equivalenceClasses :: forall a. Ord a => UnionFindData a -> Array (Array a)
equivalenceClasses (UnionFindData { parent }) =
  let
    -- Group elements by their root
    rootGroups = foldlWithIndex
      ( \element acc _ ->
          let
            root = findRootPure parent element
          in
            Map.insertWith (<>) root [ element ] acc
      )
      Map.empty
      parent
  in
    Array.fromFoldable (Map.values rootGroups)

-- | The union-find data structure, storing parent pointers and ranks.
-- |
-- | Use `emptyUnionFind` to create a new instance, then run operations
-- | in `State (UnionFindData a)`.
newtype UnionFindData a = UnionFindData
  { parent :: Map a a -- ^ Parent pointers forming a forest
  , rank :: Map a Int -- ^ Rank (upper bound on tree height) for union by rank
  }

derive instance Newtype (UnionFindData a) _

-- | Create an empty union-find structure with no elements.
emptyUnionFind :: forall a. UnionFindData a
emptyUnionFind = UnionFindData { parent: Map.empty, rank: Map.empty }
