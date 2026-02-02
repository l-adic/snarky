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
-- | import Control.Monad.State (evalState)
-- | import Data.UnionFind (emptyUnionFind, find, union, connected)
-- |
-- | example :: Boolean
-- | example = flip evalState emptyUnionFind do
-- |   union 1 2
-- |   union 2 3
-- |   connected 1 3  -- true: 1 and 3 are in the same equivalence class
-- | ```
module Data.UnionFind
  ( class MonadUnionFind
  , find
  , union
  , connected
  , equivalenceClasses
  , UnionFindData(..)
  , emptyUnionFind
  ) where

import Prelude

import Control.Monad.State (State)
import Control.Monad.State.Class (get, modify_)
import Data.Array as Array
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype, over)

-- | Type class for monads supporting union-find operations.
-- |
-- | The type parameter `a` is the element type (must be `Ord` for the
-- | standard implementation), and `m` is the monad providing the state.
class Monad m <= MonadUnionFind a m where
  -- | Find the representative (root) of an element's equivalence class.
  -- |
  -- | Elements in the same equivalence class will return the same
  -- | representative. If the element hasn't been seen before, it becomes
  -- | its own representative (a singleton equivalence class).
  find :: a -> m a

  -- | Merge the equivalence classes containing two elements.
  -- |
  -- | After `union x y`, `find x` and `find y` will return the same
  -- | representative.
  union :: a -> a -> m Unit

-- | Check if two elements are in the same equivalence class.
-- |
-- | ```purescript
-- | example = flip evalState emptyUnionFind do
-- |   union 1 2
-- |   c1 <- connected 1 2  -- true
-- |   c2 <- connected 1 3  -- false
-- |   pure { c1, c2 }
-- | ```
connected :: forall a m. MonadUnionFind a m => Eq a => a -> a -> m Boolean
connected x y = do
  rootX <- find x
  rootY <- find y
  pure (rootX == rootY)

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

-- | Standard implementation using `State (UnionFindData a)`.
-- |
-- | Uses path compression in `find` and union by rank in `union` for
-- | near-constant amortized time complexity (inverse Ackermann function).
instance (Ord a) => MonadUnionFind a (State (UnionFindData a)) where
  find x = do
    UnionFindData st <- get
    case Map.lookup x st.parent of
      Nothing -> do
        -- First time seeing this element, make it its own parent
        modify_ $ over UnionFindData \s -> s
          { parent = Map.insert x x s.parent
          , rank = Map.insert x 0 s.rank
          }
        pure x
      Just p ->
        if p == x then pure x
        else do
          root <- find p
          -- Path compression
          modify_ $ over UnionFindData \s -> s
            { parent = Map.insert x root s.parent }
          pure root

  union x y = do
    rootX <- find x
    rootY <- find y

    when (rootX /= rootY) do
      UnionFindData st <- get
      let rankX = fromMaybe 0 $ Map.lookup rootX st.rank
      let rankY = fromMaybe 0 $ Map.lookup rootY st.rank

      -- Union by rank
      if rankX < rankY then modify_ $ over UnionFindData \s -> s
        { parent = Map.insert rootX rootY s.parent }
      else if rankX > rankY then modify_ $ over UnionFindData \s -> s
        { parent = Map.insert rootY rootX s.parent }
      else modify_ $ over UnionFindData \s -> s
        { parent = Map.insert rootY rootX s.parent
        , rank = Map.insert rootX (rankX + 1) s.rank
        }