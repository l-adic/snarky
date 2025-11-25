module Data.UnionFind
  ( class MonadUnionFind
  , find
  , union
  , connected
  , equivalenceClasses
  , UnionFindData
  , emptyUnionFind
  ) where

import Prelude

import Control.Monad.State.Class (class MonadState, get, modify_)
import Data.Array as Array
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)

-- | Interface for Union-Find operations
class Monad m <= MonadUnionFind a m | m -> a where
  -- | Find the representative of an element's equivalence class
  find :: a -> m a

  -- | Union two elements into the same equivalence class
  union :: a -> a -> m Unit

-- | Check if two elements are in the same equivalence class
connected :: forall a m. MonadUnionFind a m => Eq a => a -> a -> m Boolean
connected x y = do
  rootX <- find x
  rootY <- find y
  pure (rootX == rootY)

-- | Pure function to find root without path compression
findRootPure :: forall a. Ord a => Map a a -> a -> a
findRootPure parentMap element =
  case Map.lookup element parentMap of
    Nothing -> element -- Element is its own root if not in map
    Just parent ->
      if parent == element then element -- Found root
      else findRootPure parentMap parent -- Recurse

-- | Get all equivalence classes as an array of arrays (pure function)
equivalenceClasses :: forall a. Ord a => UnionFindData a -> Array (Array a)
equivalenceClasses { parent } =
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

-- | The Union-Find data structure
type UnionFindData a =
  { parent :: Map a a -- parent pointers
  , rank :: Map a Int -- rank for union by rank
  }

-- | Create an empty union-find data structure
emptyUnionFind :: forall a. UnionFindData a
emptyUnionFind = { parent: Map.empty, rank: Map.empty }

-- | Implementation for any MonadState with a unionFind field
instance (MonadState { unionFind :: UnionFindData a | s } m, Ord a) => MonadUnionFind a m where
  find x = do
    st <- get
    case Map.lookup x st.unionFind.parent of
      Nothing -> do
        -- First time seeing this element, make it its own parent
        modify_ \s -> s
          { unionFind = s.unionFind
              { parent = Map.insert x x s.unionFind.parent
              , rank = Map.insert x 0 s.unionFind.rank
              }
          }
        pure x
      Just p ->
        if p == x then pure x
        else do
          root <- find p
          -- Path compression
          modify_ \s -> s
            { unionFind = s.unionFind
                { parent = Map.insert x root s.unionFind.parent }
            }
          pure root

  union x y = do
    rootX <- find x
    rootY <- find y

    when (rootX /= rootY) do
      st <- get
      let rankX = fromMaybe 0 $ Map.lookup rootX st.unionFind.rank
      let rankY = fromMaybe 0 $ Map.lookup rootY st.unionFind.rank

      -- Union by rank
      if rankX < rankY then modify_ \s -> s
        { unionFind = s.unionFind
            { parent = Map.insert rootX rootY s.unionFind.parent }
        }
      else if rankX > rankY then modify_ \s -> s
        { unionFind = s.unionFind
            { parent = Map.insert rootY rootX s.unionFind.parent }
        }
      else modify_ \s -> s
        { unionFind = s.unionFind
            { parent = Map.insert rootY rootX s.unionFind.parent
            , rank = Map.insert rootX (rankX + 1) s.unionFind.rank
            }
        }