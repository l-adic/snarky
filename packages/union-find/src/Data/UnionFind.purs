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

-- | Interface for Union-Find operations
class Monad m <= MonadUnionFind a m where
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

-- | The Union-Find data structure
newtype UnionFindData a = UnionFindData
  { parent :: Map a a -- parent pointers
  , rank :: Map a Int -- rank for union by rank
  }

derive instance Newtype (UnionFindData a) _

-- | Create an empty union-find data structure
emptyUnionFind :: forall a. UnionFindData a
emptyUnionFind = UnionFindData { parent: Map.empty, rank: Map.empty }

-- | Implementation for any MonadState with a unionFind field
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