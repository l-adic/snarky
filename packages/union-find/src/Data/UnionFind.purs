module Data.UnionFind
  ( class MonadUnionFind
  , find
  , union
  , connected
  , UnionFindData
  , emptyUnionFind
  ) where

import Prelude

import Control.Monad.State.Class (class MonadState, get, modify_)
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