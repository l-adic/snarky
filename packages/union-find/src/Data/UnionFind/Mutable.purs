-- | Mutable int-keyed union-find: flat `STArray Global` parent/rank with
-- | path compression and union by rank — the textbook near-O(1) structure,
-- | replacing the pure Map-backed variant on the builder's hot path.
-- | Lives in `Effect` via `toEffect` (`ST Global` shares Effect's runtime
-- | representation).
module Data.UnionFind.Mutable
  ( MutableUF
  , fresh
  , find
  , union
  , rootOf
  , equivalenceClasses
  ) where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST.Global (Global, toEffect)
import Control.Monad.ST.Internal (for) as STI
import Data.Array as Array
import Data.Array.ST (STArray)
import Data.Array.ST as STA
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)

newtype MutableUF = MutableUF
  { parent :: STArray Global Int
  , rank :: STArray Global Int
  }

fresh :: Effect MutableUF
fresh = toEffect do
  parent <- STA.new
  rank <- STA.new
  pure (MutableUF { parent, rank })

-- | Grow the backing arrays so index `i` exists (new elements are their
-- | own parent, i.e. singleton classes).
ensure :: Int -> MutableUF -> ST Global Unit
ensure i (MutableUF s) = do
  n <- Array.length <$> STA.unsafeFreeze s.parent
  STI.for n (i + 1) \k -> do
    _ <- STA.push k s.parent
    STA.push 0 s.rank

rootLoop :: Int -> STArray Global Int -> ST Global Int
rootLoop x parent = do
  p <- STA.peek x parent
  case p of
    Just px | px /= x -> do
      -- path halving: point x at its grandparent as we walk
      gp <- STA.peek px parent
      case gp of
        Just gpx -> do
          _ <- STA.poke x gpx parent
          rootLoop gpx parent
        Nothing -> pure px
    _ -> pure x

-- | Find the representative, creating the element if unseen.
find :: Int -> MutableUF -> Effect Int
find x uf@(MutableUF s) = toEffect do
  ensure x uf
  rootLoop x s.parent

-- | Merge the classes of `x` and `y` (union by rank).
union :: Int -> Int -> MutableUF -> Effect Unit
union x y uf@(MutableUF s) = toEffect do
  ensure x uf
  ensure y uf
  rx <- rootLoop x s.parent
  ry <- rootLoop y s.parent
  when (rx /= ry) do
    mcx <- STA.peek rx s.rank
    mcy <- STA.peek ry s.rank
    let cx = maybe' 0 mcx
    let cy = maybe' 0 mcy
    if cx < cy then void $ STA.poke rx ry s.parent
    else if cx > cy then void $ STA.poke ry rx s.parent
    else do
      _ <- STA.poke ry rx s.parent
      void $ STA.poke rx (cx + 1) s.rank
  where
  maybe' d = case _ of
    Just v -> v
    Nothing -> d

-- | Root of every seen element, dense by element index (element i's root
-- | at slot i). Pure consumers (the wiring pass) take this frozen view.
rootOf :: MutableUF -> Effect (Array Int)
rootOf (MutableUF s) = toEffect do
  frozen <- STA.unsafeFreeze s.parent
  let n = Array.length frozen
  out <- STA.new
  STI.for 0 n \i -> do
    r <- rootLoop i s.parent
    STA.push r out
  STA.unsafeFreeze out

-- | Equivalence classes (each ascending; matching the pure variant's
-- | enumeration order). Test-path only.
equivalenceClasses :: MutableUF -> Effect (Array (Array Int))
equivalenceClasses uf = do
  roots <- rootOf uf
  let
    grouped = Array.foldl (\acc (Tuple i r) -> Map.insertWith append r [ i ] acc) Map.empty
      (Array.mapWithIndex Tuple roots)
  pure (Array.fromFoldable (Map.values grouped))
