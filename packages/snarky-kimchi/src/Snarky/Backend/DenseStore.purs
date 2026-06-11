-- | Function-local mutable dense stores (Int-indexed) for the constraint-
-- | system wiring passes: an `STArray Global` of `Maybe` slots, replacing
-- | `Map` with O(1) array access. Use is strictly local (create, fill,
-- | fold — never escapes the enclosing function).
module Snarky.Backend.DenseStore
  ( DenseStore
  , fresh
  , pushAt
  , setAt
  , getAt
  , foldSlots
  , toEntries
  ) where

import Prelude

import Control.Monad.ST (ST) as ST
import Control.Monad.ST.Global (Global, toEffect)
import Data.Array as Array
import Data.Array.ST (STArray)
import Data.Array.ST as STA
import Data.FoldableWithIndex (foldlWithIndex)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Unsafe (unsafePerformEffect)

newtype DenseStore v = DenseStore (STArray Global (Maybe v))

fresh :: forall v. Effect (DenseStore v)
fresh = DenseStore <$> toEffect STA.new

-- | Poke with `Nothing`-padding growth to cover sparse indices.
write :: forall v. Int -> Maybe v -> STArray Global (Maybe v) -> ST.ST Global Unit
write i v s = do
  ok <- STA.poke i v s
  if ok then pure unit
  else do
    _ <- STA.push Nothing s
    write i v s

-- | Append `v` to the array at slot `i`.
pushAt :: forall v. Int -> v -> DenseStore (Array v) -> Effect Unit
pushAt i v (DenseStore s) = toEffect do
  cur <- STA.peek i s
  case join cur of
    Just xs -> write i (Just (Array.snoc xs v)) s
    Nothing -> write i (Just [ v ]) s

setAt :: forall v. Int -> v -> DenseStore v -> Effect Unit
setAt i v (DenseStore s) = toEffect (write i (Just v) s)

getAt :: forall v. Int -> DenseStore v -> Maybe v
getAt i (DenseStore s) = join (unsafePerformEffect (toEffect (STA.peek i s)))

snapshot :: forall v. DenseStore v -> Array (Maybe v)
snapshot (DenseStore s) = unsafePerformEffect (toEffect (STA.freeze s))

-- | Fold filled slots, ascending by index.
foldSlots :: forall v r. (r -> Int -> v -> r) -> r -> DenseStore v -> r
foldSlots f init s =
  foldlWithIndex
    ( \i acc -> case _ of
        Just v -> f acc i v
        Nothing -> acc
    )
    init
    (snapshot s)

-- | All filled slots, ascending by index.
toEntries :: forall v r. (Int -> v -> r) -> DenseStore v -> Array r
toEntries mk s = Array.catMaybes (mapWithIndex (\i -> map (mk i)) (snapshot s))
