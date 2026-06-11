-- | Function-local mutable dense stores (Int-indexed) for the constraint-
-- | system wiring passes, replacing `Map` with O(1) array slots. Use is
-- | strictly local (ST-style): create, fill, fold — never escapes the
-- | enclosing function.
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

import Data.Function.Uncurried (Fn2, Fn3, Fn4, runFn2, runFn3, runFn4)
import Data.Maybe (Maybe(..))
import Effect (Effect)

foreign import data DenseStore :: Type -> Type

foreign import freshImpl :: forall v. Effect (DenseStore v)

foreign import pushAtImpl :: forall v. Fn3 Int v (DenseStore (Array v)) (Effect Unit)

foreign import setAtImpl :: forall v. Fn3 Int v (DenseStore v) (Effect Unit)

foreign import getAtImpl :: forall v. Fn4 (v -> Maybe v) (Maybe v) Int (DenseStore v) (Maybe v)

foreign import foldSlotsImpl :: forall v r. Fn3 (r -> Int -> v -> r) r (DenseStore v) r

fresh :: forall v. Effect (DenseStore v)
fresh = freshImpl

pushAt :: forall v. Int -> v -> DenseStore (Array v) -> Effect Unit
pushAt i v s = runFn3 pushAtImpl i v s

setAt :: forall v. Int -> v -> DenseStore v -> Effect Unit
setAt i v s = runFn3 setAtImpl i v s

getAt :: forall v. Int -> DenseStore v -> Maybe v
getAt i s = runFn4 getAtImpl Just Nothing i s

foldSlots :: forall v r. (r -> Int -> v -> r) -> r -> DenseStore v -> r
foldSlots f init s = runFn3 foldSlotsImpl f init s

foreign import toEntriesImpl :: forall v r. Fn2 (Int -> v -> r) (DenseStore v) (Array r)

-- | All filled slots, ascending by index.
toEntries :: forall v r. (Int -> v -> r) -> DenseStore v -> Array r
toEntries mk s = runFn2 toEntriesImpl mk s
