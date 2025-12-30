module Snarky.Circuit.Kimchi.Utils where

import Prelude

import Control.Monad.State (StateT(..), runStateT)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (Tuple)

mapAccumM
  :: forall m s t a b
   . Monad m
  => Traversable t
  => (s -> a -> m (Tuple b s))
  -> s
  -> t a
  -> m (Tuple (t b) s)
mapAccumM f initial xs = runStateT (traverse step xs) initial
  where
  step x = StateT (\s -> f s x)