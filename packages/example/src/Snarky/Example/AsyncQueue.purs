-- | A minimal unbounded buffered async channel: non-blocking `enqueue`, blocking
-- | `dequeue`. Single-consumer (the dequeuer); any number of producers.
-- |
-- | Backed by a `Ref` buffer plus an `AVar` used as a "non-empty" signal: each
-- | `enqueue` appends and `tryPut`s the signal (idempotent if already raised);
-- | `dequeue` blocks on the signal, pops one item, and re-raises the signal if
-- | more remain.
module Snarky.Example.AsyncQueue
  ( Queue
  , newQueue
  , enqueue
  , dequeue
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Effect.Aff.AVar (AVar)
import Effect.Aff.AVar as AVar
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref

newtype Queue a = Queue { items :: Ref (Array a), signal :: AVar Unit }

newQueue :: forall a. Aff (Queue a)
newQueue = do
  items <- liftEffect $ Ref.new []
  signal <- AVar.empty
  pure $ Queue { items, signal }

enqueue :: forall a. Queue a -> a -> Aff Unit
enqueue (Queue q) x = do
  liftEffect $ Ref.modify_ (\xs -> Array.snoc xs x) q.items
  void $ AVar.tryPut unit q.signal

dequeue :: forall a. Queue a -> Aff a
dequeue (Queue q) = do
  _ <- AVar.take q.signal
  xs <- liftEffect $ Ref.read q.items
  case Array.uncons xs of
    Nothing -> dequeue (Queue q) -- spurious wake; retry
    Just { head, tail } -> do
      liftEffect $ Ref.write tail q.items
      when (not (Array.null tail)) $ void $ AVar.tryPut unit q.signal
      pure head
