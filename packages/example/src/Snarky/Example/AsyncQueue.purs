-- | A minimal unbounded buffered async channel: non-blocking `enqueue`, blocking
-- | `dequeue`. Single-consumer (the dequeuer); any number of producers.
-- |
-- | Backed by a `Ref` buffer plus an `AVar` used as a "non-empty" signal: each
-- | `enqueue` appends and `tryPut`s the signal (idempotent if already raised);
-- | `dequeue` blocks on the signal, pops one item, and re-raises the signal if
-- | more remain.
-- |
-- | The same `AVar` is usable from both worlds (`Effect.AVar` / `Effect.Aff.AVar`
-- | are two views of one type), so the channel also offers `Effect`-flavoured
-- | construction + enqueue (`newQueueEffect` / `enqueueEffect`) — for a producer
-- | that lives in `Effect`, e.g. a DOM/transport message handler — while the
-- | consumer still `dequeue`s in `Aff`.
module Snarky.Example.AsyncQueue
  ( Queue
  , newQueue
  , newQueueEffect
  , enqueue
  , enqueueEffect
  , dequeue
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.AVar as EffectAVar
import Effect.Aff (Aff)
import Effect.Aff.AVar (AVar)
import Effect.Aff.AVar as AVar
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref

newtype Queue a = Queue { items :: Ref (Array a), signal :: AVar Unit }

newQueue :: forall a. Aff (Queue a)
newQueue = liftEffect newQueueEffect

-- | Construct a queue in `Effect` (the backing `Ref` + `AVar` are both `Effect`
-- | resources; the `Aff` `newQueue` just lifts this).
newQueueEffect :: forall a. Effect (Queue a)
newQueueEffect = do
  items <- Ref.new []
  signal <- EffectAVar.empty
  pure $ Queue { items, signal }

-- | Enqueue from `Effect` (for an `Effect`-bound producer). Same semantics as
-- | `enqueue`: append, then raise the non-empty signal.
enqueueEffect :: forall a. Queue a -> a -> Effect Unit
enqueueEffect (Queue q) x = do
  Ref.modify_ (\xs -> Array.snoc xs x) q.items
  void $ EffectAVar.tryPut unit q.signal

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
