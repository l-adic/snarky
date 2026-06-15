-- | A pool of discrete workers behind a swappable backend. The pool is the
-- | drop-in for a single worker loop: it speaks the same `{ next, post }`
-- | protocol (`Snarky.Example.Snark.Worker`), so the producer/consumer don't
-- | change — only the number of workers and where they run.
-- |
-- | A `WorkerBackend` is "how to spawn one discrete worker": today
-- | `localBackend` (in-process — no real parallelism, since the prover is
-- | synchronous, but it exercises the plumbing), later a web worker, a node
-- | worker thread, or a p2p peer. Each is just a different `WorkerBackend`
-- | value injected at `runPool`.
module Snarky.Example.Snark.Pool
  ( Worker
  , WorkerBackend
  , localBackend
  , runPool
  ) where

import Prelude

import Control.Monad.Rec.Class (forever)
import Control.Parallel (parTraverse)
import Data.Array (range)
import Data.Foldable (for_)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff, finally, forkAff)
import Effect.Class (liftEffect)
import Fmt (fmt)
import Snarky.Example.AsyncQueue (dequeue, enqueue, newQueue)
import Snarky.Example.Log (Logger)
import Snarky.Example.Log as Log

-- | A discrete worker: runs ONE job at a time, in true parallel with its
-- | siblings. `run`'s `Aff` blocks until THIS worker finishes the job. `id`
-- | identifies the worker in dispatch logs — for a real backend it should match
-- | whatever the worker labels its own logs with (e.g. its OS thread id), so
-- | the two log streams can be correlated.
type Worker job result =
  { id :: String
  , run :: job -> Aff result
  , terminate :: Effect Unit
  }

-- | How to spawn a worker on a given backend (in-process, web worker, node
-- | thread, p2p peer — each is a value of this type). `name` is for logging.
type WorkerBackend job result =
  { name :: String
  , spawn :: Aff (Worker job result)
  }

-- | In-process backend: each worker just runs the `Effect` processor. No real
-- | parallelism (the processor is synchronous), but it validates the pool with
-- | zero worker infrastructure and keeps the demo working.
localBackend :: forall job result. (job -> Effect result) -> WorkerBackend job result
localBackend process =
  { name: "in-process"
  , spawn: pure { id: "in-process", run: \job -> liftEffect (process job), terminate: pure unit }
  }

-- | Spawn `size` workers and drive them over a `{ next, post }` work
-- | source/sink — the same protocol a single worker loop uses, so this is a
-- | drop-in replacement. One dispatcher fiber pulls the next job and a free
-- | worker (blocking when all are busy — natural backpressure), then forks the
-- | job so it keeps pulling; the forked fiber posts the result and returns the
-- | worker. So `next` and the free queue have a single consumer (the
-- | dispatcher) while results and freed workers have many producers — the
-- | channel discipline `AsyncQueue` requires.
-- |
-- | Workers are spawned concurrently (`parTraverse`), so a backend whose
-- | `spawn` does expensive warmup — e.g. a worker thread building its own SRS
-- | and compiling the circuit before it reports ready — pays that cost once in
-- | parallel rather than `size`× serially. No work is dispatched until every
-- | worker is ready.
-- | `describe` renders a job (from its routing `id` and the work itself) for
-- | the per-dispatch log that records which worker picked it up.
runPool
  :: forall id job result
   . Logger
  -> Int
  -> WorkerBackend job result
  -> { next :: Aff (Tuple id job)
     , post :: Tuple id result -> Aff Unit
     , describe :: id -> job -> String
     }
  -> Aff Unit
runPool logger size backend io = do
  free <- newQueue
  Log.logInfo logger $ fmt @"[Worker Pool] warming up {size} {name} worker(s)…"
    { size, name: backend.name }
  workers <- parTraverse (\_ -> backend.spawn) (range 1 size)
  for_ workers (enqueue free)
  Log.logInfo logger $ fmt @"[Worker Pool] ready: {size} {name} worker(s)"
    { size, name: backend.name }
  forever do
    Tuple id job <- io.next
    worker <- dequeue free
    Log.logInfo logger $ fmt @"[Worker Pool] {what} → worker {w}"
      { what: io.describe id job, w: worker.id }
    forkAff $ finally (enqueue free worker) do
      result <- worker.run job
      io.post (Tuple id result)
