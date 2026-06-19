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
-- |
-- | Reliability (timeout + reassignment) is part of the pool spec, not any one
-- | backend: if a worker does not return a job's result within `timeout`, the
-- | pool reassigns that job to another worker, and the slow one keeps going.
-- | Whichever finishes first wins; the loser's result is dropped. A worker
-- | whose `run` ERRORS (e.g. its thread died) is `terminate`d and replaced, so
-- | the pool holds its size. All of this is built on the bare `Worker`
-- | interface (`id`/`run`/`terminate`), so any backend gets it for free.
module Snarky.Example.Snark.Pool
  ( Worker
  , WorkerBackend
  , PoolSize(..)
  , localBackend
  , runPool
  ) where

import Prelude

import Control.Monad.Rec.Class (forever)
import Control.Parallel (parOneOf, parTraverse)
import Data.Array (range)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Time.Duration (Milliseconds)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff, delay, forkAff, joinFiber, try)
import Effect.Class (liftEffect)
import Effect.Exception (message)
import Effect.Ref as Ref
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

-- | How the pool is populated:
-- |   * `Fixed n` — spawn `n` workers up front (in parallel) and dispatch nothing
-- |     until all are ready; a worker that dies is replaced to hold the size.
-- |     Right for backends whose `spawn` returns promptly (in-process, node
-- |     threads), where you know the worker count.
-- |   * `Dynamic` — start dispatching immediately (jobs queue) and add each worker
-- |     as it joins (a forked loop that keeps calling `spawn`, which for such a
-- |     backend BLOCKS until a peer appears); a worker that dies just leaves. Right
-- |     for a membership that grows over time — the p2p coordinator, where peers
-- |     join an open session and a fixed count would be arbitrary.
data PoolSize
  = Fixed Int
  | Dynamic

-- | In-process backend: each worker just runs the `Effect` processor. No real
-- | parallelism (the processor is synchronous), but it validates the pool with
-- | zero worker infrastructure and keeps the demo working. (The timeout never
-- | fires here: a synchronous `run` blocks the one thread, so the timer can't
-- | even tick until it returns — there is nothing to reassign.)
localBackend :: forall job result. (job -> Effect result) -> WorkerBackend job result
localBackend process =
  { name: "in-process"
  , spawn: pure { id: "in-process", run: \job -> liftEffect (process job), terminate: pure unit }
  }

-- | Spawn `size` workers and drive them over a `{ next, post }` work
-- | source/sink — the same protocol a single worker loop uses, so this is a
-- | drop-in replacement.
-- |
-- | Channels and who touches them (the `AsyncQueue` single-consumer discipline):
-- |   * `io.next` (external work): drained by the FEEDER, which marks each job
-- |     "outstanding" (it now owes a result) and forwards it to `ready`.
-- |   * `ready`: the DISPATCHER's single input — external work from the feeder
-- |     plus internal REASSIGNMENTS (many producers, one consumer).
-- |   * `free`: idle workers — produced by completed jobs (many), consumed by
-- |     the dispatcher (one).
-- | The dispatcher pulls a job and a free worker (blocking when all are busy —
-- | natural backpressure) and forks an `attempt`.
-- |
-- | Workers are spawned concurrently (`parTraverse`), so a backend whose
-- | `spawn` does expensive warmup — e.g. a worker thread building its own SRS
-- | and compiling the circuit before it reports ready — pays that cost once in
-- | parallel rather than `size`× serially. No work is dispatched until every
-- | worker is ready.
-- |
-- | At-most-once delivery: a job is marked outstanding ONLY when it enters from
-- | outside (the feeder); a reassignment re-enters `ready` WITHOUT re-marking.
-- | Delivery clears the mark (first result wins via `claim`), and the dispatcher
-- | skips any reassignment whose job is no longer outstanding — so a job already
-- | finished by the original worker is never re-proved or re-`post`ed, even
-- | though the slow worker is left to finish. `describe` renders a job for the
-- | dispatch/timeout logs.
runPool
  :: forall id job result
   . Ord id
  => Logger
  -> Milliseconds
  -> PoolSize
  -> WorkerBackend job result
  -> { next :: Aff (Tuple id job)
     , post :: Tuple id result -> Aff Unit
     , describe :: id -> job -> String
     }
  -> Aff Unit
runPool logger timeout poolSize backend io = do
  free <- newQueue
  ready <- newQueue
  outstanding <- liftEffect $ Ref.new Set.empty
  case poolSize of
    Fixed size -> do
      Log.logInfo logger $ fmt @"[Worker Pool] warming up {size} {name} worker(s)…"
        { size, name: backend.name }
      workers <- parTraverse (\_ -> backend.spawn) (range 1 size)
      for_ workers (enqueue free)
      Log.logInfo logger $ fmt @"[Worker Pool] ready: {size} {name} worker(s)"
        { size, name: backend.name }
    Dynamic -> do
      Log.logInfo logger $ fmt @"[Worker Pool] open: {name} workers join dynamically"
        { name: backend.name }
      -- Each `spawn` blocks until the next peer joins; enqueue it and wait again.
      void $ forkAff $ forever do
        worker <- backend.spawn
        Log.logInfo logger $ fmt @"[Worker Pool] worker {w} joined" { w: worker.id }
        enqueue free worker

  let
    outstandingFor id = liftEffect $ Ref.read outstanding <#> Set.member id

    -- Deliver a result iff this is the first one for the job (the others — a
    -- slow original or a reassigned copy — are dropped). `claim` clears the
    -- outstanding mark and reports whether WE cleared it.
    deliver id result = do
      first <- liftEffect $ claim outstanding id
      when first $ io.post (Tuple id result)

    -- Return a worker to the pool, or — if its run errored (a dead thread) —
    -- terminate it. A FIXED pool spawns a replacement to hold its size; a DYNAMIC
    -- pool just drops it (the join loop is the only source of workers, so a dead
    -- one simply leaves until another peer joins).
    reclaim worker = case _ of
      Right _ -> enqueue free worker
      Left err -> do
        Log.logError logger $ fmt @"[Worker Pool] worker {w} died ({e})"
          { w: worker.id, e: message err }
        liftEffect worker.terminate
        case poolSize of
          Fixed _ -> do
            replacement <- backend.spawn
            enqueue free replacement
          Dynamic -> pure unit

    -- Run one job on one worker, bounded by `timeout`. The run is forked so the
    -- timer races only the WAIT on it — never killing the run itself, which
    -- would desync a backend's reply channel; we always re-join it to reclaim
    -- the worker.
    attempt id job worker = do
      fiber <- forkAff $ try (worker.run job)
      raced <- parOneOf [ delay timeout $> Nothing, map Just (joinFiber fiber) ]
      case raced of
        Just settled -> do
          reclaim worker settled
          case settled of
            Right result -> deliver id result
            -- Died before the timeout: nothing will come, so reassign now.
            Left _ -> enqueue ready (Tuple id job)
        Nothing -> do
          Log.logWarning logger $ fmt @"[Worker Pool] {what} timed out on worker {w} → reassigning"
            { what: io.describe id job, w: worker.id }
          enqueue ready (Tuple id job)
          void $ forkAff do
            settled <- joinFiber fiber
            reclaim worker settled
            case settled of
              -- The slow worker finished — it may still beat the reassigned
              -- copy; `deliver` keeps it at-most-once either way.
              Right result -> deliver id result
              Left _ -> pure unit

  -- Feeder: external work → mark outstanding → ready.
  void $ forkAff $ forever do
    Tuple id job <- io.next
    liftEffect $ Ref.modify_ (Set.insert id) outstanding
    enqueue ready (Tuple id job)

  -- Dispatcher: ready → a free worker → an attempt, skipping a reassignment
  -- whose job is already done (its original worker beat the reassignment here).
  forever do
    Tuple id job <- dequeue ready
    stillBefore <- outstandingFor id
    if not stillBefore then
      Log.logDebug logger $ fmt @"[Worker Pool] {what} already done; skipping reassignment"
        { what: io.describe id job }
    else do
      worker <- dequeue free
      -- The original may have delivered while we waited for a free worker;
      -- if so, return the worker rather than redundantly re-proving.
      stillAfter <- outstandingFor id
      if not stillAfter then do
        Log.logDebug logger $ fmt @"[Worker Pool] {what} finished while waiting; releasing worker {w}"
          { what: io.describe id job, w: worker.id }
        enqueue free worker
      else do
        Log.logInfo logger $ fmt @"[Worker Pool] {what} → worker {w}"
          { what: io.describe id job, w: worker.id }
        void $ forkAff $ attempt id job worker
  where
  -- | Clear a job's outstanding mark, reporting whether it was set (i.e. whether
  -- | this is the first result). A single synchronous read+write, so it is atomic
  -- | across the cooperatively-scheduled fibers that may race to deliver.
  claim ref id = Ref.modify' (\s -> { state: Set.delete id s, value: Set.member id s }) ref
