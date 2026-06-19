-- | Reliability tests for the worker pool (`Snarky.Example.Snark.Pool`),
-- | exercised entirely in-process — no transport, no proving, no browser. The
-- | pool is transport-agnostic (it speaks the abstract `WorkerBackend`/`Worker`
-- | interface), so we drive it with SCRIPTED async workers and assert its
-- | reliability contract directly:
-- |
-- |   * dispatch — every job is processed and its result posted exactly once;
-- |   * timeout → reassign — a worker that overruns the job timeout has its job
-- |     handed to another worker, and the slow original's late result is dropped
-- |     (at-most-once);
-- |   * dead worker — a worker whose `run` errors is terminated, its job
-- |     reassigned, and (Fixed) a replacement is spawned to hold the pool size;
-- |   * Dynamic growth — work submitted before any worker exists queues, and is
-- |     drained as workers join late (the p2p coordinator's membership model).
-- |
-- | Each worker is just a `{ id, run, terminate }` value whose `run :: Int -> Aff
-- | String` returns the worker's own id (so a posted result tells us which worker
-- | produced it). Behaviours: instant, slow (delay past the timeout), or dead
-- | (`run` throws). Timeouts are tens of milliseconds so the suite stays fast.
module Test.Snarky.Example.Snark.PoolSpec
  ( spec
  ) where

import Prelude

import Colog (LogAction(..))
import Data.Array as Array
import Data.Foldable (for_)
import Data.Time.Duration (Milliseconds(..))
import Data.Tuple (Tuple(..), fst, snd)
import Effect (Effect)
import Effect.Aff (Aff, delay, error, forkAff, killFiber)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Snarky.Example.AsyncQueue (Queue, dequeue, enqueue, newQueue)
import Snarky.Example.Log (Logger)
import Snarky.Example.Snark.Pool (PoolSize(..), Worker, WorkerBackend, runPool)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | A test worker: `run` ignores the job and returns the worker's id; behaviour
-- | is fixed by the constructor below. `terminate` records the worker id into a
-- | shared log so we can assert which workers the pool dropped.
type TWorker = Worker Int String

-- | A worker that finishes its job immediately.
instantWorker :: Ref (Array String) -> String -> TWorker
instantWorker term wid =
  { id: wid, run: \_ -> pure wid, terminate: recordTerm term wid }

-- | A worker that takes `d` to finish — set `d` past the pool timeout to force a
-- | reassignment (the worker still eventually succeeds, so the pool must drop its
-- | late result).
slowWorker :: Ref (Array String) -> String -> Milliseconds -> TWorker
slowWorker term wid d =
  { id: wid, run: \_ -> delay d $> wid, terminate: recordTerm term wid }

-- | A worker whose `run` errors (a dead thread).
deadWorker :: Ref (Array String) -> String -> TWorker
deadWorker term wid =
  { id: wid, run: \_ -> liftEffect (throw (wid <> " died")), terminate: recordTerm term wid }

recordTerm :: Ref (Array String) -> String -> Effect Unit
recordTerm term wid = Ref.modify_ (\xs -> Array.snoc xs wid) term

-- | The pool needs a logger; tests don't want the noise.
silentLogger :: Logger
silentLogger = LogAction \_ -> pure unit

-- | Drive `runPool` to completion of a scenario and return the posted results.
-- |
-- | Submits `jobs` (id = payload) immediately, runs the pool with the given
-- | `timeout`/`size`, and feeds workers through `feed` (which controls join
-- | timing — all-at-once for `Fixed`, staggered for a `Dynamic` late-join test).
-- | Waits until `expected` results are posted (or a 4s watchdog trips), lets a
-- | further 400ms elapse so any dropped duplicate would have surfaced, then snaps
-- | the result list. Both the work source and the "done" signal are `AsyncQueue`s.
runScenario
  :: Milliseconds
  -> PoolSize
  -> Int
  -> Array Int
  -> (Queue TWorker -> Aff Unit)
  -> Aff (Array (Tuple Int String))
runScenario timeout size expected jobs feed = do
  workerSrc <- newQueue
  workSrc <- newQueue
  for_ jobs \j -> enqueue workSrc (Tuple j j)
  posts <- liftEffect (Ref.new [])
  done <- newQueue
  let
    backend :: WorkerBackend Int String
    backend = { name: "test", spawn: dequeue workerSrc }
    io =
      { next: dequeue workSrc
      , post: \t -> do
          n <- liftEffect (Ref.modify (\xs -> Array.snoc xs t) posts) <#> Array.length
          when (n >= expected) (enqueue done unit)
      , describe: \i _ -> "job " <> show i
      }
  poolFib <- forkAff (runPool silentLogger timeout size backend io)
  feed workerSrc
  watchdog <- forkAff (delay (Milliseconds 4000.0) *> enqueue done unit)
  _ <- dequeue done
  -- settle: give a slow original (reassigned away) time to finish and be dropped.
  delay (Milliseconds 400.0)
  killFiber (error "scenario end") watchdog
  killFiber (error "scenario end") poolFib
  liftEffect (Ref.read posts)

spec :: SpecT Aff Unit Aff Unit
spec = describe "Snark worker pool" do
  it "Fixed: processes every job and posts each result exactly once" do
    term <- liftEffect (Ref.new [])
    let ws = [ instantWorker term "w0", instantWorker term "w1" ]
    res <- runScenario (Milliseconds 200.0) (Fixed 2) 4 [ 0, 1, 2, 3 ] \src -> for_ ws (enqueue src)
    Array.length res `shouldEqual` 4
    Array.sort (map fst res) `shouldEqual` [ 0, 1, 2, 3 ]
    Array.all (\by -> by == "w0" || by == "w1") (map snd res) `shouldEqual` true

  it "Fixed: reassigns a timed-out job to a free worker, exactly once" do
    term <- liftEffect (Ref.new [])
    -- w0 (dispatched first) overruns the 80ms timeout; w1 takes the reassignment.
    let ws = [ slowWorker term "w0" (Milliseconds 250.0), instantWorker term "w1" ]
    res <- runScenario (Milliseconds 80.0) (Fixed 2) 1 [ 0 ] \src -> for_ ws (enqueue src)
    -- one post, by the reassignment winner; the slow original's result is dropped.
    Array.length res `shouldEqual` 1
    map snd res `shouldEqual` [ "w1" ]

  it "Fixed: drops a worker whose run errors, reassigns its job, and replaces it" do
    term <- liftEffect (Ref.new [])
    res <- runScenario (Milliseconds 200.0) (Fixed 2) 1 [ 0 ] \src -> do
      enqueue src (deadWorker term "w0") -- dies on its job
      enqueue src (instantWorker term "w1")
      enqueue src (instantWorker term "w2") -- the replacement Fixed spawns
    Array.length res `shouldEqual` 1
    -- produced by a live worker, not the dead one…
    Array.all (\by -> by == "w1" || by == "w2") (map snd res) `shouldEqual` true
    -- …and the dead worker was terminated.
    terminated <- liftEffect (Ref.read term)
    Array.elem "w0" terminated `shouldEqual` true

  it "Dynamic: queues work and drains it as workers join late" do
    term <- liftEffect (Ref.new [])
    res <- runScenario (Milliseconds 500.0) Dynamic 3 [ 0, 1, 2 ] \src -> do
      -- the 3 jobs are already queued; no worker exists yet — they join late.
      delay (Milliseconds 60.0)
      enqueue src (instantWorker term "w0")
      delay (Milliseconds 60.0)
      enqueue src (instantWorker term "w1")
    Array.length res `shouldEqual` 3
    Array.sort (map fst res) `shouldEqual` [ 0, 1, 2 ]
