-- | The parallel snark backend: real `worker_threads` workers behind the same
-- | `Snarky.Example.Snark.Worker.SnarkBackend` interface the in-process
-- | `localSnarkBackend` implements. Injecting this into `mkManager`/
-- | `mkSimulation` (instead of `localSnarkBackend`) makes `poolSize` a true
-- | parallelism knob: each base/merge job runs on its own OS thread.
-- |
-- | Each worker (`Snarky.Example.Terminal.SnarkWorker`) compiles its own copy
-- | of the program — proving is just a function, so there is nothing to ship
-- | but the chain id. The host only encodes work items out and decodes proofs
-- | back, which is why this needs the `Env`'s SRSes (for the proof codec's
-- | `WidthDummies`).
module Snarky.Example.Terminal.NodeBackend
  ( nodeSnarkBackend
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Tuple (Tuple(..))
import Effect.Aff.AVar as AVar
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Mina.ChainId (ChainId(..))
import Node.WorkerBees (ThreadId(..), Worker, unsafeWorkerFromPath)
import Node.WorkerBees as WB
import Node.WorkerBees.Aff as WBAff
import Pickles.Prove.SerializeProof (decodeCompiledProof, mkWidthDummies)
import Snarky.Example.Snark.Work (encodeWorkItem)
import Snarky.Example.Snark.Worker (SnarkBackend)

-- | The bundled worker entry, spawned once per worker. The path must be
-- | absolute or `./`-relative to the process cwd (a `worker_threads` rule); the
-- | simulation runs from the repo root (see `tools/run_simulation.sh`), so this
-- | resolves there. `worker-entry.mjs` runs `SnarkWorker.main` in the thread.
workerRef :: Worker String String String
workerRef = unsafeWorkerFromPath "./packages/example/app/terminal/worker-entry.mjs"

-- | The chain id the worker should compile its circuit for, sent as
-- | `workerData` (decoded by `SnarkWorker.chainIdFromTag`).
chainTag :: ChainId -> String
chainTag = case _ of
  Mainnet -> "mainnet"
  Testnet -> "testnet"

nodeSnarkBackend :: forall d. SnarkBackend d
nodeSnarkBackend env =
  { name: "node worker_thread"
  , spawn: do
      Tuple thread output <- WBAff.spawn workerRef (chainTag env.chainId)
      -- Wait for the worker's readiness signal (its single warmup message),
      -- sent once it has built its own SRS + lagrange basis and compiled the
      -- circuit — its setup logs go to the shared worker-log file, not here. So
      -- a worker is only handed back to the pool warm; its first job pays no
      -- init cost.
      _ <- AVar.take output
      -- Tag the worker with its OS thread id — the same id it stamps its own
      -- file logs with — so the host's dispatch log and the worker log line up.
      ThreadId tid <- liftEffect $ WB.threadId thread
      pure
        { id: show tid
        , run: \job -> do
            -- The pool runs one job per worker at a time, so the single reply
            -- AVar holds exactly this job's result.
            WBAff.post (encodeWorkItem job) thread
            res <- AVar.take output
            case res of
              Left code ->
                liftEffect $ throw ("snark worker exited (code " <> show code <> ")")
              Right encoded -> case decodeCompiledProof dummies encoded of
                Left err ->
                  liftEffect $ throw ("snark worker: decodeCompiledProof failed: " <> show err)
                Right proof -> pure proof
        , terminate: WB.terminate thread (const (pure unit))
        }
  }
  where
  dummies = mkWidthDummies env.pallasSrs env.vestaSrs
