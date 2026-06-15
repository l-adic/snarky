-- | The node worker-thread entry point for snark proving — the parallel
-- | counterpart of `Snarky.Example.Snark.Worker.localSnarkBackend`. Spawned by
-- | `Snarky.Example.Terminal.NodeBackend` (via `worker-entry.mjs`) and driven
-- | over `worker_threads` message passing.
-- |
-- | Each worker does its OWN one-time setup — build the Pasta SRSes and compile
-- | the transaction-snark program — then loops: decode a `WorkItem`, prove it,
-- | and reply with the encoded `CompiledProof`. There is no proving key to
-- | ship; proving is just a function, so a worker compiles its own program
-- | rather than receiving one from the host. The only thing the host hands over
-- | is the chain id (as `workerData`), so the worker compiles the same circuit.
module Snarky.Example.Terminal.SnarkWorker
  ( main
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Int as Int
import Data.Maybe (fromMaybe)
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Random (random)
import Mina.ChainId (ChainId(..))
import Node.Process (lookupEnv)
import Node.WorkerBees (ThreadId(..), WorkerContext, makeAsMain)
import Pickles.Prove.SerializeProof (encodeCompiledProof, mkWidthDummies)
import Snarky.Example.Env (mkConfig, mkEnv)
import Snarky.Example.Log as Log
import Snarky.Example.Snark.Work (WorkItem(..), decodeWorkItem)
import Snarky.Example.Snark.Worker (proveItem)
import Snarky.Example.Terminal.WorkerLog (workerLogger)

foreign import sleepSync :: Int -> Effect Unit

-- | Ledger tree depth — MUST match `Snarky.Example.Main`'s `Depth`. The host
-- | and worker compile the same circuit and exchange `Mask`/proof encodings
-- | sized by it; a mismatch would silently corrupt the wire format.
type Depth = 4

-- | Decode the chain-id tag the host sends as `workerData` (the inverse of
-- | `Snarky.Example.Terminal.NodeBackend`'s tag). Anything other than the
-- | mainnet tag is treated as testnet (the example's default).
chainIdFromTag :: String -> ChainId
chainIdFromTag = case _ of
  "mainnet" -> Mainnet
  _ -> Testnet

-- | Which kind of work a job is, for the lifecycle logs.
describeJob :: forall d. WorkItem d -> String
describeJob = case _ of
  Base _ -> "base"
  Merge _ -> "merge"

-- | Fault-injection knobs for exercising the pool's reliability paths, read once
-- | from the environment. Both probabilities are fractions in [0, 1]:
-- |
-- |   * timeout + reassignment: with probability `SNARK_WORKER_DELAY_PCT`%
-- |     (default 50) a job is stalled for `SNARK_WORKER_DELAY_MS` ms (default 0
-- |     = off) before proving, so the host's `run` overruns the pool's timeout.
-- |   * death + replacement: with probability `SNARK_WORKER_CRASH_PCT`%
-- |     (default 0 = off) the worker throws on a job, killing its thread, so the
-- |     pool's `run` errors → the worker is terminated, replaced, and the job
-- |     reassigned.
type Fault = { delayMs :: Int, delayPct :: Number, crashPct :: Number }

readFault :: Effect Fault
readFault = do
  delayMs <- intEnv "SNARK_WORKER_DELAY_MS" 0
  delayPct <- intEnv "SNARK_WORKER_DELAY_PCT" 50
  crashPct <- intEnv "SNARK_WORKER_CRASH_PCT" 0
  pure { delayMs, delayPct: pctFraction delayPct, crashPct: pctFraction crashPct }
  where
  intEnv name def = lookupEnv name <#> \mv -> fromMaybe def (Int.fromString =<< mv)
  pctFraction n = Int.toNumber n / 100.0

-- | One worker: build the SRS + lagrange basis + compile the circuit once,
-- | logging each phase to the shared worker-log file (NOT the host console,
-- | which has a progress tree pinned to it), announce readiness, then prove
-- | every `WorkItem` that arrives.
-- |
-- | The only message a worker sends before proving is the bare `ready` sentinel
-- | — its warmup logs go to `Snarky.Example.Terminal.WorkerLog.workerLogPath`,
-- | keeping the work-message channel free of log traffic. Every message after
-- | the sentinel is one encoded proof.
worker :: WorkerContext String String String -> Effect Unit
worker ctx = do
  let
    ThreadId tid = ctx.threadId
    note text = Log.logInfo workerLogger ("[worker " <> show tid <> "] " <> text)
  fault <- readFault
  note "building SRS + lagrange basis…"
  config <- mkConfig (chainIdFromTag ctx.workerData)
  note "compiling circuit…"
  env <- mkEnv @Depth mempty config
  let dummies = mkWidthDummies env.pallasSrs env.vestaSrs
  note "ready"
  ctx.reply "ready"
  ctx.receive \encoded ->
    case decodeWorkItem dummies encoded :: Either _ (WorkItem Depth) of
      Left err -> throw ("snark worker: decodeWorkItem failed: " <> show err)
      Right item -> do
        let kind = describeJob item
        -- Fault injection (no-ops unless the env knobs are set): crash this
        -- worker to exercise reclaim's death/replace path, or stall before
        -- proving to exercise the pool's timeout + reassignment.
        when (fault.crashPct > 0.0) do
          roll <- random
          when (roll < fault.crashPct) do
            note ("FAULT-INJECT crashing on " <> kind <> " job")
            throw "fault-inject: simulated worker crash"
        when (fault.delayMs > 0) do
          roll <- random
          when (roll < fault.delayPct) do
            note ("FAULT-INJECT stalling " <> show fault.delayMs <> "ms before " <> kind <> " job")
            sleepSync fault.delayMs
        note ("starting job (" <> kind <> ")")
        proof <- proveItem env.compiledTx item
        note ("submitting work (" <> kind <> ")")
        ctx.reply (encodeCompiledProof proof)

main :: Effect Unit
main = makeAsMain worker
