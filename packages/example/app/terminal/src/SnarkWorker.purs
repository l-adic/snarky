-- | The node worker-thread entry point for snark proving — the parallel
-- | counterpart of `Snarky.Example.Snark.Worker.localSnarkBackend`. Spawned by
-- | `Snarky.Example.Terminal.NodeBackend` (via `worker-entry.mjs`) and driven
-- | over `worker_threads` message passing.
-- |
-- | Each worker does its OWN one-time setup — build the Pasta SRSes and compile
-- | the transaction-snark program — then loops: decode a `WorkItem`, prove it,
-- | and reply with the encoded `CompiledProof`. There is no proving key to
-- | ship; proving is just a function, so a worker compiles its own program
-- | rather than receiving one from the host. The host only hands over the
-- | `WorkerData` (chain id + ledger depth) so the worker compiles the same
-- | circuit — the depth is reified into a type, so this module hard-codes none.
module Snarky.Example.Terminal.SnarkWorker
  ( main
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Int as Int
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Reflectable (class Reflectable, reifyType)
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Exception (throw)
import Effect.Random (random)
import Mina.ChainId (ChainId(..))
import Node.Process (lookupEnv)
import Node.WorkerBees (ThreadId(..), WorkerContext, makeAsMain)
import Pickles.Prove.SerializeProof (encodeCompiledProof)
import Snarky.Example.Env (mkConfigCached, mkEnv)
import Snarky.Example.Log (Logger)
import Snarky.Example.Log as Log
import Snarky.Example.Snark.Work (WorkItem(..), decodeWorkItem)
import Snarky.Example.Snark.Worker (proveItem)
import Snarky.Example.Srs.Cache (SrsCache, entryKey)
import Snarky.Example.Srs.Cache.Fs (fsCache)
import Snarky.Example.Terminal.WorkerLog (workerLogger)
import Type.Proxy (Proxy)

foreign import sleepSync :: Int -> Effect Unit

-- | The on-disk SRS cache directory shared by all worker threads (and reused
-- | across runs); `SNARK_SRS_CACHE_DIR` overrides it.
foreign import resolveSrsCacheDir :: Effect String

-- | Wrap an `SrsCache` so every lookup logs HIT (loaded + injected, no FFT) or
-- | MISS (will build + store). Lives here in the app, not the cache manager, so
-- | the manager stays silent — the `{ get, put }` seam carries the observability.
loggingCache :: Logger -> SrsCache -> SrsCache
loggingCache logger inner = inner
  { get = \e -> do
      result <- inner.get e
      Log.logInfo logger $ case result of
        Just _ -> "[srs-cache] HIT  " <> entryKey e <> " (inject, no FFT)"
        Nothing -> "[srs-cache] MISS " <> entryKey e <> " (building + storing)"
      pure result
  }

-- | The init data the host sends as `workerData`: the chain id (as `Mina.ChainId`
-- | shows it) and the ledger depth, so the worker compiles the same circuit as
-- | the host — neither is hard-coded here.
type WorkerData = { chain :: String, depth :: Int }

-- | Inverse of `show :: ChainId -> String`. Anything but the mainnet tag is
-- | treated as testnet (the example's default).
chainIdFromTag :: String -> ChainId
chainIdFromTag = case _ of
  "Mainnet" -> Mainnet
  _ -> Testnet

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

main :: Effect Unit
main = makeAsMain worker

-- | Reify the host-supplied ledger depth into a type and run the worker at it,
-- | so this module never hard-codes a `Depth`.
worker :: WorkerContext WorkerData String String -> Effect Unit
worker ctx = reifyType ctx.workerData.depth (workerAtDepth ctx)

-- | One worker at a concrete depth (reified into `d`): build the SRS + lagrange
-- | basis + compile the circuit once, logging each phase to the shared
-- | worker-log file (NOT the host console, which has a progress tree pinned to
-- | it), announce readiness, then prove every `WorkItem` that arrives. Its only
-- | pre-proving message is the bare `ready` sentinel; every later message is one
-- | encoded proof. The `Proxy d` is just the reify witness — `d` is used via
-- | `mkEnv @d`.
workerAtDepth :: forall d. Reflectable d Int => WorkerContext WorkerData String String -> Proxy d -> Effect Unit
workerAtDepth ctx _ = launchAff_ do
  let
    ThreadId tid = ctx.threadId

    note :: forall m. MonadEffect m => String -> m Unit
    note text = Log.logInfo workerLogger ("[worker " <> show tid <> "] " <> text)
  fault <- liftEffect readFault
  cacheDir <- liftEffect resolveSrsCacheDir
  note "building SRS + lagrange basis…"
  -- Build the SRS through the shared on-disk cache: a cold cache runs the
  -- Lagrange-basis FFTs once (and stores them) for the whole worker pool; a warm
  -- one (a later worker, or a later run) loads + injects them, no FFT.
  config <- mkConfigCached (loggingCache workerLogger (fsCache cacheDir)) (chainIdFromTag ctx.workerData.chain)
  note "compiling circuit…"
  env <- liftEffect $ mkEnv @d mempty config
  note "ready"
  liftEffect $ ctx.reply "ready"
  liftEffect $ ctx.receive \encoded ->
    case decodeWorkItem env encoded :: Either _ (WorkItem d) of -- d = the reified depth
      Left err -> throw ("snark worker: decodeWorkItem failed: " <> show err)
      Right item -> do
        let
          kind = case item of
            Base _ -> "base"
            Merge _ -> "merge"
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
