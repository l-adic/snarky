-- | The simulation entry point: build a `Simulation` (SRS + circuit compile,
-- | genesis ledger, snark manager), then drive one block through the full
-- | pipeline — generate random transfers, extract per-transaction snark work,
-- | farm it to the manager, and on a verified root proof adopt the new ledger.
-- |
-- | The scan-state progress display pins a live work tree to the bottom of
-- | the terminal (logs scroll above it).
module Snarky.Example.Main
  ( main
  ) where

import Prelude

import Colog (richMessageStdout)
import Data.Foldable (for_)
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Milliseconds(..))
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Fmt (fmt)
import Mina.ChainId (ChainId(..))
import Node.Process (exit', lookupEnv)
import Pickles (toVerifiable, verifyBatch)
import Snarky.Example.Block (Block(..), processBlock)
import Snarky.Example.Ledger (balanceOf)
import Snarky.Example.Log (Logger)
import Snarky.Example.Log as Log
import Snarky.Example.Simulation (generateBlock, mkSimulation)
import Snarky.Example.Snark.Manager (submitBlock)
import Snarky.Example.Snark.Pool (PoolSize(Fixed))
import Snarky.Example.Terminal.NodeBackend (nodeSnarkBackend)
import Snarky.Example.Terminal.ProgressDisplay (mkProgressDisplay)
import Snarky.Example.Terminal.WorkerLog (workerLogPath)
import Snarky.Example.Transaction (SignedTransaction(..), Transaction(..), Transfer(..))

-- | Ledger tree depth for the simulation (2^4 = 16 account slots).
type Depth = 4

-- | Worker-pool size when `SNARK_POOL_SIZE` is unset or invalid. An
-- | 8-transaction block has 8 base proofs available at once; 4 worker threads
-- | runs them in two waves, keeping peak memory ~halved versus one worker per
-- | leaf. Raise `SNARK_POOL_SIZE` toward 8 for more parallelism if memory allows.
defaultPoolSize :: Int
defaultPoolSize = 4

-- | Resolve the worker-pool size from `SNARK_POOL_SIZE` (a positive integer),
-- | falling back to `defaultPoolSize` — and warning — when unset or invalid.
resolvePoolSize :: Logger -> Effect Int
resolvePoolSize logger =
  lookupEnv "SNARK_POOL_SIZE" >>= case _ of
    Nothing -> pure defaultPoolSize
    Just s -> case Int.fromString s of
      Just n | n >= 1 -> pure n
      _ -> do
        Log.logWarning logger $
          fmt @"[Main] ignoring invalid SNARK_POOL_SIZE='{s}' (want a positive integer); using {d}"
            { s, d: defaultPoolSize }
        pure defaultPoolSize

-- | Per-job timeout (seconds) when `SNARK_JOB_TIMEOUT_S` is unset or invalid.
-- | A warm proof is ~30s, so the default leaves comfortable headroom before the
-- | pool speculatively reassigns a job to another worker.
defaultJobTimeoutS :: Int
defaultJobTimeoutS = 120

-- | Resolve the per-job timeout from `SNARK_JOB_TIMEOUT_S` (positive seconds),
-- | falling back to `defaultJobTimeoutS` — and warning — when unset or invalid.
resolveJobTimeout :: Logger -> Effect Milliseconds
resolveJobTimeout logger = do
  secs <- lookupEnv "SNARK_JOB_TIMEOUT_S" >>= case _ of
    Nothing -> pure defaultJobTimeoutS
    Just s -> case Int.fromString s of
      Just n | n >= 1 -> pure n
      _ -> do
        Log.logWarning logger $
          fmt @"[Main] ignoring invalid SNARK_JOB_TIMEOUT_S='{s}' (want positive seconds); using {d}"
            { s, d: defaultJobTimeoutS }
        pure defaultJobTimeoutS
  pure $ Milliseconds (Int.toNumber secs * 1000.0)

main :: Effect Unit
main = launchAff_ do
  display <- liftEffect mkProgressDisplay
  let logger = display.wrapLogger richMessageStdout
  poolSize <- liftEffect $ resolvePoolSize logger
  jobTimeout <- liftEffect $ resolveJobTimeout logger
  Log.logInfo logger $ fmt @"[Main] worker setup logs → {path} (tail it to watch warmup)"
    { path: workerLogPath }
  sim <- mkSimulation @Depth
    { chainId: Testnet
    , numAccounts: 10
    , logger
    , onProgress: Just display.reporter
    , poolSize: Fixed poolSize
    , jobTimeout
    , backend: nodeSnarkBackend
    }

  -- One block of random transfers against the current ledger.
  ledger0 <- liftEffect $ Ref.read sim.env.ledger
  block@(Block { transactions }) <- liftEffect $ generateBlock sim.env.chainId sim.keys ledger0
  for_ transactions \(SignedTransaction { transaction: Transaction { nonce, transfer: Transfer { from, to, amount } } }) ->
    Log.logInfo logger $ fmt
      @"[Main] tx (nonce {nonce}): {from} -> {to}, amount {amount}"
      { nonce: show nonce, from: show from, to: show to, amount: show (balanceOf amount) }

  -- Phase 1: the sequential witness-extraction fold; Phase 2: farm the work
  -- to the snark manager and await the block's root proof.
  { ledger: ledger1, snarkWork } <- liftEffect $ processBlock sim.env.chainId ledger0 block
  rootProof <- submitBlock sim.manager 0 snarkWork

  -- Accept the block: verify the root proof, then adopt the new ledger.
  if verifyBatch sim.env.compiledTx.verifier [ toVerifiable rootProof ] then do
    liftEffect $ Ref.write ledger1 sim.env.ledger
    Log.logInfo logger "[Main] root proof verified — block accepted, ledger advanced"
  else
    Log.logError logger "[Main] root proof FAILED to verify — block rejected"

  -- Persist the final frame of the progress display.
  liftEffect display.done

  -- Each worker thread keeps a `parentPort` receiver attached, which holds the
  -- node event loop open, so this one-shot demo exits explicitly once its
  -- single block is done. (The pool and manager are long-lived by design — a
  -- server processing many blocks would keep them, and the workers, running.)
  liftEffect $ exit' 0
