-- | Driving the example node with synthetic traffic: a `Keystore` that can
-- | sign for every simulated account, genesis-ledger generation, and block
-- | generation (sequentially-valid random transfers).
-- |
-- | `Simulation` is the top-level bundle — everything a simulation run needs —
-- | and `mkSimulation` performs the whole one-time setup: build the SRSes,
-- | compile the transaction-snark program (via `mkEnv`, the single compile
-- | point), mint the genesis ledger into the env's ledger ref, and start the
-- | snark manager.
module Snarky.Example.Simulation
  ( Simulation
  , SimulationConfig
  , mkSimulation
  , module Snarky.Example.Simulation.Keystore
  , module Snarky.Example.Simulation.Genesis
  , module Snarky.Example.Simulation.Transaction
  , module Snarky.Example.Simulation.Block
  ) where

import Prelude

import Data.Maybe (Maybe)
import Data.Reflectable (class Reflectable)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Fmt (fmt)
import Mina.ChainId (ChainId)
import Snarky.Example.Env (Env, mkConfig, mkEnv)
import Snarky.Example.Log (Logger)
import Snarky.Example.Log as Log
import Snarky.Example.Simulation.Block (generateBlock)
import Snarky.Example.Simulation.Genesis (genGenesisLedger)
import Snarky.Example.Simulation.Keystore (Keystore, senderInfo)
import Snarky.Example.Simulation.Transaction (genDistinctPublicKeys, genOverdraftSignedTransaction, genValidSignedTransaction)
import Snarky.Example.Snark.Manager (Manager, OnProgress, mkManager)
import Test.QuickCheck.Gen (randomSampleOne)

-- | What a simulation run is configured by. `onProgress` optionally plugs a
-- | scan-state observer (e.g. the terminal display in
-- | `Snarky.Example.Snark.Progress`) into the snark manager.
type SimulationConfig d =
  { chainId :: ChainId
  , numAccounts :: Int
  , logger :: Logger
  , onProgress :: Maybe (OnProgress d)
  }

-- | Everything needed to run the simulation: the app `Env` (compiled program,
-- | current-ledger ref, logger), the genesis `Keystore` (to sign for every
-- | simulated account), and the running snark manager (to submit block work).
type Simulation d =
  { env :: Env d
  , keys :: Keystore
  , manager :: Manager d
  }

-- | One-time setup of a full simulation: SRS build + circuit compile (`mkEnv`),
-- | genesis ledger minted into the env's ledger ref, snark manager started.
mkSimulation
  :: forall @d
   . Reflectable d Int
  => SimulationConfig d
  -> Aff (Simulation d)
mkSimulation { chainId, numAccounts, logger, onProgress } = do
  Log.logInfo logger "[Simulation] building SRS + compiling the transaction snark…"
  config <- liftEffect $ mkConfig chainId
  env <- liftEffect $ mkEnv @d logger config
  Log.logInfo logger $ fmt @"[Simulation] minting genesis ledger of {numAccounts} accounts" { numAccounts }
  { ledger, keys } <- liftEffect $ randomSampleOne (genGenesisLedger numAccounts)
  liftEffect $ Ref.write ledger env.ledger
  manager <- mkManager { logger, onProgress } env.compiledTx
  pure { env, keys, manager }
