-- | One-time initialization for the example app: build the Pasta SRSes and
-- | compile the transaction-snark program ONCE, then hand the resulting `Env`
-- | to every subsystem (tests, the snark manager, ...). Compiling is expensive
-- | — nothing downstream should ever call `compileTxCircuit` itself.
-- |
-- | The one deliberate exception is the snark worker: it initializes itself
-- | from a `CompiledTx` (today the manager passes it the Env's), because the
-- | whole point of the worker boundary is that it will eventually be
-- | externalized — a remote worker compiles its own.
-- |
-- | The `Env` also carries the application `Logger` (a plain colog
-- | `LogAction Effect Message`); log with the `Snarky.Example.Log` helpers
-- | from any `MonadEffect` context.
module Snarky.Example.Env where

import Prelude

import Data.Foldable (for_)
import Data.Reflectable (class Reflectable)
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Mina.ChainId (ChainId)
import Pickles (StepField)
import Snarky.Backend.Kimchi.Class (addLagrangeBasis, createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Example.Ledger (Ledger)
import Snarky.Example.Ledger as Ledger
import Snarky.Example.Log (Logger)
import Snarky.Example.Log as Log
import Snarky.Example.Transaction.Checked (CompiledTx, compileTxCircuit)

type Config =
  { pallasSrs :: CRS PallasG
  , vestaSrs :: CRS VestaG
  , chainId :: ChainId
  }

-- | Build the Pasta SRSes, pre-warming the lagrange-basis cache for
-- | exactly the domains this program commits over (measured by
-- | instrumenting the prover, not guessed):
-- |
-- |   * Vesta (step): 2^13 (base step) and 2^15 (merge step)
-- |   * Pallas (wrap): 2^14 (the `override_wrap_domain:N1`)
-- |
-- | These are circuit-determined, so stable across blocks. Warming a
-- | superset is merely wasted MSMs (the old code warmed Vesta 2^9..2^16
-- | + Pallas 2^12..2^15 — 12 domains for the 3 actually used); warming a
-- | subset just defers the missing basis to a one-time lazy generation
-- | at prove time (correct, slower). The Pallas SRS depth stays 2^15
-- | (the OCaml Tock URS convention) regardless of which bases are warmed.
mkConfig
  :: ChainId
  -> Effect Config
mkConfig chainId = do
  let pallasSrs = PallasImpl.pallasCrsCreate 32768
  vestaSrs <- createCRS @StepField
  for_ [ 13, 15 ] (addLagrangeBasis vestaSrs)
  for_ [ 14 ] (addLagrangeBasis pallasSrs)
  pure { pallasSrs, vestaSrs, chainId }

type Env d =
  { chainId :: ChainId
  , compiledTx :: CompiledTx d
  , ledger :: Ref (Ledger d)
  , logger :: Logger
  -- Carried for decoding transported proofs (the `WidthDummies` a worker
  -- needs to reconstruct a `CompiledProof` derive from these).
  , pallasSrs :: CRS PallasG
  , vestaSrs :: CRS VestaG
  }

mkEnv
  :: forall @d
   . Reflectable d Int
  => Logger
  -> Config
  -> Effect (Env d)
mkEnv logger cfg = do
  ledger <- Ref.new $ Ledger.empty @d
  Log.logDebug logger "Compiling TxCircuit..."
  compiledTx <- compileTxCircuit cfg.chainId { pallasSrs: cfg.pallasSrs, vestaSrs: cfg.vestaSrs }
  Log.logDebug logger "Compiled TxCircuit"
  pure { ledger, compiledTx, chainId: cfg.chainId, logger, pallasSrs: cfg.pallasSrs, vestaSrs: cfg.vestaSrs }
