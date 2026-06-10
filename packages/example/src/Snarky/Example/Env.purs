-- | One-time initialization for the example app: build the Pasta SRSes and
-- | compile the transaction-snark program ONCE, then hand the resulting `Env`
-- | to every subsystem (tests, the snark manager, ...). Compiling is expensive
-- | — nothing downstream should ever call `compileTxCircuit` itself.
-- |
-- | The one deliberate exception is the snark worker: it initializes itself
-- | from a `CompiledTx` (today the manager passes it the Env's), because the
-- | whole point of the worker boundary is that it will eventually be
-- | externalized — a remote worker compiles its own.
module Snarky.Example.Env where

import Prelude

import Data.Array (range)
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
import Snarky.Example.Transaction.Checked (CompiledTx, compileTxCircuit)

type Config =
  { pallasSrs :: CRS PallasG
  , vestaSrs :: CRS VestaG
  , chainId :: ChainId
  }

-- | Build the Pasta SRSes with the lagrange-basis caches pre-warmed for the
-- | step (Vesta, 2^9..2^16) and wrap (Pallas, 2^12..2^15) domains the program
-- | touches. Mirrors `Test.Pickles.SharedSrs.buildSharedSrs`; the wrap depth
-- | (2^15) is the OCaml Tock URS convention.
mkConfig
  :: ChainId
  -> Effect Config
mkConfig chainId = do
  let pallasSrs = PallasImpl.pallasCrsCreate 32768
  vestaSrs <- createCRS @StepField
  for_ (range 9 16) (addLagrangeBasis vestaSrs)
  for_ (range 12 15) (addLagrangeBasis pallasSrs)
  pure { pallasSrs, vestaSrs, chainId }

type Env d =
  { chainId :: ChainId
  , compiledTx :: CompiledTx d
  , ledger :: Ref (Ledger d)
  }

mkEnv
  :: forall @d
   . Reflectable d Int
  => Config
  -> Effect (Env d)
mkEnv cfg = do
  ledger <- Ref.new $ Ledger.empty @d
  compiledTx <- compileTxCircuit cfg.chainId { pallasSrs: cfg.pallasSrs, vestaSrs: cfg.vestaSrs }
  pure { ledger, compiledTx, chainId: cfg.chainId }
