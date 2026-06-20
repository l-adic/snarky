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

import Data.Maybe (Maybe)
import Data.Reflectable (class Reflectable)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Mina.ChainId (ChainId)
import Snarky.Backend.Kimchi.Impl.Pallas as P
import Snarky.Backend.Kimchi.Impl.Vesta as V
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Example.Ledger (Ledger)
import Snarky.Example.Ledger as Ledger
import Snarky.Example.Log (Logger)
import Snarky.Example.Log as Log
import Snarky.Example.Transaction.Checked (CompiledTx, compileTxCircuit)
import Snarky.Lagrange.Cache (LagrangeCache)

type Config =
  { pallasSrs :: CRS PallasG
  , vestaSrs :: CRS VestaG
  , chainId :: ChainId
  -- | Threaded to `compileTxCircuit` so compile warms exactly the domains the
  -- | transaction circuit commits over — no guessed domain list.
  , lagrangeCache :: Maybe LagrangeCache
  }

-- | The Pasta SRS depths (the only sizes this program uses). Single-sourced.
-- | Vesta = 2^16 (OCaml Tick URS), Pallas = 2^15 (Tock URS).
vestaSrsSize :: Int
vestaSrsSize = 65536

pallasSrsSize :: Int
pallasSrsSize = 32768

-- | Build the Pasta SRS *generators* directly (a cheap, deterministic
-- | hash-to-curve string) and carry `lagrangeCache` onto the `Config` for
-- | compile — only the expensive Lagrange bases are cached, lazily at compile.
-- | The chain plays no part. Pass `Nothing` for the un-cached path (bases
-- | kimchi-lazy, not persisted).
mkConfig
  :: Maybe LagrangeCache
  -> ChainId
  -> Aff Config
mkConfig lagrangeCache chainId = pure
  { pallasSrs: P.pallasCrsCreate pallasSrsSize
  , vestaSrs: V.vestaCrsCreate vestaSrsSize
  , chainId
  , lagrangeCache
  }

type Env d =
  { chainId :: ChainId
  , compiledTx :: CompiledTx d
  , ledger :: Ref (Ledger d)
  , logger :: Logger
  -- Carried for decoding transported proofs: `decodeCompiledProof` takes the
  -- SRSes directly (it builds the reconstruction dummies internally).
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
  compiledTx <- compileTxCircuit cfg.chainId cfg.lagrangeCache { pallasSrs: cfg.pallasSrs, vestaSrs: cfg.vestaSrs }
  Log.logDebug logger "Compiled TxCircuit"
  pure { ledger, compiledTx, chainId: cfg.chainId, logger, pallasSrs: cfg.pallasSrs, vestaSrs: cfg.vestaSrs }
