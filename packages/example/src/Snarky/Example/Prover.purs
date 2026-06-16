-- | The transport-agnostic prover server: from the host-supplied chain id and
-- | ledger depth, compile a circuit once and return a per-job closure that
-- | decodes a `WorkItem`, proves it, and encodes the resulting proof — all as
-- | plain strings, so any worker runtime (node worker_threads, browser Web
-- | Workers) can drive it over its own message channel. The depth is reified
-- | into a type, so nothing here is hard-coded.
-- |
-- | This is the shared core of a prover worker; the node `SnarkWorker` and the
-- | browser `prover-entry.js` both ultimately do this, differing only in the
-- | transport that feeds it.
module Snarky.Example.Prover
  ( buildProver
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Reflectable (class Reflectable, reifyType)
import Effect (Effect)
import Effect.Exception (throw)
import Mina.ChainId (ChainId(..))
import Pickles.Prove.SerializeProof (encodeCompiledProof)
import Snarky.Example.Env (mkConfig, mkEnv)
import Snarky.Example.Log (Logger)
import Snarky.Example.Log as Log
import Snarky.Example.Snark.Work (WorkItem, decodeWorkItem)
import Snarky.Example.Snark.Worker (proveItem)
import Type.Proxy (Proxy)

-- | Inverse of `show :: ChainId -> String` (anything but mainnet is testnet).
chainIdFromTag :: String -> ChainId
chainIdFromTag = case _ of
  "Mainnet" -> Mainnet
  _ -> Testnet

-- | Build the SRS + compile the circuit for the given chain + depth, returning
-- | a closure that proves one encoded `WorkItem` and returns the encoded proof.
-- | The closure captures the compiled program + the SRS, so the (expensive)
-- | setup happens once. The `Logger` carries the SRS-build / circuit-compile
-- | progress to the worker (`mkEnv` logs the compile through it too).
buildProver :: Logger -> { chain :: String, depth :: Int } -> Effect (String -> Effect String)
buildProver logger { chain, depth } = reifyType depth (buildProverAt logger chain)

buildProverAt :: forall d. Reflectable d Int => Logger -> String -> Proxy d -> Effect (String -> Effect String)
buildProverAt logger chain _ = do
  Log.logInfo logger "building SRS…"
  config <- mkConfig (chainIdFromTag chain)
  Log.logInfo logger "SRS ready — compiling the transaction circuit…"
  env <- mkEnv @d logger config
  Log.logInfo logger "circuit compiled"
  pure \encoded -> case decodeWorkItem env encoded :: Either _ (WorkItem d) of
    Left err -> throw ("prover: decodeWorkItem failed: " <> show err)
    Right item -> encodeCompiledProof <$> proveItem env.compiledTx item
