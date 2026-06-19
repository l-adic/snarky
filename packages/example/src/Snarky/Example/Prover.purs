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
import Data.Newtype (un)
import Data.Reflectable (class Reflectable, reifyType)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Mina.ChainId (chainIdFromTag)
import Pickles.Prove.SerializeProof (encodeCompiledProof)
import Snarky.Example.Env (mkConfig, mkEnv)
import Snarky.Example.Log (Logger)
import Snarky.Example.Log as Log
import Snarky.Example.P2P.Types (Payload(..))
import Snarky.Example.Snark.Work (WorkItem, decodeWorkItem)
import Snarky.Example.Snark.Worker (proveItem)
import Snarky.Example.Srs.Cache (SrsCache)
import Type.Proxy (Proxy)

-- | Build the SRS + compile the circuit for the given chain + depth, returning
-- | a closure that proves one encoded `WorkItem` and returns the encoded proof.
-- | The closure captures the compiled program + the SRS, so the (expensive)
-- | setup happens once. The `Logger` carries the SRS-build / circuit-compile
-- | progress to the worker (`mkEnv` logs the compile through it too).
buildProver :: SrsCache -> Logger -> { chain :: String, depth :: Int } -> Aff (Payload -> Effect Payload)
buildProver cache logger { chain, depth } = reifyType depth (buildProverAt cache logger chain)

buildProverAt :: forall d. Reflectable d Int => SrsCache -> Logger -> String -> Proxy d -> Aff (Payload -> Effect Payload)
buildProverAt cache logger chain _ = do
  Log.logInfo logger "building SRS…"
  config <- mkConfig cache (chainIdFromTag chain)
  Log.logInfo logger "SRS ready — compiling the transaction circuit…"
  env <- liftEffect $ mkEnv @d logger config
  Log.logInfo logger "circuit compiled"
  pure \encoded -> case decodeWorkItem env (un Payload encoded) :: Either _ (WorkItem d) of
    Left err -> throw ("prover: decodeWorkItem failed: " <> show err)
    Right item -> (Payload <<< encodeCompiledProof) <$> proveItem env.compiledTx item
