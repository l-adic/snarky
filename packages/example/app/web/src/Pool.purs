-- | The browser worker-pool backend: the `SnarkBackend` twin of the node
-- | `nodeSnarkBackend`, over Web Workers. Each prover is a Web Worker
-- | (`prover-entry.js`) constructed by a JS factory (vite needs the literal
-- | `new Worker(new URL(...))`, so construction stays in JS and is injected
-- | here). The host posts an init record (chain id + depth + rayon thread
-- | count), the worker replies `ready`, then it's post-a-job / await-a-proof —
-- | the same string codecs the node pool uses.
-- |
-- | `runSimulationPool` wires this into the shared `Engine.runWith`, so the
-- | browser coordinator drives the SAME one-block pipeline as everything else,
-- | just with N prover workers instead of an in-process prover.
module Snarky.Example.Web.Pool
  ( runSimulationPool
  ) where

import Prelude

import Colog (Msg(..), Severity(..), unLogAction)
import Data.Either (Either(..))
import Data.Reflectable (class Reflectable, reflectType)
import Data.Time.Duration (Milliseconds(..))
import Effect (Effect)
import Effect.AVar as EffectAVar
import Effect.Aff.AVar as AVar
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Foreign (unsafeFromForeign, unsafeToForeign)
import Pickles.Prove.SerializeProof (decodeCompiledProof)
import Snarky.Example.Engine (EngineCallbacks, runWith)
import Snarky.Example.Snark.Work (encodeWorkItem)
import Snarky.Example.Snark.Worker (SnarkBackend)
import Type.Proxy (Proxy(..))
import Web.Worker.MessageEvent (data_)
import Web.Worker.Worker as WW

-- | The host's view of a prover reply: a tag plus a string payload
-- | (`ready` carries none, `proof`/`error` carry one).
type Reply = { tag :: String, value :: String }

foreign import hardwareConcurrency :: Effect Int

-- | A `SnarkBackend` whose workers are Web Workers built by `spawnWorker`. Each
-- | worker is told `threads` (its rayon pool size). The host decodes proofs
-- | with the `Env`'s SRSes.
webWorkerSnarkBackend
  :: forall d
   . Reflectable d Int
  => Int
  -> Effect WW.Worker
  -> SnarkBackend d
webWorkerSnarkBackend threads spawnWorker env =
  { name: "web worker"
  , spawn: do
      worker <- liftEffect spawnWorker
      -- One reply slot per worker: the pool runs one job at a time per worker,
      -- so each posted message is answered by exactly one reply.
      reply <- liftEffect EffectAVar.empty
      -- A `log`-tagged message is the worker's progress note: forward it to the
      -- coordinator's logger (the UI). Everything else (`ready`/`proof`/`error`)
      -- is a reply for the waiting `spawn`/`run`.
      let
        onMsg ev =
          let
            r = unsafeFromForeign (data_ ev) :: Reply
          in
            if r.tag == "log" then unLogAction env.logger (Msg { severity: Info, text: "[prover] " <> r.value })
            else void $ EffectAVar.put (data_ ev) reply mempty
      liftEffect $ WW.onMessage onMsg worker
      liftEffect $ WW.onError
        (\_ -> void $ EffectAVar.put (unsafeToForeign errorReply) reply mempty)
        worker
      -- Tell the worker what to compile (chain id via the Show instance, the
      -- reified depth) and how many rayon threads to take, then wait for ready.
      liftEffect $ WW.postMessage
        { tag: "init", chain: show env.chainId, depth: reflectType (Proxy :: Proxy d), threads }
        worker
      _ <- AVar.take reply
      pure
        { id: "web-worker" -- Web Workers expose no stable id
        , run: \job -> do
            liftEffect $ WW.postMessage { tag: "job", value: encodeWorkItem job } worker
            r <- AVar.take reply
            let rec = unsafeFromForeign r :: Reply
            case rec.tag of
              "proof" -> case decodeCompiledProof env rec.value of
                Left err -> liftEffect $ throw ("decodeCompiledProof: " <> show err)
                Right proof -> pure proof
              _ -> liftEffect $ throw ("prover worker: " <> rec.value)
        , terminate: WW.terminate worker
        }
  }
  where
  errorReply = { tag: "error", value: "prover worker error event" } :: Reply

-- | Drive the shared engine over a pool of `poolSize` prover Web Workers built
-- | by `spawnWorker`. Each worker gets an even share of the cores (`cores /
-- | poolSize`) for rayon. A generous job timeout — browser proving is slow and a
-- | spurious reassignment would spawn another (memory-hungry) wasm instance.
runSimulationPool :: Int -> Effect WW.Worker -> EngineCallbacks -> Effect Unit
runSimulationPool poolSize spawnWorker cb = do
  cores <- hardwareConcurrency
  let threads = max 1 (cores / poolSize)
  runWith (webWorkerSnarkBackend threads spawnWorker) poolSize (Milliseconds 600000.0) cb
