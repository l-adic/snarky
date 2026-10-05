module Example.FixtureDump.Worker (main, WorkerData, Request, Reply) where

import Prelude

import Data.Either (either)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)
import Effect.Exception (throw)
import Example.FixtureDump.Application (Depth, compileFixture)
import Example.FixtureDump.Cache (proofEntries, readStore)
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Node.WorkerBees (ThreadId(..), makeAsMain)
import Pickles.Prove.SerializeProof (encodeCompiledProof)
import Simple.JSON as JSON
import Snarky.Example.Snark.Work (WorkItem, decodeWorkItem)
import Snarky.Example.Snark.Worker (proveItem)

type WorkerData = { directory :: String, seed :: String }
type Request = { name :: String, work :: String }
type Reply = { proof :: String, cache :: String }

main :: Effect Unit
main = makeAsMain \ctx -> do
  let
    ThreadId tid = ctx.threadId
    path = ctx.workerData.directory <> "/worker-" <> show tid <> ".json"
  seed <- readStore ctx.workerData.seed
  FS.writeTextFile UTF8 path (JSON.writeJSON seed)
  app <- compileFixture Nothing path
  ctx.receive \request -> do
    log ("[ExampleTransaction worker " <> show tid <> "] " <> request.name)
    item <-
      either (throw <<< show) pure (decodeWorkItem app.srs request.work)
        :: Effect (WorkItem Depth)
    proof <- proveItem app.compiled item
    cache <- proofEntries path proof
    ctx.reply { proof: encodeCompiledProof proof, cache: JSON.writeJSON cache }
