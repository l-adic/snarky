-- | Export a four-transaction proof tree using two WorkerBees threads.
module Example.FixtureDump (main) where

import Prelude

import Control.Parallel (parTraverse)
import Data.Either (either)
import Data.Maybe (Maybe(..))
import Data.MerkleTree.Sparse as Sparse
import Data.MerkleTree.Sparse.Mask (fromSubset)
import Effect (Effect)
import Effect.Aff (bracket, launchAff_)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Exception (throw)
import Example.FixtureDump.Application (Depth, compileFixture)
import Example.FixtureDump.Cache as Cache
import Example.FixtureDump.Worker (Reply, Request, WorkerData)
import Mina.ChainId (ChainId(..))
import Node.Encoding (Encoding(..))
import Node.FS.Perms (permsAll)
import Node.FS.Sync as FS
import Node.Path (resolve)
import Node.Process (lookupEnv)
import Node.WorkerBees (Worker, unsafeWorkerFromPath)
import Node.WorkerBees.Aff.Pool as Pool
import Pickles (toVerifiable, verifyBatch)
import Pickles.Prove.SerializeProof (decodeCompiledProof)
import Pickles.Types (ApplicationStatement(..))
import Pickles.Verify (CompiledProof(..))
import Random.LCG (mkSeed)
import Simple.JSON as JSON
import Snarky.Example.Ledger (Ledger)
import Snarky.Example.Simulation.Genesis (genGenesisLedger)
import Snarky.Example.Simulation.Transaction (genValidSignedTransaction)
import Snarky.Example.Snark.Work (BaseJob, Proof, WorkItem(..), encodeWorkItem)
import Snarky.Example.Transaction (Statement(..), applyTx, touchedAccounts)
import Test.QuickCheck.Gen (Gen, evalGen)

sample :: forall a. Int -> Gen a -> a
sample seed gen = evalGen gen { newSeed: mkSeed seed, size: 10 }

requiredEnv :: String -> Effect String
requiredEnv name = lookupEnv name >>= case _ of
  Just value | value /= "" -> resolve [] value
  _ -> throw (name <> " must name the fixture output directory")

worker :: Worker WorkerData Request Reply
worker = unsafeWorkerFromPath "./packages/example/bin/worker-entry.mjs"

merge :: Proof -> Proof -> Effect (WorkItem Depth)
merge proof1@(CompiledProof left) proof2@(CompiledProof right) = do
  let
    ApplicationStatement { input: Statement l } = left.statement
    ApplicationStatement { input: Statement r } = right.statement
  unless (l.target == r.source) (throw "fixture transitions do not connect")
  pure $ Merge
    { proof1, proof2, statement: Statement { source: l.source, target: r.target } }

main :: Effect Unit
main = launchAff_ do
  dumpDir <- liftEffect $ requiredEnv "PICKLES_DUMP_DIR"
  cacheDir <- liftEffect $ requiredEnv "PICKLES_PROOF_CACHE_DIR"
  let cachePath = cacheDir <> "/ExampleTransaction.json"
  liftEffect $ FS.mkdir' cacheDir { recursive: true, mode: permsAll }
  bracket
    (liftEffect $ FS.mkdtemp (cacheDir <> "/.example-workers-"))
    ( \directory -> liftEffect $ FS.rm' directory
        { force: true, recursive: true, maxRetries: 0, retryDelay: 100 }
    )
    \directory -> do
      let compileCache = directory <> "/compile.json"
      liftEffect $ log "[ExampleTransaction] compiling base, merge and wrap circuits"
      app <- liftEffect $ compileFixture
        (Just (dumpDir <> "/ExampleTransaction/transaction.json"))
        compileCache
      let
        genesis = sample 430 (genGenesisLedger 10)

        prepare :: Int -> Ledger Depth -> Effect { ledger :: Ledger Depth, job :: BaseJob Depth }
        prepare seed ledger = do
          let tx = sample seed (genValidSignedTransaction Testnet ledger genesis.keys)
          next <- applyTx Testnet tx ledger
          pure
            { ledger: next
            , job:
                { tx
                , mask: fromSubset ledger.tree (touchedAccounts ledger tx)
                , statement: Statement { source: Sparse.root ledger.tree, target: Sparse.root next.tree }
                }
            }
      t0 <- liftEffect $ prepare 431 genesis.ledger
      t1 <- liftEffect $ prepare 432 t0.ledger
      t2 <- liftEffect $ prepare 433 t1.ledger
      t3 <- liftEffect $ prepare 434 t2.ledger
      results <- Pool.withPool worker { directory, seed: cachePath } 2 \pool -> do
        let
          submit name item = do
            reply <- Pool.invoke pool { name, work: encodeWorkItem item }
            liftEffect do
              proof <- either (throw <<< show) pure (decodeCompiledProof app.srs reply.proof)
              cache <- either (throw <<< show) pure (JSON.readJSON reply.cache)
              pure { proof, cache }
        bases <- parTraverse (\{ name, job } -> submit name (Base job))
          [ { name: "base 0", job: t0.job }
          , { name: "base 1", job: t1.job }
          , { name: "base 2", job: t2.job }
          , { name: "base 3", job: t3.job }
          ]
        case bases of
          [ b0, b1, b2, b3 ] -> do
            j01 <- liftEffect $ merge b0.proof b1.proof
            j23 <- liftEffect $ merge b2.proof b3.proof
            pairs <- parTraverse (\{ name, job } -> submit name job)
              [ { name: "merge(0,1)", job: j01 }, { name: "merge(2,3)", job: j23 } ]
            case pairs of
              [ m01, m23 ] -> do
                rootJob <- liftEffect $ merge m01.proof m23.proof
                root <- submit "root merge" rootJob
                pure (bases <> pairs <> [ root ])
              _ -> liftEffect $ throw "expected two merge results"
          _ -> liftEffect $ throw "expected four base results"
      liftEffect do
        unless (verifyBatch app.compiled.verifier (map (_.proof >>> toVerifiable) results))
          (throw "transaction fixture proofs did not verify")
        store <- Cache.combine (map _.cache results)
        FS.writeTextFile UTF8 cachePath (JSON.writeJSON store)
        log "[ExampleTransaction] verified 4 transfers and 3 merges; fixtures written"
