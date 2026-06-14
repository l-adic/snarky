-- | The per-peer prover service: the wasm-backed compute core that runs inside
-- | a Web Worker. It compiles the transaction-snark circuit once and then
-- | answers RPC requests issued by the main thread (which owns the WebRTC
-- | transport + gossip state machine). Pure compute — no network, no UI.
-- |
-- | Three operations, all over plain `String` wires (never witnesses):
-- |   * `seedBlock`  — BASE mode: generate a block, prove its base proofs
-- |                    locally (private inputs stay on-device), return the
-- |                    encoded leaves + leaf statements.
-- |   * `merge`      — given two child proof wires, verify both, merge them,
-- |                    return the parent {key, wire}. Trustless: a received
-- |                    proof is verified before it is merged on top of.
-- |   * `verifyWire` — verify an encoded proof (used for the root).
-- |
-- | The merge tree's structure/statements come from `Snarky.Example.Merge`
-- | (`decodeNode`, `encodeStmt`, `stmtKey`); the prove calls come from the
-- | compiled `Env` (`Snarky.Example.Env`). This is the externalized form of
-- | `Snark.Worker.proveItem`, with the in-memory `Proof` replaced by wires.
module Snarky.Example.P2P.ProverService
  ( ServiceState
  , LeafOut
  , SeedOut
  , BlockMeta
  , MergeOut
  , initService
  , fingerprint
  , seedBlock
  , genBlock
  , proveBaseLeaf
  , merge
  , verifyWire
  ) where

import Prelude

import Colog (LogAction(..), Message, Msg(..), Severity(..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Traversable (sequence)
import Effect (Effect)
import Effect.Aff (attempt, launchAff_)
import Effect.Class (liftEffect)
import Effect.Exception (message, throw)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Mina.ChainId (ChainId(..))
import Pickles (toVerifiable, verifyBatch)
import Pickles.Prove.SerializeProof (WidthDummies, toSerializableCompiledProof)
import Snarky.Example.Block (TxSnarkWork, processBlock)
import Snarky.Example.Env (Env, mkEnv)
import Snarky.Example.Merge (Depth, decodeNode, encodeStmt, mkWidthDummies, stmtKey)
import Snarky.Example.Simulation (generateBlock)
import Snarky.Example.Simulation.Genesis (genGenesisLedger)
import Snarky.Example.Snark.LeafCodec (encodeLeaf)
import Snarky.Example.SrsCache (buildCachedConfig)
import Snarky.Example.Transaction.Checked (Statement(..))
import Test.QuickCheck.Gen (randomSampleOne)

-- | Structured log line forwarded to the page (clean severity + text).
foreign import svcLog :: { severity :: String, text :: String } -> Effect Unit

severityLabel :: Severity -> String
severityLabel = case _ of
  Debug -> "debug"
  Info -> "info"
  Warning -> "warning"
  Error -> "error"

logger :: LogAction Effect Message
logger = LogAction \(Msg { severity, text }) -> svcLog { severity: severityLabel severity, text }

-- | The compiled circuit + a slot for the current block's base jobs (held here
-- | so base proofs can be proved one at a time without the private witnesses
-- | ever leaving the worker).
type ServiceState =
  { env :: Env Depth
  , dummies :: WidthDummies
  , jobs :: Ref (Array (TxSnarkWork Depth))
  }

-- | One produced base proof: its heap slot, its content-address key, its wire.
type LeafOut = { slot :: Int, key :: String, wire :: String }

-- | The block's public shape (no proofs): size + leaf statements.
type BlockMeta = { n :: Int, leafStmts :: Array { slot :: Int, stmt :: String } }

-- | The originator's seed: the block size, the encoded leaves, and the leaf
-- | statements (so merge peers can derive the whole slot→statement map).
type SeedOut =
  { n :: Int
  , leaves :: Array LeafOut
  , leafStmts :: Array { slot :: Int, stmt :: String }
  }

type MergeOut = { key :: String, wire :: String }

-- | Compile once. Callback style so the worker JS can wrap it in a promise.
initService :: (ServiceState -> Effect Unit) -> (String -> Effect Unit) -> Effect Unit
initService onReady onError = launchAff_ do
  res <- attempt do
    config <- buildCachedConfig Testnet
    env <- liftEffect $ mkEnv @Depth logger config
    jobs <- liftEffect $ Ref.new []
    pure { env, dummies: mkWidthDummies config.pallasSrs config.vestaSrs, jobs }
  liftEffect case res of
    Right st -> onReady st
    Left e -> onError (message e)

-- | A build/circuit fingerprint peers exchange to refuse cross-version meshes.
-- | M2 will derive this from the verifier-index bytes; for now it is a build
-- | constant (all peers on the same static build agree).
fingerprint :: ServiceState -> String
fingerprint _ = "snarky-p2p/txn-snark/depth4/v1"

-- | BASE mode: generate a block, prove each transaction's base proof locally,
-- | encode the leaves. The private witnesses never leave this function.
seedBlock :: ServiceState -> Effect SeedOut
seedBlock { env } = do
  { ledger, keys } <- randomSampleOne (genGenesisLedger 10)
  block <- generateBlock env.chainId keys ledger
  { snarkWork } <- processBlock env.chainId ledger block
  let n = Array.length snarkWork
  leaves <- sequence $ Array.mapWithIndex
    ( \j job -> do
        proof <- env.compiledTx.baseProver
          { env: { mask: job.mask, tx: job.tx }, statement: job.statement }
        let
          Statement { source, target } = job.statement
          key = stmtKey { source, target }
          wire = encodeLeaf (toSerializableCompiledProof proof)
        pure { slot: n + j, key, wire }
    )
    snarkWork
  let
    leafStmts = Array.mapWithIndex
      ( \j job ->
          let
            Statement { source, target } = job.statement
          in
            { slot: n + j, stmt: encodeStmt { source, target } }
      )
      snarkWork
  pure { n, leaves, leafStmts }

-- | BASE mode, stepped: generate the block and stash its jobs, returning only
-- | the public shape. The per-tx base proofs are then proved one at a time via
-- | `proveBaseLeaf` (the private witnesses stay in this worker).
genBlock :: ServiceState -> Effect BlockMeta
genBlock { env, jobs } = do
  { ledger, keys } <- randomSampleOne (genGenesisLedger 10)
  block <- generateBlock env.chainId keys ledger
  { snarkWork } <- processBlock env.chainId ledger block
  Ref.write snarkWork jobs
  let n = Array.length snarkWork
  let
    leafStmts = Array.mapWithIndex
      ( \j job ->
          let
            Statement { source, target } = job.statement
          in
            { slot: n + j, stmt: encodeStmt { source, target } }
      )
      snarkWork
  pure { n, leafStmts }

-- | Prove the j-th base leaf of the stashed block.
proveBaseLeaf :: ServiceState -> Int -> Effect LeafOut
proveBaseLeaf { env, jobs } j = do
  js <- Ref.read jobs
  case Array.index js j of
    Nothing -> throw ("proveBaseLeaf: no job " <> show j)
    Just job -> do
      proof <- env.compiledTx.baseProver { env: { mask: job.mask, tx: job.tx }, statement: job.statement }
      let Statement { source, target } = job.statement
      pure
        { slot: Array.length js + j
        , key: stmtKey { source, target }
        , wire: encodeLeaf (toSerializableCompiledProof proof)
        }

-- | Verify both child proofs, merge them, return the parent {key, wire}. The
-- | parent statement is `source` of the left child, `target` of the right —
-- | the in-circuit chaining enforces left.target == right.source.
merge :: ServiceState -> { aWire :: String, bWire :: String } -> Effect MergeOut
merge { env, dummies } { aWire, bWire } = do
  a <- decodeNode dummies aWire
  b <- decodeNode dummies bWire
  let ok = verifyBatch env.compiledTx.verifier [ toVerifiable a.proof, toVerifiable b.proof ]
  if not ok then
    -- Reject Byzantine / corrupt inputs before spending a merge on them.
    pure { key: "", wire: "" }
  else do
    let statement = Statement { source: a.source, target: b.target }
    proof <- env.compiledTx.mergeProver { proof1: a.proof, proof2: b.proof, statement }
    pure
      { key: stmtKey { source: a.source, target: b.target }
      , wire: encodeLeaf (toSerializableCompiledProof proof)
      }

verifyWire :: ServiceState -> String -> Effect Boolean
verifyWire { env, dummies } wire = do
  node <- decodeNode dummies wire
  pure (verifyBatch env.compiledTx.verifier [ toVerifiable node.proof ])
