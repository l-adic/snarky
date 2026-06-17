-- | Tier-4 integration: prove a whole block end-to-end through the P2P star, in
-- | Node, with REAL proofs — but no browser. The snark manager drives the
-- | coordinator's `WorkerBackend` (`Snarky.Example.P2P.Coordinator.mkStarBackend`),
-- | which assigns each work item over the in-memory transport to a real remote
-- | peer (`runStarPeer`); the peer proves it, encodes the `CompiledProof`, and
-- | ships it back over the bus, where the coordinator decodes it (`mapResult`).
-- |
-- | This is the one tier that exercises the proof SERIALIZE→wire→DESERIALIZE path
-- | the stub-prover coordination tests can't, and it does so without the headless
-- | browser. Both ends reuse the suite-wide `Env` (the SRS + compiled program
-- | built once in `Test.Example.Main`), so nothing recompiles — only proving runs.
-- |
-- | The assertions mirror `Test.Snarky.Example.Block`: the root proof spans the
-- | whole block (L0 → L4) and verifies.
module Test.Snarky.Example.P2P.PipelineSpec
  ( spec
  ) where

import Prelude

import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.MerkleTree.Sparse (root)
import Data.Newtype (un)
import Data.Time.Duration (Milliseconds(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Pickles (CompiledProof(..), StatementIO(..), toVerifiable, verifyBatch)
import Pickles.Prove.SerializeProof (decodeCompiledProof, encodeCompiledProof)
import Snarky.Example.Block (processBlock)
import Snarky.Example.Env (Env)
import Snarky.Example.Ledger (Ledger)
import Snarky.Example.Log as Log
import Snarky.Example.P2P.Coordinator (mapResult, mkStarBackend)
import Snarky.Example.P2P.Peer (runStarPeer)
import Snarky.Example.P2P.Types (Payload(..))
import Snarky.Example.Simulation (genGenesisLedger, generateBlock)
import Snarky.Example.Snark.Manager (mkManager, submitBlock)
import Snarky.Example.Snark.Pool (PoolSize(Dynamic))
import Snarky.Example.Snark.Work (decodeWorkItem, encodeWorkItem)
import Snarky.Example.Snark.Worker (proveItem)
import Snarky.Example.Transaction (Statement(..))
import Test.QuickCheck.Gen (randomSampleOne)
import Test.Snarky.Example.Config (Depth)
import Test.Snarky.Example.P2P.InMemoryBus (connect, newBus)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT Aff (Env Depth) Aff Unit
spec =
  describe "Snarky.Example.P2P pipeline" do
    it "proves a block to a root over the in-memory transport (real proofs, real codecs)" \env -> do
      { ledger, keys } <- liftEffect $ randomSampleOne (genGenesisLedger 10)
      let l0 = ledger :: Ledger Depth
      block <- liftEffect $ generateBlock env.chainId keys l0
      { ledger: lFinal, snarkWork } <- liftEffect $ processBlock env.chainId l0 block

      -- One bus, a coordinator + one remote peer.
      bus <- liftEffect newBus
      coordT <- liftEffect (connect bus "coord")
      peerT <- liftEffect (connect bus "peer")

      -- The coordinator backend: assign over the transport, decode each result
      -- back into a CompiledProof. No self prover — the remote peer does the work.
      base <- liftEffect $ mkStarBackend
        { logger: env.logger
        , transport: coordT
        , encodeJob: Payload <<< encodeWorkItem
        , jobLabel: const "proving"
        , prepareLocal: pure (Left "no self worker in test")
        , onPeers: \_ -> pure unit
        }
      let backend e = mapResult (lmap show <<< decodeCompiledProof e <<< un Payload) base

      -- A real remote peer: decode the work item, prove it with the shared Env's
      -- compiled program (no recompile), and ship the encoded proof back.
      liftEffect $ runStarPeer
        { transport: peerT
        , logger: env.logger
        , prove: \encoded -> case decodeWorkItem env (un Payload encoded) of
            Left e -> throw ("decodeWorkItem failed: " <> show e)
            Right item -> (Payload <<< encodeCompiledProof) <$> proveItem env.compiledTx item
        , describeJob: const "job"
        , onPhase: \_ -> pure unit
        , reannounceMs: 50.0
        , reannounceMax: 40
        }

      Log.logInfo env.logger "[Pipeline] submitting block over the in-memory transport"
      manager <- mkManager
        { logger: env.logger
        , onProgress: Nothing
        , poolSize: Dynamic
        , jobTimeout: Milliseconds 120000.0
        , backend
        }
        env
      rootProof <- submitBlock manager 0 snarkWork

      -- The root proof's statement must span the whole block: L0 → L4, and verify.
      let
        CompiledProof cp = rootProof
        StatementIO io = cp.statement
        Statement rootStmt = io.input
      rootStmt.source `shouldEqual` root l0.tree
      rootStmt.target `shouldEqual` root lFinal.tree
      verifyBatch env.compiledTx.verifier [ toVerifiable rootProof ] `shouldEqual` true
