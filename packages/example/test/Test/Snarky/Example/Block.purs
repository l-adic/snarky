-- | End-to-end block proving: `processBlock` turns a block of 4 transactions
-- | into per-transaction snark work (witness mask + statement), and the snark
-- | manager farms that work to its worker — base leaves first, each completion
-- | unlocking merge work up the scan-state tree — until a single root proof
-- | covers the whole block.
-- |
-- | This exercises the full pipeline that `Test.Snarky.Example.TransactionSnark`
-- | drives by hand: scan state, work/result channels, the dumb worker, and the
-- | reactive listener. The final assertions are that the root proof's statement
-- | is exactly `{ source = root L0, target = root L4 }` and that it verifies.
-- |
-- | The spec consumes the suite-wide `Env` (SRS + compiled program, built ONCE
-- | in `Test.Example.Main`'s `beforeAll`); the manager is started from the
-- | Env's compiled program and never compiles.
module Test.Snarky.Example.Block
  ( spec
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (for_)
import Data.Maybe (fromJust)
import Data.MerkleTree.Sparse (root)
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Class.Console as Console
import Mina.ChainId (ChainId)
import Partial.Unsafe (unsafePartial)
import Pickles (CompiledProof(..), StatementIO(..), toVerifiable, verifyBatch)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Block (Block(..), processBlock)
import Snarky.Example.Env (Env)
import Snarky.Example.Ledger (Ledger)
import Snarky.Example.Snark.Manager (mkManager, submitBlock, verifier)
import Snarky.Example.Transaction (SignedTransaction, Statement(..), applyTx)
import Test.QuickCheck.Gen (randomSampleOne)
import Test.Snarky.Example.Config (Depth)
import Test.Snarky.Example.Generators (Keystore, genLedger, genValidSignedTransaction)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | Generate a chain of `n` sequentially-valid transactions from `l`: each is
-- | valid against the ledger state left by the previous one.
genTxChain
  :: ChainId
  -> Int
  -> Keystore
  -> Ledger Depth
  -> Aff (Array (SignedTransaction Vesta.ScalarField))
genTxChain chainId n keys = go n []
  where
  go 0 acc _ = pure acc
  go k acc l = do
    tx <- liftEffect $ randomSampleOne (genValidSignedTransaction chainId l keys)
    l' <- liftEffect $ applyTx chainId tx l
    go (k - 1) (Array.snoc acc tx) l'

spec :: SpecT Aff (Env Depth) Aff Unit
spec =
  describe "Snarky.Example.Block" do
    it "proves a 4-transaction block to a single root proof via the snark manager" \env -> do
      { ledger, keys } <- liftEffect $ randomSampleOne (genLedger 10)
      let l0 = ledger :: Ledger Depth

      txs <- genTxChain env.chainId 4 keys l0
      let block = Block { transactions: unsafePartial fromJust (Vector.toVector txs) }

      -- Phase 1: sequential off-circuit fold — per transaction, the witness
      -- mask of the slots it touches and its { source, target } statement.
      { ledger: lFinal, snarkWork } <- liftEffect $ processBlock env.chainId l0 block
      Array.length snarkWork `shouldEqual` 4

      -- The jobs form a chain: job i's target is job i+1's source, anchored at
      -- root L0 and ending at the final ledger's root.
      let
        sourceOf j = let Statement s = j.statement in s.source
        targetOf j = let Statement s = j.statement in s.target
      for_ (Array.zip snarkWork (Array.drop 1 snarkWork)) \(Tuple j j') ->
        targetOf j `shouldEqual` sourceOf j'
      (sourceOf <$> Array.head snarkWork) `shouldEqual` pure (root l0.tree)
      (targetOf <$> Array.last snarkWork) `shouldEqual` pure (root lFinal.tree)

      -- Phase 2: ship the work. The manager (started from the Env's compiled
      -- program) runs the worker + listener and fills the scan-state tree
      -- (4 bases + 3 merges) to the root.
      Console.log "[Block] starting snark manager; submitting block…"
      manager <- mkManager env.compiledTx
      rootProof <- submitBlock manager 0 snarkWork
      Console.log "[Block] root proof received; checking statement + verifying…"

      -- The root proof's statement must span the whole block: L0 → L4.
      let
        CompiledProof cp = rootProof
        StatementIO io = cp.statement
        Statement rootStmt = io.input
      rootStmt.source `shouldEqual` root l0.tree
      rootStmt.target `shouldEqual` root lFinal.tree

      verifyBatch (verifier manager) [ toVerifiable rootProof ] `shouldEqual` true
