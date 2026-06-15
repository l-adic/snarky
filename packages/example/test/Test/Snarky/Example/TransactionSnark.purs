-- | The pickled transaction-snark as a single two-branch application
-- | program, mirroring Mina's `Transaction_snark` (`compile
-- | ~choices:[Base; Merge]`):
-- |
-- |   * branch 0 — `baseRule` (mpv = 0): proves a single signed transfer
-- |     `target = processTransaction(source, tx)` against an extracted
-- |     `Mask` witness (the slots the transfer touches), not the full ledger.
-- |   * branch 1 — `mergeRule` (mpv = 2, Self): verifies two proofs of THIS
-- |     program (base or merge, interchangeably — same wrap VK) and composes
-- |     their statements.
-- |
-- | The spec consumes the suite-wide `Env` (SRS + compiled program, built ONCE
-- | in `Test.Example.Main`'s `beforeAll`) and drives a two-base + one-merge
-- | chain (L0 → L1 → L2), proving each base against the mask of the ledger at
-- | that point, and `verifyBatch`-checking all three proofs. So it also
-- | validates that proving against the witness slice ≡ proving against the
-- | whole ledger.
module Test.Snarky.Example.TransactionSnark
  ( spec
  ) where

import Prelude

import Data.Either (Either(..))
import Data.MerkleTree.Sparse as Sparse
import Data.MerkleTree.Sparse.Mask (fromSubset)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Pickles (CompiledProof, toVerifiable, verifyBatch)
import Snarky.Circuit.RandomOracle (Digest)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Env (Env)
import Snarky.Example.Ledger (Ledger)
import Snarky.Example.Log as Log
import Snarky.Example.Simulation (genGenesisLedger, genValidSignedTransaction)
import Snarky.Example.Snark.Work (BaseJob, decodeBaseJob, decodeMergeJob, encodeBaseJob, encodeMergeJob)
import Snarky.Example.Transaction (SignedTransaction, Statement(..), TxnStmt, applyTx, touchedAccounts)
import Test.QuickCheck.Gen (randomSampleOne)
import Test.Snarky.Example.Config (Depth)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT Aff (Env Depth) Aff Unit
spec =
  describe "Snarky.Example.TransactionSnark" do
    it "proves two base transitions + a merge of them, and batch-verifies the chain" \env -> do
      let { baseProver, mergeProver, verifier } = env.compiledTx

      -- Initial ledger L0 (with the wallet `keys` to sign transfers). The
      -- ledger is threaded immutably by `applyTx`; each base proof runs against
      -- the mask of the ledger at that point, not a shared ref.
      { ledger, keys } <- liftEffect $ randomSampleOne (genGenesisLedger 10)
      let l0 = ledger :: Ledger Depth

      let
        -- Prove a base transition against the mask of `l` (= the slots the
        -- transfer touches), extracted via `touchedAccounts` + `fromSubset`.
        runBase
          :: Ledger Depth
          -> SignedTransaction Vesta.ScalarField
          -> Statement Vesta.ScalarField
          -> Aff (CompiledProof 2 TxnStmt)
        runBase l tx statement = do
          -- Round-trip the base job (tx + witness mask + statement) through the
          -- transport codec first, then prove from the DECODED job — so the
          -- proof succeeds only if the mask codec is byte-faithful.
          let job = { tx, mask: fromSubset l.tree (touchedAccounts l tx), statement } :: BaseJob Depth
          job' <- case decodeBaseJob (encodeBaseJob job) of
            Left e -> liftEffect $ throw ("decodeBaseJob: " <> show e)
            Right j -> pure j
          liftEffect $ baseProver
            { env: { mask: job'.mask, tx: job'.tx }, statement: job'.statement }

      Log.logInfo env.logger "[TxnSnark] proving base0…"

      -- base0: L0 → L1. `source0` is the pre-state root; `target0` the pure
      -- post-transfer root (the same value the circuit computes from the mask).
      tx0 <- liftEffect $ randomSampleOne (genValidSignedTransaction env.chainId l0 keys)
      let source0 = Sparse.root l0.tree :: Digest Vesta.ScalarField
      l1 <- liftEffect $ applyTx env.chainId tx0 l0
      let target0 = Sparse.root l1.tree
      b0 <- runBase l0 tx0 (Statement { source: source0, target: target0 })
      Log.logInfo env.logger "[TxnSnark] base0 proved; proving base1…"

      -- base1: L1 → L2, transferring from the post-b0 state.
      tx1 <- liftEffect $ randomSampleOne (genValidSignedTransaction env.chainId l1 keys)
      let source1 = Sparse.root l1.tree :: Digest Vesta.ScalarField
      l2 <- liftEffect $ applyTx env.chainId tx1 l1
      let target1 = Sparse.root l2.tree
      b1 <- runBase l1 tx1 (Statement { source: source1, target: target1 })
      Log.logInfo env.logger "[TxnSnark] base1 proved; verifying [b0, b1] standalone…"

      -- Milestone check: the two base proofs verify on their own.
      verifyBatch verifier (map toVerifiable [ b0, b1 ]) `shouldEqual` true
      Log.logInfo env.logger "[TxnSnark] [b0, b1] verified"

      -- merge(b0, b1): connects L0 → L1 → L2 into one L0 → L2 statement.
      Log.logInfo env.logger "[TxnSnark] proving merge…"
      let mergedStmt = Statement { source: source0, target: target1 }
      -- Round-trip the merge job through the transport codec first: the merge
      -- proves from the DECODED child proofs, so it succeeds only if
      -- encode/decode is byte-faithful.
      mergeJob <- case decodeMergeJob env (encodeMergeJob { proof1: b0, proof2: b1, statement: mergedStmt }) of
        Left e -> liftEffect $ throw ("decodeMergeJob: " <> show e)
        Right j -> pure j
      merge <- liftEffect $ mergeProver mergeJob
      Log.logInfo env.logger "[TxnSnark] merge proved (from round-tripped job); batch-verifying full chain…"
      verifyBatch verifier (map toVerifiable [ b0, b1, merge ]) `shouldEqual` true
