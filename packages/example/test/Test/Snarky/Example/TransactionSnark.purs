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
-- | The whole compile + prover wiring lives in
-- | `Snarky.Example.Transaction.Checked.compileTxCircuit`; this test drives a
-- | two-base + one-merge chain (L0 → L1 → L2), proving each base against the
-- | mask of the ledger at that point, and `verifyBatch`-checking all three
-- | proofs. So it also validates that proving against the witness slice ≡
-- | proving against the whole ledger.
module Test.Snarky.Example.TransactionSnark
  ( spec
  ) where

import Prelude

import Data.Array (range)
import Data.Foldable (for_)
import Data.MerkleTree.Sparse as Sparse
import Data.MerkleTree.Sparse.Mask (fromSubset)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Class.Console as Console
import Pickles (CompiledProof, StepField, toVerifiable, verifyBatch)
import Snarky.Backend.Kimchi.Class (addLagrangeBasis, createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.RandomOracle (Digest)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Ledger (Ledger)
import Snarky.Example.Transaction (SignedTransaction, Statement(..), TxnStmt, applyTx, compileTxCircuit, touchedAccounts)
import Test.QuickCheck.Gen (randomSampleOne)
import Test.Snarky.Example.Config (Depth, chainId)
import Test.Snarky.Example.Generators (genLedger, genValidSignedTransaction)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | Build the Pasta SRSes with the lagrange-basis caches pre-warmed for the
-- | step (Vesta, 2^9..2^16) and wrap (Pallas, 2^12..2^15) domains this
-- | program touches. Mirrors `Test.Pickles.SharedSrs.buildSharedSrs`; the
-- | wrap depth (2^15) is the OCaml Tock URS convention.
buildSrs :: Aff { pallasSrs :: CRS PallasG, vestaSrs :: CRS VestaG }
buildSrs = liftEffect do
  let pallasSrs = PallasImpl.pallasCrsCreate 32768
  vestaSrs <- createCRS @StepField
  for_ (range 9 16) (addLagrangeBasis vestaSrs)
  for_ (range 12 15) (addLagrangeBasis pallasSrs)
  pure { pallasSrs, vestaSrs }

spec :: SpecT Aff Unit Aff Unit
spec =
  describe "Snarky.Example.TransactionSnark" do
    it "proves two base transitions + a merge of them, and batch-verifies the chain" do
      { pallasSrs, vestaSrs } <- buildSrs

      -- Initial ledger L0 (with the wallet `keys` to sign transfers). The
      -- ledger is threaded immutably by `applyTx`; each base proof runs against
      -- the mask of the ledger at that point, not a shared ref.
      { ledger, keys } <- liftEffect $ randomSampleOne (genLedger 10)
      let l0 = ledger :: Ledger Depth

      -- Compile the two-branch program once. The provers are self-contained
      -- (`Effect`), taking the witness env directly.
      { baseProver, mergeProver, verifier } <- liftEffect $
        compileTxCircuit chainId { vestaSrs, pallasSrs }

      let
        -- Prove a base transition against the mask of `l` (= the slots the
        -- transfer touches), extracted via `touchedAccounts` + `fromSubset`.
        runBase
          :: Ledger Depth
          -> SignedTransaction Vesta.ScalarField
          -> Statement Vesta.ScalarField
          -> Aff (CompiledProof 2 TxnStmt)
        runBase l tx statement =
          liftEffect $ baseProver
            { env: { mask: fromSubset l.tree (touchedAccounts l tx), tx }
            , statement
            }

      Console.log "[TxnSnark] compiled program; proving base0…"

      -- base0: L0 → L1. `source0` is the pre-state root; `target0` the pure
      -- post-transfer root (the same value the circuit computes from the mask).
      tx0 <- liftEffect $ randomSampleOne (genValidSignedTransaction chainId l0 keys)
      let source0 = Sparse.root l0.tree :: Digest Vesta.ScalarField
      l1 <- liftEffect $ applyTx chainId tx0 l0
      let target0 = Sparse.root l1.tree
      b0 <- runBase l0 tx0 (Statement { source: source0, target: target0 })
      Console.log "[TxnSnark] base0 proved; proving base1…"

      -- base1: L1 → L2, transferring from the post-b0 state.
      tx1 <- liftEffect $ randomSampleOne (genValidSignedTransaction chainId l1 keys)
      let source1 = Sparse.root l1.tree :: Digest Vesta.ScalarField
      l2 <- liftEffect $ applyTx chainId tx1 l1
      let target1 = Sparse.root l2.tree
      b1 <- runBase l1 tx1 (Statement { source: source1, target: target1 })
      Console.log "[TxnSnark] base1 proved; verifying [b0, b1] standalone…"

      -- Milestone check: the two base proofs verify on their own.
      verifyBatch verifier (map toVerifiable [ b0, b1 ]) `shouldEqual` true
      Console.log "[TxnSnark] [b0, b1] verified"

      -- merge(b0, b1): connects L0 → L1 → L2 into one L0 → L2 statement.
      Console.log "[TxnSnark] proving merge…"
      let mergedStmt = Statement { source: source0, target: target1 }
      merge <- liftEffect $ mergeProver { proof1: b0, proof2: b1, statement: mergedStmt }
      Console.log "[TxnSnark] merge proved; batch-verifying full chain…"
      verifyBatch verifier (map toVerifiable [ b0, b1, merge ]) `shouldEqual` true
