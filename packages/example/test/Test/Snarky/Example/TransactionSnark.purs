-- | The pickled transaction-snark as a single two-branch application
-- | program, mirroring Mina's `Transaction_snark` (`compile
-- | ~choices:[Base; Merge]`):
-- |
-- |   * branch 0 — `baseRule` (mpv = 0): proves a single signed transfer
-- |     `target = processTransaction(source, tx)`. Exercises app advice
-- |     (`AccountMapM` / `MerkleRequestM` / `TransferM`) on the bare app
-- |     monad `TransferM`.
-- |   * branch 1 — `mergeRule` (mpv = 2, Self): verifies two proofs of THIS
-- |     program (base or merge, interchangeably — same wrap VK) and composes
-- |     their statements.
-- |
-- | Both branches compile to ONE wrap VK that the merge's `Self` slots
-- | recurse on. The test proves two base transitions forming a ledger chain
-- | (L0 → L1 → L2), merges them into a single L0 → L2 statement, and
-- | `verifyBatch`-checks all three proofs.
module Test.Snarky.Example.TransactionSnark
  ( spec
  ) where

import Prelude

import Control.Monad.Except (runExceptT)
import Data.Array (range)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.MerkleTree.Sparse as Sparse
import Data.Tuple (fst, snd)
import Data.Tuple.Nested (type (/\), tuple2)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Class.Console as Console
import Effect.Exception as Exc
import Effect.Ref as Ref
import Pickles (BranchProver(..), Compiled, CompiledProof, PrevSlot(..), RulesCons, RulesNil, Slot, SlotWrapKey(..), Slots2, StatementIO, StepField, compileMulti, mkRuleEntry, toVerifiable, verifyBatch)
import Snarky.Backend.Kimchi.Class (addLagrangeBasis, createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.RandomOracle (Digest)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Transaction (SignedTransaction, Statement(..), TransferM, applyTx, baseRule, mergeRule, runTransferM)
import Test.QuickCheck.Gen (randomSampleOne)
import Test.Snarky.Example.Config (Depth, chainId)
import Test.Snarky.Example.Generators (genLedger, genValidSignedTransaction)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | The shared statement type carried as each branch's public input: a
-- | {source, target} ledger-digest pair with no public output.
type TxnStmt = StatementIO (Statement Vesta.ScalarField) Unit

-- | The two-branch program. Branch 0 (base) has no prev slots; branch 1
-- | (merge) has two `Self` slots, each width 2 (a proof of THIS mpv=2
-- | program) at one chunk.
type TxnSnarkRules =
  RulesCons 0 Unit Unit Unit
    ( RulesCons 2
        (TxnStmt /\ TxnStmt /\ Unit)
        (Slot Compiled 2 1 TxnStmt /\ Slot Compiled 2 1 TxnStmt /\ Unit)
        (SlotWrapKey /\ SlotWrapKey /\ Unit)
        RulesNil
    )

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

      -- Initial ledger L0, held in the prover monad's ledger ref (with the
      -- wallet `keys` to sign transfers). The base rule's `processTransaction`
      -- reads accounts from and mutates this tree, so after each base prove
      -- the ref's ledger advances by one transition.
      { ledger: l0, keys } <- liftEffect $ randomSampleOne (genLedger 10)
      ref <- liftEffect $ Ref.new l0

      let
        cfg =
          { srs: { vestaSrs, pallasSrs }
          , debug: false
          -- `override_wrap_domain: N1` (2^14), the canonical N2 setting
          -- (Mina's transaction_snark and every N2 pickles fixture use it).
          -- Required so each Self slot's wrap-domain lagrange basis matches
          -- the wrap proofs the merge recurses on; omitting it (default N2 =
          -- 2^15) makes the merge's slot-0 xhat/IVP transcript diverge.
          , wrapDomainOverride: Just 14
          , proofCache: Nothing
          }

      baseEntry <- liftEffect $ mkRuleEntry @2 @Unit @(Statement Vesta.ScalarField) @1 @1 @(TransferM Depth Vesta.ScalarField)
        (baseRule @Depth chainId)
        unit
      mergeEntry <- liftEffect $ mkRuleEntry @2 @Unit @(Statement Vesta.ScalarField) @1 @1 @(TransferM Depth Vesta.ScalarField)
        mergeRule
        (tuple2 Self Self)

      let rules = tuple2 baseEntry mergeEntry

      out <- liftEffect $ runTransferM { currentTransaction: Nothing, ledger: ref } $ compileMulti
        @TxnSnarkRules
        @Unit
        @(Statement Vesta.ScalarField)
        @(Slots2 2 2)
        @1
        cfg
        rules

      let
        BranchProver baseProver = fst out.provers
        BranchProver mergeProver = fst (snd out.provers)

        runBase
          :: SignedTransaction Vesta.ScalarField
          -> Statement Vesta.ScalarField
          -> Aff (CompiledProof 2 TxnStmt)
        runBase tx appInput = do
          e <- liftEffect $ runTransferM { currentTransaction: Just tx, ledger: ref } $ runExceptT $ baseProver
            { appInput, prevs: unit, sideloadedVKs: unit }
          case e of
            Left err -> liftEffect $ Exc.throw ("baseProver: " <> show err)
            Right p -> pure p

      Console.log "[TxnSnark] compiled program; proving base0…"

      -- base0: L0 → L1 with a fresh valid transfer. `source0` is the
      -- pre-state root; `target0` is the pure post-transfer root (the same
      -- value `processTransaction` computes in-circuit).
      let source0 = Sparse.root l0.tree :: Digest Vesta.ScalarField
      tx0 <- liftEffect $ randomSampleOne (genValidSignedTransaction chainId l0 keys)
      postState0 <- liftEffect $ applyTx chainId tx0 l0
      let target0 = Sparse.root postState0.tree
      b0 <- runBase tx0 (Statement { source: source0, target: target0 })
      Console.log "[TxnSnark] base0 proved; proving base1…"

      -- base1: L1 → L2. Read the ref's actual post-b0 state (the base
      -- rule mutated it to L1) and transfer from there.
      l1 <- liftEffect $ Ref.read ref
      let source1 = Sparse.root l1.tree :: Digest Vesta.ScalarField
      tx1 <- liftEffect $ randomSampleOne (genValidSignedTransaction chainId l1 keys)
      postState1 <- liftEffect $ applyTx chainId tx1 l1
      let target1 = Sparse.root postState1.tree
      b1 <- runBase tx1 (Statement { source: source1, target: target1 })
      Console.log "[TxnSnark] base1 proved; verifying [b0, b1] standalone…"

      -- Milestone check: the two base proofs verify on their own. This
      -- isolates "are base proofs well-formed at mpv=2" from "does the
      -- merge reconstruct their transcript correctly".
      verifyBatch out.verifier (map toVerifiable [ b0, b1 ]) `shouldEqual` true
      Console.log "[TxnSnark] [b0, b1] verified"

      -- merge(b0, b1): connects L0 → L1 → L2 into one L0 → L2 statement.
      -- Both prevs are real `InductivePrev` proofs (base proofs are valid
      -- Self-prevs — same wrap VK), so no base-case dummy is needed.
      Console.log "[TxnSnark] proving merge…"
      let mergedStmt = Statement { source: source0, target: target1 }
      eMerge <- liftEffect $ runTransferM { currentTransaction: Nothing, ledger: ref } $ runExceptT $ mergeProver
        { appInput: mergedStmt
        , prevs: tuple2 (InductivePrev b0 out.tag) (InductivePrev b1 out.tag)
        , sideloadedVKs: tuple2 unit unit
        }
      merge <- case eMerge of
        Left err -> liftEffect $ Exc.throw ("mergeProver: " <> show err)
        Right p -> pure p
      Console.log "[TxnSnark] merge proved; batch-verifying full chain…"
      verifyBatch out.verifier (map toVerifiable [ b0, b1, merge ]) `shouldEqual` true
