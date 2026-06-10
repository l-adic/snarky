module Test.Snarky.Example.Circuits
  ( spec
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Maybe (Maybe(..), fromJust)
import Data.MerkleTree.Sparse as Sparse
import Data.Reflectable (class Reflectable, reifyType)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Class.Console as Console
import Effect.Exception (throw, try)
import Effect.Ref (write)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)
import Partial.Unsafe (unsafePartial)
import Snarky.Backend.Compile (compile, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky, const_)
import Snarky.Circuit.Kimchi (verifyCircuitM)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Constraint.Kimchi (KimchiConstraint, eval, initialState)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Ledger (balanceOf, getAccount, lookupAddress)
import Snarky.Example.Simulation (genGenesisLedger, genOverdraftSignedTransaction, genUnknownReceiverSignedTransaction, genValidSignedTransaction, genWrongNonceSignedTransaction)
import Snarky.Example.Transaction (class AccountMapM, SignedTransaction(..), Transaction(..), Transfer(..), TransferCompileM, TransferM, applyTx, applyTxChecked, runTransferCompileM, runTransferM)
import Snarky.Example.Types (Account(..), mkAmount)
import Test.QuickCheck (quickCheck', (===))
import Test.QuickCheck.Gen (randomSampleOne)
import Test.Snarky.Circuit.Utils (runTestM, satisfied, unsatisfied)
import Test.Snarky.Example.Config (chainId)
import Test.Spec (SpecT, describe, it)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- Spec

-- | Tree depths to test
treeDepths :: Array Int
treeDepths = [ 4, 6 ]

spec :: SpecT Aff Unit Aff Unit
spec =
  describe "Transfer Circuit Specs" do
    for_ treeDepths \depth ->
      describe ("depth " <> show depth) do
        it "processTransaction" $ reifyType depth transferSpec

transferSpec
  :: forall d
   . Reflectable d Int
  => Proxy d
  -> Aff Unit
transferSpec _ = do
  { ledger, keys } <- liftEffect $ randomSampleOne (genGenesisLedger 10)

  let
    -- Test-local oracle: directly construct the expected post-transfer tree
    -- (sender debited + nonce bumped, receiver credited) and take its root.
    -- Deliberately does no validation — the rejection scenarios below cover
    -- that — so it stays independent of the circuit it is checking.
    expectedRoot :: SignedTransaction Vesta.ScalarField -> Digest Vesta.ScalarField
    expectedRoot (SignedTransaction { transaction: Transaction { transfer: Transfer { from, to, amount } } }) =
      unsafePartial $ fromJust do
        fromAddr <- lookupAddress ledger from
        toAddr <- lookupAddress ledger to
        Account sender <- getAccount ledger fromAddr
        senderBalance <- mkAmount (balanceOf sender.tokenBalance - balanceOf amount)
        tree' <- Sparse.set fromAddr
          (Account sender { tokenBalance = senderBalance, nonce = sender.nonce + one })
          ledger.tree
        Account receiver <- Sparse.get tree' toAddr
        receiverBalance <- mkAmount (balanceOf receiver.tokenBalance + balanceOf amount)
        tree'' <- Sparse.set toAddr (Account receiver { tokenBalance = receiverBalance }) tree'
        pure (Sparse.root tree'')

    rootVar =
      let
        Digest r = Sparse.root ledger.tree
      in
        Digest $ const_ r

    -- The circuit verifies the signature, then applies the transfer.
    circuit
      :: forall t @m
       . AccountMapM m d
      => CMT.MerkleRequestM m Vesta.ScalarField (Account Vesta.ScalarField) d
      => CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t m
      => SignedTransaction (FVar Vesta.ScalarField)
      -> Snarky (KimchiConstraint Vesta.ScalarField) t m (Digest (FVar Vesta.ScalarField))
    circuit tx = applyTxChecked @d chainId rootVar tx

    solver = makeSolver (Proxy @(KimchiConstraint Vesta.ScalarField)) circuit
    s =
      runTransferCompileM $
        compile
          (Proxy @(SignedTransaction Vesta.ScalarField))
          (Proxy @(Digest Vesta.ScalarField))
          (Proxy @(KimchiConstraint Vesta.ScalarField))
          (circuit @(TransferCompileM d))
          initialState

  ref <- liftEffect $ Ref.new ledger

  let
    -- The transfer circuit takes its transaction explicitly, so the prover
    -- monad needs no current transaction — only the (mutable) ledger.
    env = { currentTransaction: Nothing, ledger: ref }

    -- Reset the ledger before each test case
    natWithReset :: TransferM d ~> Effect
    natWithReset m = do
      write ledger ref
      runTransferM env m

  Console.log "Checking the valid case"
  liftEffect $ quickCheck' 100 $ genValidSignedTransaction chainId ledger keys <#> \a ->
    unsafePerformEffect $ natWithReset $ runTestM { builtState: s, solver, checker: eval, postCondition: Kimchi.postCondition } (satisfied expectedRoot) a

  liftEffect $ write ledger ref
  liftEffect $ runTransferM env $ verifyCircuitM { s, gen: genValidSignedTransaction chainId ledger keys, solver }

  Console.log "Checking the overdraft case"
  liftEffect $ quickCheck' 100 $ genOverdraftSignedTransaction chainId ledger keys <#> \a ->
    unsafePerformEffect $ natWithReset $ runTestM { builtState: s, solver, checker: eval, postCondition: Kimchi.postCondition } unsatisfied a

  Console.log "Checking the wrong-nonce case"
  liftEffect $ quickCheck' 100 $ genWrongNonceSignedTransaction chainId ledger keys <#> \a ->
    unsafePerformEffect $ natWithReset $ runTestM { builtState: s, solver, checker: eval, postCondition: Kimchi.postCondition } unsatisfied a
  liftEffect $ write ledger ref

  -- `applyTx` is the same circuit run through the `runAndCheck` interpreter
  -- (ProverT with eager constraint checking): check that it agrees with the
  -- oracle on valid transfers and rejects each invalid scenario.
  Console.log "Checking applyTx (the unchecked interpretation) against the oracle"
  liftEffect $ quickCheck' 10 $ genValidSignedTransaction chainId ledger keys <#> \tx ->
    Sparse.root (unsafePerformEffect (applyTx chainId tx ledger)).tree === expectedRoot tx

  Console.log "Checking applyTx rejects invalid transactions"
  liftEffect $
    for_
      [ genOverdraftSignedTransaction
      , genWrongNonceSignedTransaction
      , genUnknownReceiverSignedTransaction
      ]
      \gen -> do
        tx <- randomSampleOne (gen chainId ledger keys)
        try (applyTx chainId tx ledger) >>= case _ of
          Left _ -> pure unit
          Right _ -> throw "expected applyTx to reject the transaction"
