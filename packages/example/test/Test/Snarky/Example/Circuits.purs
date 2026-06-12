module Test.Snarky.Example.Circuits
  ( spec
  ) where

import Prelude

import Data.Foldable (for_)
import Data.Functor.Variant (case_, on)
import Data.Maybe (Maybe(..))
import Data.MerkleTree.Sparse as Sparse
import Data.Reflectable (class Reflectable, reifyType)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Class.Console as Console
import Effect.Exception (throw)
import Effect.Ref (Ref, read, write)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)
import Snarky.Backend.Advice (AdviceHandler(..), badAdvice)
import Snarky.Backend.Compile (compile, makeSolver)
import Snarky.Circuit.DSL (FVar, Snarky, const_)
import Snarky.Circuit.Kimchi (verifyCircuitM)
import Snarky.Circuit.MerkleTree (MerkleF(..), _merkle)
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Constraint.Kimchi (KimchiConstraint, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Ledger (Ledger, lookupAddress)
import Snarky.Example.Simulation (genGenesisLedger, genOverdraftSignedTransaction, genValidSignedTransaction)
import Snarky.Example.Transaction (SignedTransaction, TransferAdvice, applyTx, applyTxChecked)
import Snarky.Example.Transaction.Monad (AccountMapF(..), TransactionF(..), _accountMap, _transaction)
import Snarky.Example.Types (Account)
import Test.QuickCheck.Gen (randomSampleOne)
import Test.Snarky.Circuit.Utils (quickCheckEffect, runTestM, satisfied, unsatisfied)
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

-- | Full-ledger advice interpreter for the standalone-circuit tests:
-- | answers Merkle/account requests from a complete `Ledger` reference
-- | (production proving uses the mask-backed `runTransferMaskM`; this
-- | test exercises the circuit against the whole tree).
runTransferM
  :: forall d
   . Reflectable d Int
  => { currentTransaction :: Maybe (SignedTransaction Vesta.ScalarField), ledger :: Ref (Ledger d) }
  -> AdviceHandler (TransferAdvice d)
runTransferM env = AdviceHandler
  ( case_
      # on _transaction transactionH
      # on _accountMap accountMapH
      # on _merkle merkleH
  )
  where
  getLedger = read env.ledger

  merkleH :: MerkleF Vesta.ScalarField (Account Vesta.ScalarField) d ~> Effect
  merkleH = case _ of
    GetElement addr k -> getLedger >>= \{ tree } ->
      case Sparse.get tree addr of
        Just v -> pure (k { value: v, path: Sparse.getWitness addr tree })
        Nothing -> throw "getElement: address not set in sparse tree"
    GetPath addr k -> getLedger <#> \{ tree } ->
      k (Sparse.getWitness addr tree)
    SetValue addr v k -> getLedger >>= \ledger ->
      case Sparse.set addr v ledger.tree of
        Just tree' -> write (ledger { tree = tree' }) env.ledger $> k
        Nothing -> throw "setValue: invalid address"

  accountMapH :: AccountMapF d ~> Effect
  accountMapH (GetAccountId pk k) = getLedger >>= \ledger ->
    case lookupAddress ledger pk of
      Just addr -> pure (k addr)
      Nothing -> throw "getAccountId: public key not found in account map"

  transactionH :: TransactionF ~> Effect
  transactionH (GetCurrentTransaction k) = case env.currentTransaction of
    Just tx -> pure (k tx)
    Nothing -> throw "getCurrentTransaction: no current transaction set"

transferSpec
  :: forall d
   . Reflectable d Int
  => Proxy d
  -> Aff Unit
transferSpec _ = do
  { ledger, keys } <- liftEffect $ randomSampleOne (genGenesisLedger 10)

  let
    -- Expected root after applying the transfer: the pure ledger arrow.
    -- The in-circuit `processTransaction` must agree with this. `apply`
    -- is in `Effect` only to `throw` on bad inputs; the valid-case generator
    -- never produces those, so `unsafePerformEffect` is safe here.
    testFunction :: SignedTransaction Vesta.ScalarField -> Digest Vesta.ScalarField
    testFunction tx = Sparse.root (unsafePerformEffect (applyTx chainId tx ledger)).tree

    rootVar =
      let
        Digest r = Sparse.root ledger.tree
      in
        Digest $ const_ r

    -- The circuit verifies the signature, then applies the transfer.
    circuit
      :: SignedTransaction (FVar Vesta.ScalarField)
      -> Snarky Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) (TransferAdvice d) (Digest (FVar Vesta.ScalarField))
    circuit tx = applyTxChecked @d chainId rootVar tx

    solver = makeSolver (Proxy @(KimchiConstraint Vesta.ScalarField)) circuit

  s <- liftEffect $
    compile badAdvice
      (Proxy @(SignedTransaction Vesta.ScalarField))
      (Proxy @(Digest Vesta.ScalarField))
      (Proxy @(KimchiConstraint Vesta.ScalarField))
      circuit

  ref <- liftEffect $ Ref.new ledger

  let
    -- The transfer circuit takes its transaction explicitly, so the prover
    -- monad needs no current transaction — only the (mutable) ledger.
    env = { currentTransaction: Nothing, ledger: ref }

  Console.log "Checking the Valid case"
  liftEffect $ quickCheckEffect 100 (genValidSignedTransaction chainId ledger keys) \a -> do
    write ledger ref
    runTestM (runTransferM env) { builtState: s, solver, checker: eval, postCondition: Kimchi.postCondition } (satisfied testFunction) a

  liftEffect $ write ledger ref
  liftEffect $ verifyCircuitM (runTransferM env) { s, gen: genValidSignedTransaction chainId ledger keys, solver }

  Console.log "Checking the overdraft case"
  liftEffect $ quickCheckEffect 100 (genOverdraftSignedTransaction chainId ledger keys) \a -> do
    write ledger ref
    runTestM (runTransferM env) { builtState: s, solver, checker: eval, postCondition: Kimchi.postCondition } unsatisfied a
  liftEffect $ write ledger ref
