-- | The prover-side advice effects and their interpreters, plus the
-- | `TRANSACTION` effect the circuit rules speak through.
-- |
-- | `runTransferM` answers a circuit's advice requests (`MERKLE` /
-- | `ACCOUNT_MAP` / `TRANSACTION`) against a live ledger and the particular
-- | transaction being proven. The transaction is NOT ledger state — it is the
-- | "arrow" mapping one ledger to the next — so it rides the handler's
-- | environment as an explicit per-prove input alongside the (mutable) ledger
-- | reference:
-- |
-- |   { currentTransaction :: Maybe (SignedTransaction Vesta.ScalarField)
-- |   , ledger :: Ref (Ledger d) }
-- |
-- | A base prove supplies `currentTransaction = Just tx`; a merge prove
-- | (which witnesses no transaction) supplies `Nothing`. `runTransferCompileM`
-- | is the compile-time twin whose handlers throw (compilation discards
-- | `exists` bodies, so no request is ever served).
-- |
-- | Everything here is value-only, so the field is pinned to the example's
-- | `Vesta.ScalarField` rather than carried as a parameter.
module Snarky.Example.Transaction.Monad
  ( TransactionF(..)
  , TRANSACTION
  , _transaction
  , getCurrentTransaction
  , AccountMapF(..)
  , ACCOUNT_MAP
  , _accountMap
  , getAccountId
  , TransferAdvice
  , TransferRow
  , runTransferM
  , runTransferCompileM
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.MerkleTree.Sparse (Address)
import Data.MerkleTree.Sparse as Sparse
import Data.Reflectable (class Reflectable)
import Effect (Effect)
import Effect.Exception (error, throwException)
import Effect.Ref (Ref, read, write)
import Partial.Unsafe (unsafeCrashWith)
import Run (EFFECT, Run)
import Run as Run
import Snarky.Circuit.MerkleTree (MERKLE, MerkleF(..), _merkle)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Ledger (Ledger, lookupAddress)
import Snarky.Example.Transaction.Types (SignedTransaction)
import Snarky.Example.Types (Account, PublicKey)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))

--------------------------------------------------------------------------------
-- | Advice effect for supplying the transaction being proven as a private
-- | witness. The pickled {source, target} statement does not carry the
-- | `SignedTransaction`; the prover conjures it in-circuit via `exists`,
-- | reading it from the advice row's handler.
data TransactionF a = GetCurrentTransaction (SignedTransaction Vesta.ScalarField -> a)

derive instance Functor TransactionF

type TRANSACTION r = (transaction :: TransactionF | r)

_transaction :: Proxy "transaction"
_transaction = Proxy

getCurrentTransaction :: forall r. Run (TRANSACTION + r) (SignedTransaction Vesta.ScalarField)
getCurrentTransaction = Run.lift _transaction (GetCurrentTransaction identity)

--------------------------------------------------------------------------------
-- | Advice effect for looking up account addresses from public keys.
-- |
-- | This lets circuits "conjure" an address from a public key during witness
-- | generation. The prover provides the mapping externally.
data AccountMapF (d :: Int) a = GetAccountId (PublicKey Vesta.ScalarField) (Address d -> a)

derive instance Functor (AccountMapF d)

type ACCOUNT_MAP d r = (accountMap :: AccountMapF d | r)

_accountMap :: Proxy "accountMap"
_accountMap = Proxy

getAccountId :: forall d r. PublicKey Vesta.ScalarField -> Run (ACCOUNT_MAP d + r) (Address d)
getAccountId pk = Run.lift _accountMap (GetAccountId pk identity)

--------------------------------------------------------------------------------
-- | The full advice row a transfer circuit's witnesses request from.
-- | Advice labels a transfer circuit's witnesses request (EFFECT is
-- | structural in circuit/witness rows, so it is not named here).
type TransferAdvice d =
  MERKLE Vesta.ScalarField (Account Vesta.ScalarField) d
    + ACCOUNT_MAP d
    + TRANSACTION
    + ()

-- | The interpreter-facing row: advice plus the EFFECT channel the
-- | solver/interpreters emit into.
type TransferRow d = MERKLE Vesta.ScalarField (Account Vesta.ScalarField) d + ACCOUNT_MAP d + TRANSACTION + EFFECT + ()

--------------------------------------------------------------------------------
-- Run-time advice interpreter

-- | Answers advice requests against a live ledger reference plus the
-- | per-prove transaction.
runTransferM
  :: forall d
   . Reflectable d Int
  => { currentTransaction :: Maybe (SignedTransaction Vesta.ScalarField), ledger :: Ref (Ledger d) }
  -> Run (TransferRow d) ~> Effect
runTransferM env = Run.runBaseEffect <<< Run.interpret
  ( Run.on _merkle merkleH
      (Run.on _accountMap accountMapH (Run.on _transaction transactionH Run.send))
  )
  where
  getLedger = Run.liftEffect (read env.ledger)

  die :: forall a. String -> Run (EFFECT + ()) a
  die = Run.liftEffect <<< throwException <<< error

  merkleH :: MerkleF Vesta.ScalarField (Account Vesta.ScalarField) d ~> Run (EFFECT + ())
  merkleH = case _ of
    GetElement addr k -> getLedger >>= \{ tree } ->
      case Sparse.get tree addr of
        Just v -> pure (k { value: v, path: Sparse.getWitness addr tree })
        Nothing -> die "getElement: address not set in sparse tree"
    GetPath addr k -> getLedger <#> \{ tree } ->
      k (Sparse.getWitness addr tree)
    SetValue addr v k -> getLedger >>= \ledger ->
      case Sparse.set addr v ledger.tree of
        Just tree' -> Run.liftEffect (write (ledger { tree = tree' }) env.ledger) $> k
        Nothing -> die "setValue: invalid address"

  accountMapH :: AccountMapF d ~> Run (EFFECT + ())
  accountMapH (GetAccountId pk k) = getLedger >>= \ledger ->
    case lookupAddress ledger pk of
      Just addr -> pure (k addr)
      Nothing -> die "getAccountId: public key not found in account map"

  transactionH :: TransactionF ~> Run (EFFECT + ())
  transactionH (GetCurrentTransaction k) = case env.currentTransaction of
    Just tx -> pure (k tx)
    Nothing -> die "getCurrentTransaction: no current transaction set"

--------------------------------------------------------------------------------
-- Compile-time advice interpreter (crashes on any request)

-- | Compilation discards `exists` bodies, so no advice request is ever
-- | served; any request firing here is a bug.
runTransferCompileM :: forall d. Run (TransferRow d) ~> Effect
runTransferCompileM = Run.runBaseEffect <<< Run.interpret
  ( Run.on _merkle merkleH
      (Run.on _accountMap accountMapH (Run.on _transaction transactionH Run.send))
  )
  where
  merkleH :: MerkleF Vesta.ScalarField (Account Vesta.ScalarField) d ~> Run (EFFECT + ())
  merkleH = case _ of
    GetElement _ _ -> unsafeCrashWith "the impossible happened! unhandled request: getElement"
    GetPath _ _ -> unsafeCrashWith "the impossible happened! unhandled request: getPath"
    SetValue _ _ _ -> unsafeCrashWith "the impossible happened! unhandled request: setValue"

  accountMapH :: AccountMapF d ~> Run (EFFECT + ())
  accountMapH (GetAccountId _ _) = unsafeCrashWith "the impossible happened! unhandled request: getAccountId"

  transactionH :: TransactionF ~> Run (EFFECT + ())
  transactionH (GetCurrentTransaction _) = unsafeCrashWith "the impossible happened! unhandled request: getCurrentTransaction"
