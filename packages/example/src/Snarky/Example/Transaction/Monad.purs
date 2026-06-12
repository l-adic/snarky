-- | The transfer circuit's advice effects and their production interpreter.
-- |
-- | `runTransferMaskM` answers a circuit's advice requests (`MERKLE` /
-- | `ACCOUNT_MAP` / `TRANSACTION`) against a `Mask` — the minimal
-- | sparse-tree slice a snark worker receives — plus the particular
-- | transaction being proven. The transaction is NOT ledger state — it is
-- | the "arrow" mapping one ledger to the next — so it rides the handler's
-- | environment as an explicit per-prove input alongside the (mutable)
-- | mask reference:
-- |
-- |   { currentTransaction :: Maybe (SignedTransaction Vesta.ScalarField)
-- |   , mask :: Ref (Mask d) }
-- |
-- | A base prove supplies `currentTransaction = Just tx`; a merge prove
-- | (which witnesses no transaction) supplies `Nothing`. (Compilation
-- | needs no handler at all — pass `Snarky.Backend.Advice.badAdvice`.)
-- | The handler is a direct `VariantF row ~> Effect` function the
-- | interpreters call per advice op (no Run handler chain).
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
  , runTransferMaskM
  ) where

import Prelude

import Data.Functor.Variant (case_, on)
import Data.Maybe (Maybe(..))
import Data.MerkleTree.Sparse (Address)
import Data.MerkleTree.Sparse.Mask as Mask
import Data.Reflectable (class Reflectable)
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Ref (Ref, modify_, read)
import Run (Run)
import Run as Run
import Snarky.Backend.Advice (AdviceHandler(..))
import Snarky.Circuit.MerkleTree (MERKLE, MerkleF(..), _merkle)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Ledger (Mask)
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

--------------------------------------------------------------------------------
-- Prove-time advice interpreter

-- | Answers advice requests against a mutable mask reference plus the
-- | per-prove transaction (the witness mutates the mask in place as the
-- | circuit applies the transfer).
runTransferMaskM
  :: forall d
   . Reflectable d Int
  => { currentTransaction :: Maybe (SignedTransaction Vesta.ScalarField), mask :: Ref (Mask d) }
  -> AdviceHandler (TransferAdvice d)
runTransferMaskM env = AdviceHandler
  ( case_
      # on _transaction transactionH
      # on _accountMap accountMapH
      # on _merkle merkleH
  )
  where
  getMask = read env.mask

  merkleH :: MerkleF Vesta.ScalarField (Account Vesta.ScalarField) d ~> Effect
  merkleH = case _ of
    GetElement addr k -> getMask >>= \mask ->
      case Mask.get addr mask of
        Just v -> pure (k { value: v, path: Mask.getPath addr mask })
        Nothing -> throw "getElement: address not present in the witness"
    GetPath addr k -> getMask <#> \mask ->
      k (Mask.getPath addr mask)
    SetValue addr v k -> modify_ (Mask.set addr v) env.mask $> k

  accountMapH :: AccountMapF d ~> Effect
  accountMapH (GetAccountId pk k) = getMask >>= \mask ->
    case Mask.findIndex pk mask of
      Just addr -> pure (k addr)
      Nothing -> throw "getAccountId: public key not present in the witness"

  transactionH :: TransactionF ~> Effect
  transactionH (GetCurrentTransaction k) = case env.currentTransaction of
    Just tx -> pure (k tx)
    Nothing -> throw "getCurrentTransaction: no current transaction set"
