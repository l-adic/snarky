-- | Mask-backed advice interpreter: like `runTransferM`, but answers
-- | Merkle/account requests from a `Mask` (the minimal sparse-tree slice a
-- | snark worker receives) instead of the full ledger.
module Snarky.Example.Transaction.MaskMonad
  ( runTransferMaskM
  ) where

import Prelude

import Data.Functor.Variant (case_, on)
import Data.Maybe (Maybe(..))
import Data.MerkleTree.Sparse.Mask as Mask
import Data.Reflectable (class Reflectable)
import Effect (Effect)
import Effect.Exception (error, throwException)
import Effect.Ref (Ref, modify_, read)
import Snarky.Backend.Advice (AdviceHandler(..))
import Snarky.Circuit.MerkleTree (MerkleF(..), _merkle)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Ledger (Mask)
import Snarky.Example.Transaction.Monad (AccountMapF(..), TransactionF(..), TransferAdvice, _accountMap, _transaction)
import Snarky.Example.Transaction.Types (SignedTransaction)
import Snarky.Example.Types (Account)

-- | Answers advice requests against a mutable mask reference plus the
-- | per-prove transaction (the witness mutates the mask in place as the
-- | circuit applies the transfer).
runTransferMaskM
  :: forall d
   . Reflectable d Int
  => { currentTransaction :: Maybe (SignedTransaction Vesta.ScalarField), mask :: Ref (Mask d) }
  -> AdviceHandler (TransferAdvice d)
runTransferMaskM env = AdviceHandler
  (on _merkle merkleH (on _accountMap accountMapH (on _transaction transactionH case_)))
  where
  getMask = read env.mask

  die :: forall a. String -> Effect a
  die = throwException <<< error

  merkleH :: MerkleF Vesta.ScalarField (Account Vesta.ScalarField) d ~> Effect
  merkleH = case _ of
    GetElement addr k -> getMask >>= \mask ->
      case Mask.get addr mask of
        Just v -> pure (k { value: v, path: Mask.getPath addr mask })
        Nothing -> die "getElement: address not present in the witness"
    GetPath addr k -> getMask <#> \mask ->
      k (Mask.getPath addr mask)
    SetValue addr v k -> modify_ (Mask.set addr v) env.mask $> k

  accountMapH :: AccountMapF d ~> Effect
  accountMapH (GetAccountId pk k) = getMask >>= \mask ->
    case Mask.findIndex pk mask of
      Just addr -> pure (k addr)
      Nothing -> die "getAccountId: public key not present in the witness"

  transactionH :: TransactionF ~> Effect
  transactionH (GetCurrentTransaction k) = case env.currentTransaction of
    Just tx -> pure (k tx)
    Nothing -> die "getCurrentTransaction: no current transaction set"
