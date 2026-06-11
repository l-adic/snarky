-- | Mask-backed advice interpreter: like `runTransferM`, but answers
-- | Merkle/account requests from a `Mask` (the minimal sparse-tree slice a
-- | snark worker receives) instead of the full ledger.
module Snarky.Example.Transaction.MaskMonad
  ( runTransferMaskM
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.MerkleTree.Sparse.Mask as Mask
import Data.Reflectable (class Reflectable)
import Effect (Effect)
import Effect.Exception (error, throwException)
import Effect.Ref (Ref, modify_, read)
import Run (EFFECT, Run)
import Run as Run
import Snarky.Circuit.MerkleTree (MerkleF(..), _merkle)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Ledger (Mask)
import Snarky.Example.Transaction.Monad (AccountMapF(..), TransactionF(..), TransferRow, _accountMap, _transaction)
import Snarky.Example.Transaction.Types (SignedTransaction)
import Snarky.Example.Types (Account)
import Type.Row (type (+))

-- | Answers advice requests against a mutable mask reference plus the
-- | per-prove transaction (the witness mutates the mask in place as the
-- | circuit applies the transfer).
runTransferMaskM
  :: forall d
   . Reflectable d Int
  => { currentTransaction :: Maybe (SignedTransaction Vesta.ScalarField), mask :: Ref (Mask d) }
  -> Run (TransferRow d) ~> Effect
runTransferMaskM env = Run.runBaseEffect <<< Run.interpret
  ( Run.on _merkle merkleH
      (Run.on _accountMap accountMapH (Run.on _transaction transactionH Run.send))
  )
  where
  getMask = Run.liftEffect (read env.mask)

  die :: forall a. String -> Run (EFFECT + ()) a
  die = Run.liftEffect <<< throwException <<< error

  merkleH :: MerkleF Vesta.ScalarField (Account Vesta.ScalarField) d ~> Run (EFFECT + ())
  merkleH = case _ of
    GetElement addr k -> getMask >>= \mask ->
      case Mask.get addr mask of
        Just v -> pure (k { value: v, path: Mask.getPath addr mask })
        Nothing -> die "getElement: address not present in the witness"
    GetPath addr k -> getMask <#> \mask ->
      k (Mask.getPath addr mask)
    SetValue addr v k -> Run.liftEffect (modify_ (Mask.set addr v) env.mask) $> k

  accountMapH :: AccountMapF d ~> Run (EFFECT + ())
  accountMapH (GetAccountId pk k) = getMask >>= \mask ->
    case Mask.findIndex pk mask of
      Just addr -> pure (k addr)
      Nothing -> die "getAccountId: public key not present in the witness"

  transactionH :: TransactionF ~> Run (EFFECT + ())
  transactionH (GetCurrentTransaction k) = case env.currentTransaction of
    Just tx -> pure (k tx)
    Nothing -> die "getCurrentTransaction: no current transaction set"
