module Snarky.Example.Block
  ( Block(..)
  , TxSnarkWork
  , processBlock
  ) where

import Prelude

import Data.MerkleTree.Sparse (root)
import Data.MerkleTree.Sparse.Mask as Mask
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Mina.ChainId (ChainId)
import Snarky.Circuit.Kimchi.Utils (mapAccumM)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Ledger (Ledger, Mask)
import Snarky.Example.Transaction (SignedTransaction, Statement(..), applyTx)
import Snarky.Example.Transaction.Unchecked (touchedAccounts)

newtype Block = Block
  { transactions :: Vector 4 (SignedTransaction Vesta.ScalarField)
  }

type TxSnarkWork d =
  { mask :: Mask d
  , tx :: SignedTransaction Vesta.ScalarField
  , statement :: Statement Vesta.ScalarField
  }

processBlock
  :: forall d
   . Reflectable d Int
  => ChainId
  -> Ledger d
  -> Block
  -> Effect
       { ledger :: Ledger d
       , snarkWork :: Array (TxSnarkWork d)
       }
processBlock chainId ledger (Block { transactions }) = do
  Tuple jobs finalLedger <- mapAccumM step ledger transactions
  pure { ledger: finalLedger, snarkWork: Vector.toUnfoldable jobs }
  where
  step l tx = do
    let mask = Mask.fromSubset l.tree (touchedAccounts l tx)
    l' <- applyTx chainId tx l
    let statement = Statement { source: root l.tree, target: root l'.tree }
    pure (Tuple { mask, tx, statement } l')