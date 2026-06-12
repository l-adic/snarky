-- | Block generation for the simulation: fill a `Block` with sequentially
-- | valid transfers — each transaction is generated (and signed) against the
-- | ledger state left by applying the previous one, the same fold
-- | `processBlock` later re-applies for witness extraction.
module Snarky.Example.Simulation.Block
  ( generateBlock
  ) where

import Prelude

import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import Effect (Effect)
import Mina.ChainId (ChainId)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Block (Block(..))
import Snarky.Example.Ledger (Ledger)
import Snarky.Example.Simulation.Keystore (Keystore)
import Snarky.Example.Simulation.Transaction (genValidSignedTransaction)
import Snarky.Example.Transaction (SignedTransaction, applyTx)
import Test.QuickCheck.Gen (randomSampleOne)

-- | Generate a block of sequentially-valid transfers from the given ledger
-- | state. The block size comes from the `Block` type itself
-- | (`Vector.unfoldM` fills exactly its `transactions` vector, threading
-- | the ledger as the accumulator), so there is no size to pass.
generateBlock
  :: forall d
   . Reflectable d Int
  => ChainId
  -> Keystore
  -> Ledger d
  -> Effect Block
generateBlock chainId keys ledger0 = do
  Tuple transactions _ <- Vector.unfoldM step ledger0
  pure $ Block { transactions }
  where
  step :: Ledger d -> Effect (Tuple (SignedTransaction Vesta.ScalarField) (Ledger d))
  step l = do
    tx <- randomSampleOne (genValidSignedTransaction chainId l keys)
    l' <- applyTx chainId tx l
    pure (Tuple tx l')
