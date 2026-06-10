-- | Block generation for the simulation: fill a `Block` with sequentially
-- | valid transfers — each transaction is generated (and signed) against the
-- | ledger state left by applying the previous one, the same fold
-- | `processBlock` later re-applies for witness extraction.
module Snarky.Example.Simulation.Block
  ( generateBlock
  ) where

import Prelude

import Control.Monad.State (StateT, evalStateT, get, lift, put)
import Data.Reflectable (class Reflectable)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Class (liftEffect)
import Mina.ChainId (ChainId)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Block (Block(..))
import Snarky.Example.Ledger (Ledger)
import Snarky.Example.Simulation.Keystore (Keystore)
import Snarky.Example.Simulation.Transaction (genValidSignedTransaction)
import Snarky.Example.Transaction (SignedTransaction, applyTx)
import Test.QuickCheck.Gen (randomSampleOne)

-- | Generate a block of sequentially-valid transfers from the given ledger
-- | state. The block size comes from the `Block` type itself (`Vector.generateA`
-- | fills exactly its `transactions` vector), so there is no size to pass.
generateBlock
  :: forall d
   . Reflectable d Int
  => ChainId
  -> Keystore
  -> Ledger d
  -> Effect Block
generateBlock chainId keys ledger0 = do
  transactions <- evalStateT (Vector.generateA \_ -> step) ledger0
  pure $ Block { transactions }
  where
  step :: StateT (Ledger d) Effect (SignedTransaction Vesta.ScalarField)
  step = do
    l <- get
    tx <- liftEffect $ randomSampleOne (genValidSignedTransaction chainId l keys)
    l' <- lift $ applyTx chainId tx l
    put l'
    pure tx
