module Snarky.Example.Block
  ( Block(..)
  , SnarkWork(..)
  , scanlM
  ) where

import Prelude

import Control.Monad.State (evalStateT, get, lift, put)
import Data.Traversable (class Traversable, traverse)
import Data.Vector (Vector)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Transaction (SignedTransaction, Statement)

newtype Block = Block
  { transactions :: Vector 8 (SignedTransaction Vesta.ScalarField)
  }

data SnarkWork
  = Transaction (Statement Vesta.ScalarField)
  | Merge (Statement Vesta.ScalarField) (Statement Vesta.ScalarField)

-- type State = 
--   { Map (Digest Vesta.ScalarField) 

--   }

-- processBlock
--   :: forall d
--    . Reflectable d Int
--   => ChainId
--   -> Block
--   -> Ledger d Vesta.ScalarField 
--   -> Effect
--       { snarkWork :: SnarkWork
--       , ledger :: Ledger d Vesta.ScalarField
--       }
-- processBlock chainId (Block txs) ledger = do
--   let
--     init = { root: root ledger.tree, ledger }
--     f acc tx = do
--       ledger' <- applyTx chainId tx ledger 
--       let root' = root ledger'.tree
--       pure { root: root', ledger: ledger' }
--   states <- scanlM f init txs

scanlM
  :: forall t m a b
   . Traversable t
  => Monad m
  => (b -> a -> m b)
  -> b
  -> t a
  -> m (t b)
scanlM f seed t = evalStateT (traverse step t) seed
  where
  step a = do
    acc <- get
    b <- lift (f acc a)
    put b
    pure b