module Snarky.Example.Env where

import Prelude

import Data.Array (range)
import Data.Foldable (for_)
import Data.Reflectable (class Reflectable)
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Mina.ChainId (ChainId)
import Snarky.Backend.Kimchi.Class (addLagrangeBasis, createCRS)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Ledger (Ledger)
import Snarky.Example.Ledger as Ledger
import Snarky.Example.Transaction.Checked (CompiledTx, compileTxCircuit)

type Config =
  { pallasSrs :: CRS PallasG
  , vestaSrs :: CRS VestaG
  , chainId :: ChainId
  }

mkConfig
  :: ChainId
  -> Effect Config
mkConfig chainId = do
  pallasSrs <- createCRS @Pallas.ScalarField
  vestaSrs <- createCRS @Vesta.ScalarField
  for_ (range 14 16) (addLagrangeBasis vestaSrs)
  for_ (range 12 15) (addLagrangeBasis pallasSrs)
  pure { pallasSrs, vestaSrs, chainId }

type Env d =
  { chainId :: ChainId
  , compiledTx :: CompiledTx d
  , ledger :: Ref (Ledger d)
  }

mkEnv
  :: forall d
   . Reflectable d Int
  => Config
  -> Effect (Env d)
mkEnv cfg = do
  ledger <- Ref.new $ Ledger.empty @d
  compiledTx <- compileTxCircuit cfg.chainId { pallasSrs: cfg.pallasSrs, vestaSrs: cfg.vestaSrs }
  pure { ledger, compiledTx, chainId: cfg.chainId }