-- | The simulation's wallet registry: a map from every simulated account's
-- | public key to its Pallas signing key. A real signer holds only their own
-- | key — this registry exists so the simulation can sign on behalf of
-- | whichever account it samples as a sender.
module Snarky.Example.Simulation.Keystore
  ( Keystore
  , senderInfo
  ) where

import Prelude

import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (fromJust)
import Partial.Unsafe (unsafePartial)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Ledger (Ledger, balanceOf, getAccount, lookupAddress)
import Snarky.Example.Types (Account(..), PublicKey)

type Keystore = Map (PublicKey Vesta.ScalarField) Pallas.ScalarField

-- | Look up everything needed to sign as `fromPk`: its signing key (from the
-- | registry), current nonce, and spendable balance (from the ledger).
senderInfo
  :: forall d
   . Ledger d
  -> Keystore
  -> PublicKey Vesta.ScalarField
  -> { privateKey :: Pallas.ScalarField, nonce :: Vesta.ScalarField, balance :: Vesta.ScalarField }
senderInfo ledger wallet fromPk =
  let
    fromAddr = unsafePartial fromJust $ lookupAddress ledger fromPk
    Account senderAcc = unsafePartial fromJust $ getAccount ledger fromAddr
  in
    { privateKey: unsafePartial fromJust $ Map.lookup fromPk wallet
    , nonce: senderAcc.nonce
    , balance: balanceOf senderAcc.tokenBalance
    }
