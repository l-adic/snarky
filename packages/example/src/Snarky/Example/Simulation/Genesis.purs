-- | Genesis-state generation for the simulation: mint a fresh ledger of
-- | funded accounts together with the `Keystore` that can sign for them.
module Snarky.Example.Simulation.Genesis
  ( genGenesisLedger
  ) where

import Prelude

import Data.Array ((..))
import Data.Foldable (foldl)
import Data.Map as Map
import Data.Maybe (fromJust)
import Data.MerkleTree.Sparse as Sparse
import Data.Reflectable (class Reflectable)
import Data.Traversable (for)
import Partial.Unsafe (unsafePartial)
import Snarky.Curves.Class (fromInt, generator, scalarMul, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Snarky.Example.Ledger (Ledger)
import Snarky.Example.Simulation.Keystore (Keystore)
import Snarky.Example.Types (Account(..), PublicKey(..), mkAmount)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen, chooseInt)

-- | Mint a fresh ledger of `numAccounts` accounts, each with a Pallas
-- | keypair (public key = `[sk]·G`), a large balance, and nonce 0.
-- | Addresses are assigned sequentially (0, 1, 2, ...) like Mina does.
-- | Returns the ledger together with the wallet `keys` (public key →
-- | signing key) — the signing keys are NOT part of the ledger, but the
-- | simulation needs them to sign on a sender's behalf.
-- |
-- | Curve-bound (the public keys are Pallas points), hence pinned to
-- | `Vesta.ScalarField`.
genGenesisLedger
  :: forall d
   . Reflectable d Int
  => Int
  -> Gen { ledger :: Ledger d, keys :: Keystore }
genGenesisLedger numAccounts = do
  accounts <- for (1 .. numAccounts) \_ -> do
    privateKey <- arbitrary :: Gen Pallas.ScalarField
    balanceInt <- chooseInt 1000000 9999999
    let
      pkPoint = unsafePartial fromJust $ toAffine (scalarMul privateKey (generator :: PallasG))
      publicKey = PublicKey (AffinePoint { x: pkPoint.x, y: pkPoint.y })
      account = Account
        { publicKey
        , tokenBalance: unsafePartial fromJust $ mkAmount (fromInt balanceInt)
        , nonce: zero
        }
    pure { privateKey, publicKey, account }

  let
    insert acc { privateKey, publicKey, account } =
      let
        addr = Sparse.Address acc.ledger.nextAddress
      in
        { ledger: acc.ledger
            { tree = unsafePartial fromJust $ Sparse.set addr account acc.ledger.tree
            , accountMap = Map.insert publicKey addr acc.ledger.accountMap
            , nextAddress = acc.ledger.nextAddress + one
            }
        , keys: Map.insert publicKey privateKey acc.keys
        }

    initial =
      { ledger:
          { tree: Sparse.empty
          , accountMap: Map.empty
          , nextAddress: zero
          }
      , keys: Map.empty
      }

  pure $ foldl insert initial accounts
