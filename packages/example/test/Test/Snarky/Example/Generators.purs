-- | Random transaction *scenarios* for the example specs: pick a
-- | sender/receiver pair and produce either a valid transfer (amount below
-- | the sender's balance) or an overdraft (amount above it, so the circuit
-- | must reject). These are test inputs, not node behaviour — the ledger
-- | lives in `Snarky.Example.Ledger` and `sign` in
-- | `Snarky.Example.Transaction`. The signing `keys` are the wallet map
-- | returned alongside the ledger by `genLedger`.
module Test.Snarky.Example.Generators
  ( genLedger
  , genDistinctPublicKeys
  , genValidSignedTransaction
  , genOverdraftSignedTransaction
  ) where

import Prelude

import Data.Array (length, (!!), (..))
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (fromJust)
import Data.MerkleTree.Sparse as Sparse
import Data.Reflectable (class Reflectable)
import Data.Set as Set
import Data.Traversable (for)
import Mina.ChainId (ChainId)
import Partial.Unsafe (unsafePartial)
import Snarky.Circuit.DSL (F(..))
import Snarky.Curves.Class (fromBigInt, fromInt, generator, scalarMul, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Ledger (Ledger, balanceOf, getAccount, lookupAddress)
import Snarky.Example.Transaction (SignedTransaction, sign)
import Snarky.Example.Types (Account(..), PublicKey(..), mkAmount)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen, chooseInt, suchThat)
import Test.Snarky.Example.Utils (chooseBigInt)

type Keystore = Map (PublicKey (F Vesta.ScalarField)) Pallas.ScalarField

-- | Pick two distinct public keys from the ledger's account index.
genDistinctPublicKeys
  :: forall d
   . Ledger d Vesta.ScalarField
  -> Gen { fromPk :: PublicKey (F Vesta.ScalarField), toPk :: PublicKey (F Vesta.ScalarField) }
genDistinctPublicKeys ledger = do
  let
    keys :: Array (PublicKey (F Vesta.ScalarField))
    keys = Set.toUnfoldable $ Map.keys ledger.accountMap
    maxIdx = length keys - 1
  fromIdx <- chooseInt 0 maxIdx
  toIdx <- chooseInt 0 maxIdx `suchThat` (\i -> i /= fromIdx)
  pure
    { fromPk: unsafePartial fromJust $ keys !! fromIdx
    , toPk: unsafePartial fromJust $ keys !! toIdx
    }

-- | Test-harness lookup: a sender's signing key (from the wallet
-- | "registry"), current nonce, and spendable balance. A real signer just
-- | holds their own key — this registry only exists so the random
-- | generators can sign as whichever account they happened to sample.
senderInfo
  :: forall d
   . Ledger d Vesta.ScalarField
  -> Keystore
  -> PublicKey (F Vesta.ScalarField)
  -> { privateKey :: F Pallas.ScalarField, nonce :: F Vesta.ScalarField, balance :: F Vesta.ScalarField }
senderInfo ledger wallet fromPk =
  let
    fromAddr = unsafePartial fromJust $ lookupAddress ledger fromPk
    Account senderAcc = unsafePartial fromJust $ getAccount ledger fromAddr
  in
    { privateKey: F (unsafePartial fromJust $ Map.lookup fromPk wallet)
    , nonce: senderAcc.nonce
    , balance: balanceOf senderAcc.tokenBalance
    }

-- | Generate a valid, signed transfer against the given ledger + wallet,
-- | signed under `chainId` (must match the verifier's chain id).
genValidSignedTransaction
  :: forall d
   . ChainId
  -> Ledger d Vesta.ScalarField
  -> Keystore
  -> Gen (SignedTransaction (F Vesta.ScalarField))
genValidSignedTransaction chainId ledger wallet = do
  { fromPk, toPk } <- genDistinctPublicKeys ledger
  let { privateKey, nonce, balance } = senderInfo ledger wallet fromPk
  -- Pick a valid transfer amount (less than the sender's balance).
  amountInt <- chooseBigInt one (max one (toBigInt balance - one))
  let amount = unsafePartial fromJust $ mkAmount (fromBigInt amountInt)
  pure $ sign privateKey chainId nonce { amount, to: toPk }

-- | Generate a correctly-signed transfer whose amount exceeds the
-- | sender's balance (so the in-circuit underflow check must reject it).
genOverdraftSignedTransaction
  :: forall d
   . ChainId
  -> Ledger d Vesta.ScalarField
  -> Keystore
  -> Gen (SignedTransaction (F Vesta.ScalarField))
genOverdraftSignedTransaction chainId ledger wallet = do
  { fromPk, toPk } <- genDistinctPublicKeys ledger
  let
    { privateKey, nonce, balance } = senderInfo ledger wallet fromPk
    amount = unsafePartial fromJust $ mkAmount (balance + one)
  pure $ sign privateKey chainId nonce { amount, to: toPk }

-- | Mint a fresh ledger of `numAccounts` accounts, each with a Pallas
-- | keypair (public key = `[sk]·G`), a large balance, and nonce 0.
-- | Addresses are assigned sequentially (0, 1, 2, ...) like Mina does.
-- | Returns the ledger together with the wallet `keys` (public key →
-- | signing key) — the signing keys are NOT part of the ledger, but a
-- | test/wallet needs them to sign on a sender's behalf.
-- |
-- | Curve-bound (the public keys are Pallas points), hence pinned to
-- | `Vesta.ScalarField`.
genLedger
  :: forall d
   . Reflectable d Int
  => Int
  -> Gen { ledger :: Ledger d Vesta.ScalarField, keys :: Keystore }
genLedger numAccounts = do
  accounts <- for (1 .. numAccounts) \_ -> do
    privateKey <- arbitrary :: Gen Pallas.ScalarField
    balanceInt <- chooseInt 1000000 9999999
    let
      pkPoint = unsafePartial fromJust $ toAffine (scalarMul privateKey (generator :: PallasG))
      publicKey = PublicKey { x: F pkPoint.x, y: F pkPoint.y }
      account = Account
        { publicKey
        , tokenBalance: unsafePartial fromJust $ mkAmount (fromInt balanceInt)
        , nonce: F zero
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
