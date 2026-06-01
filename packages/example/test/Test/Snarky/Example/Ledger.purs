-- | Shared ledger fixtures for the example transaction circuits: account
-- | tree generation, signed-transfer construction, and a pure
-- | `applyTransfer` mirror of `processTransaction`'s ledger effect. Used
-- | by both the in-circuit `Test.Snarky.Example.Circuits` spec and the
-- | pickled `Test.Snarky.Example.TransactionSnark` spec.
module Test.Snarky.Example.Ledger
  ( mkAmount
  , balanceOf
  , numAccounts
  , genTreeWithAccounts
  , genDistinctPublicKeys
  , signedTransfer
  , genValidSignedTransaction
  , genOverdraftSignedTransaction
  , applyTransfer
  ) where

import Prelude

import Data.Array (length, (!!), (..))
import Data.Foldable (foldl)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust)
import Data.MerkleTree.Sparse as Sparse
import Data.Newtype (un)
import Data.Reflectable (class Reflectable)
import Data.Set as Set
import Data.Traversable (for)
import Mina.ChainId (ChainId(..))
import Partial.Unsafe (unsafePartial)
import Snarky.Circuit.DSL (F(..), fromField, toField)
import Snarky.Curves.Class (fromBigInt, fromInt, generator, scalarMul, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Types (Account(..), PublicKey(..), SignedTransaction(..), TokenAmount(..), Transaction(..), Transfer(..), signTransaction)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen, chooseInt, suchThat)
import Test.Snarky.Example.Monad (TransferState, lookupAddress)
import Test.Snarky.Example.Utils (chooseBigInt)

type SF = Vesta.ScalarField

-- | Build a token amount from a field value (balances stay well under 2^128).
mkAmount :: SF -> TokenAmount (F SF)
mkAmount v = TokenAmount (unsafePartial fromJust (fromField @128 (F v)))

-- | Read the underlying field value of a token amount.
balanceOf :: TokenAmount (F SF) -> SF
balanceOf tb = un F (toField (un TokenAmount tb))

-- | Number of accounts to generate for testing
numAccounts :: Int
numAccounts = 10

-- | Generate a sparse merkle tree of accounts, each with a fresh Pallas
-- | keypair (public key = `[sk]·G`), a large balance, and nonce 0.
-- | Addresses are assigned sequentially (0, 1, 2, ...) like Mina does.
-- | The signing keys are retained so the generators can sign on a
-- | sender's behalf.
genTreeWithAccounts
  :: forall d
   . Reflectable d Int
  => Gen (TransferState d SF)
genTreeWithAccounts = do
  accounts <- for (1 .. numAccounts) \_ -> do
    privateKey <- arbitrary :: Gen Pallas.ScalarField
    balanceInt <- chooseInt 1000000 9999999
    let
      pkPoint = unsafePartial fromJust $ toAffine (scalarMul privateKey (generator :: PallasG))
      publicKey = PublicKey { x: F pkPoint.x, y: F pkPoint.y }
      account = Account
        { publicKey
        , tokenBalance: mkAmount (fromInt balanceInt)
        , nonce: F zero
        }
    pure { privateKey, publicKey, account }

  let
    insertAccount st { privateKey, publicKey, account } =
      let
        addr = Sparse.Address st.nextAddress
      in
        st
          { tree = unsafePartial fromJust $ Sparse.set addr account st.tree
          , accountMap = Map.insert publicKey addr st.accountMap
          , privateKeys = Map.insert publicKey privateKey st.privateKeys
          , nextAddress = st.nextAddress + one
          }

    initialSt =
      { tree: Sparse.empty
      , accountMap: Map.empty
      , privateKeys: Map.empty
      , nextAddress: zero
      , currentTransaction: Nothing
      }

  pure $ foldl insertAccount initialSt accounts

-- | Pick two distinct public keys from the account map.
genDistinctPublicKeys
  :: forall d
   . TransferState d SF
  -> Gen { fromPk :: PublicKey (F SF), toPk :: PublicKey (F SF) }
genDistinctPublicKeys state = do
  let
    keys :: Array (PublicKey (F SF))
    keys = Set.toUnfoldable $ Map.keys state.accountMap
    maxIdx = length keys - 1
  fromIdx <- chooseInt 0 maxIdx
  toIdx <- chooseInt 0 maxIdx `suchThat` (\i -> i /= fromIdx)
  pure
    { fromPk: unsafePartial fromJust $ keys !! fromIdx
    , toPk: unsafePartial fromJust $ keys !! toIdx
    }

-- | Build and sign a transaction transferring `amount` from one account
-- | to another, using the sender's stored signing key and current nonce.
signedTransfer
  :: forall d
   . TransferState d SF
  -> PublicKey (F SF)
  -> PublicKey (F SF)
  -> TokenAmount (F SF)
  -> SignedTransaction (F SF)
signedTransfer state fromPk toPk amount =
  let
    fromAddr = unsafePartial fromJust $ lookupAddress state fromPk
    Account senderAcc = unsafePartial fromJust $ Sparse.get state.tree fromAddr
    privateKey = unsafePartial fromJust $ Map.lookup fromPk state.privateKeys
    transaction = Transaction
      { nonce: senderAcc.nonce
      , transfer: Transfer { from: fromPk, to: toPk, amount }
      }
  in
    SignedTransaction { signature: signTransaction privateKey Mainnet transaction, transaction }

-- | Generate a valid, signed transfer for a given state.
genValidSignedTransaction
  :: forall d
   . TransferState d SF
  -> Gen (SignedTransaction (F SF))
genValidSignedTransaction state = do
  { fromPk, toPk } <- genDistinctPublicKeys state
  let
    fromAddr = unsafePartial fromJust $ lookupAddress state fromPk
    Account senderAcc = unsafePartial fromJust $ Sparse.get state.tree fromAddr
    senderBalance = balanceOf senderAcc.tokenBalance
  -- Pick a valid transfer amount (less than the sender's balance).
  amountInt <- chooseBigInt one (max one (toBigInt senderBalance - one))
  pure $ signedTransfer state fromPk toPk (mkAmount (fromBigInt amountInt))

-- | Generate a correctly-signed transfer whose amount exceeds the
-- | sender's balance (so the in-circuit underflow check must reject it).
genOverdraftSignedTransaction
  :: forall d
   . TransferState d SF
  -> Gen (SignedTransaction (F SF))
genOverdraftSignedTransaction state = do
  { fromPk, toPk } <- genDistinctPublicKeys state
  let
    fromAddr = unsafePartial fromJust $ lookupAddress state fromPk
    Account senderAcc = unsafePartial fromJust $ Sparse.get state.tree fromAddr
    senderBalance = balanceOf senderAcc.tokenBalance
  pure $ signedTransfer state fromPk toPk (mkAmount (senderBalance + one))

-- | Pure mirror of `processTransaction`'s ledger effect: apply a signed
-- | transfer to a state, returning the new state. Debits the sender (and
-- | bumps its nonce) and credits the receiver. The resulting tree's root
-- | is the `target` ledger digest for the corresponding base statement.
-- | (The in-circuit `processTransaction` is checked against this exact
-- | logic by the `Test.Snarky.Example.Circuits` quickcheck spec.)
applyTransfer
  :: forall d
   . Reflectable d Int
  => TransferState d SF
  -> SignedTransaction (F SF)
  -> TransferState d SF
applyTransfer state (SignedTransaction { transaction: Transaction { transfer: Transfer { from, to, amount } } }) =
  let
    fromAddr = unsafePartial fromJust $ lookupAddress state from
    toAddr = unsafePartial fromJust $ lookupAddress state to

    Account senderAcc = unsafePartial fromJust $ Sparse.get state.tree fromAddr
    Account receiverAcc = unsafePartial fromJust $ Sparse.get state.tree toAddr

    amt = balanceOf amount
    F senderNonce = senderAcc.nonce

    newSenderAcc = Account senderAcc
      { tokenBalance = mkAmount (balanceOf senderAcc.tokenBalance - amt)
      , nonce = F (senderNonce + one)
      }
    newReceiverAcc = Account receiverAcc
      { tokenBalance = mkAmount (balanceOf receiverAcc.tokenBalance + amt) }

    tree' = unsafePartial fromJust $ Sparse.set fromAddr newSenderAcc state.tree
    tree'' = unsafePartial fromJust $ Sparse.set toAddr newReceiverAcc tree'
  in
    state { tree = tree'' }
