module Test.Snarky.Example.Circuits
  ( spec
  ) where

import Prelude

import Data.Array (length, (!!), (..))
import Data.Foldable (foldl, for_)
import Data.Map as Map
import Data.Maybe (fromJust)
import Data.MerkleTree.Sparse as Sparse
import Data.Newtype (un)
import Data.Reflectable (class Reflectable, reifyType)
import Data.Set as Set
import Data.Traversable (for)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Class.Console as Console
import Effect.Ref (write)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)
import Mina.ChainId (ChainId(..))
import Partial.Unsafe (unsafePartial)
import Snarky.Backend.Compile (compile, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, const_, fromField, toField)
import Snarky.Circuit.Kimchi (verifyCircuitM)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Constraint.Kimchi (KimchiConstraint, eval, initialState)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (fromBigInt, fromInt, generator, scalarMul, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Circuits (class AccountMapM, processTransaction)
import Snarky.Example.Types (Account(..), PublicKey(..), SignedTransaction(..), TokenAmount(..), Transaction(..), Transfer(..), signTransaction)
import Test.QuickCheck (arbitrary, quickCheck')
import Test.QuickCheck.Gen (Gen, chooseInt, randomSampleOne, suchThat)
import Test.Snarky.Circuit.Utils (runTestM, satisfied, unsatisfied)
import Test.Snarky.Example.Monad (TransferCompileM, TransferRefM, TransferState, lookupAddress, runTransferCompileM, runTransferRefM)
import Test.Snarky.Example.Utils (chooseBigInt)
import Test.Spec (SpecT, describe, it)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- | The example circuit is monomorphic to `Vesta.ScalarField` (the token
-- | amount range check and the in-circuit Schnorr verifier both pin it),
-- | so the whole test runs over that field.
type SF = Vesta.ScalarField

-- | Build a token amount from a field value (balances stay well under 2^128).
mkAmount :: SF -> TokenAmount (F SF)
mkAmount v = TokenAmount (unsafePartial fromJust (fromField @128 (F v)))

-- | Read the underlying field value of a token amount.
balanceOf :: TokenAmount (F SF) -> SF
balanceOf tb = un F (toField (un TokenAmount tb))

--------------------------------------------------------------------------------
-- Spec

-- | Tree depths to test
treeDepths :: Array Int
treeDepths = [ 4, 6 ]

spec :: SpecT Aff Unit Aff Unit
spec =
  describe "Transfer Circuit Specs" do
    for_ treeDepths \depth ->
      describe ("depth " <> show depth) do
        it "processTransaction" $ reifyType depth transferSpec

transferSpec
  :: forall d
   . Reflectable d Int
  => Proxy d
  -> Aff Unit
transferSpec _ = do
  initialState' <- liftEffect $ randomSampleOne genTreeWithAccounts

  let
    -- Test function: compute expected root after applying the transfer.
    -- Debits the sender (and bumps its nonce) and credits the receiver.
    testFunction :: SignedTransaction (F SF) -> Digest (F SF)
    testFunction (SignedTransaction { transaction: Transaction { transfer: Transfer { from, to, amount } } }) =
      let
        fromAddr = unsafePartial fromJust $ lookupAddress initialState' from
        toAddr = unsafePartial fromJust $ lookupAddress initialState' to

        Account senderAcc = unsafePartial fromJust $ Sparse.get initialState'.tree fromAddr
        Account receiverAcc = unsafePartial fromJust $ Sparse.get initialState'.tree toAddr

        amt = balanceOf amount
        F senderNonce = senderAcc.nonce

        newSenderAcc = Account senderAcc
          { tokenBalance = mkAmount (balanceOf senderAcc.tokenBalance - amt)
          , nonce = F (senderNonce + one)
          }
        newReceiverAcc = Account receiverAcc
          { tokenBalance = mkAmount (balanceOf receiverAcc.tokenBalance + amt) }

        tree' = unsafePartial fromJust $ Sparse.set fromAddr newSenderAcc initialState'.tree
        tree'' = unsafePartial fromJust $ Sparse.set toAddr newReceiverAcc tree'
      in
        Sparse.root tree''

    rootVar =
      let
        Digest (F r) = Sparse.root initialState'.tree
      in
        Digest $ const_ r

    -- The circuit verifies the signature, then applies the transfer.
    circuit
      :: forall t @m
       . AccountMapM m SF d
      => CMT.MerkleRequestM m SF (Account (F SF)) d (Account (FVar SF))
      => CircuitM SF (KimchiConstraint SF) t m
      => SignedTransaction (FVar SF)
      -> Snarky (KimchiConstraint SF) t m (Digest (FVar SF))
    circuit tx = processTransaction @d Mainnet rootVar tx

    solver = makeSolver (Proxy @(KimchiConstraint SF)) circuit
    s =
      runTransferCompileM $
        compile
          (Proxy @(SignedTransaction (F SF)))
          (Proxy @(Digest (F SF)))
          (Proxy @(KimchiConstraint SF))
          (circuit @(TransferCompileM d SF))
          initialState

  ref <- liftEffect $ Ref.new initialState'

  -- Reset state before each test case
  let
    natWithReset :: TransferRefM d SF ~> Effect
    natWithReset m = do
      write initialState' ref
      runTransferRefM ref m

  Console.log "Checking the Valid case"
  liftEffect $ quickCheck' 100 $ genValidSignedTransaction initialState' <#> \a ->
    unsafePerformEffect $ natWithReset $ runTestM { builtState: s, solver, checker: eval, postCondition: Kimchi.postCondition } (satisfied testFunction) a

  liftEffect $ write initialState' ref
  liftEffect $ runTransferRefM ref $ verifyCircuitM { s, gen: genValidSignedTransaction initialState', solver }

  Console.log "Checking the overdraft case"
  liftEffect $ quickCheck' 100 $ genOverdraftSignedTransaction initialState' <#> \a ->
    unsafePerformEffect $ natWithReset $ runTestM { builtState: s, solver, checker: eval, postCondition: Kimchi.postCondition } unsatisfied a
  liftEffect $ write initialState' ref

--------------------------------------------------------------------------------
-- Test data generation

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
