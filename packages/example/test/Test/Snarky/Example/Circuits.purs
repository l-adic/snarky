module Test.Snarky.Example.Circuits
  ( spec
  ) where

import Prelude

import Data.Array (length, (!!), (..))
import Data.Foldable (foldl, for_)
import Data.Map as Map
import Data.Maybe (fromJust)
import Data.MerkleTree.Hashable (class MerkleHashable)
import Data.MerkleTree.Sparse as Sparse
import Data.Reflectable (class Reflectable, reifyType)
import Data.Set as Set
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Class.Console as Console
import Effect.Ref (write)
import Effect.Ref as Ref
import Partial.Unsafe (unsafePartial)
import Poseidon (class PoseidonField)
import Prim.Int (class Add)
import Snarky.Backend.Compile (compile, makeSolver)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky)
import Snarky.Circuit.Kimchi.Utils (verifyCircuitM)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Constraint.Kimchi (KimchiConstraint, eval, initialState)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromBigInt, fromInt, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Circuits (class AccountMapM, transfer)
import Snarky.Example.Types (Account(..), PublicKey(..), TokenAmount(..), Transaction)
import Test.QuickCheck.Gen (Gen, chooseInt, randomSampleOne, suchThat)
import Test.Snarky.Circuit.Utils (circuitSpec', satisfied, unsatisfied)
import Test.Snarky.Example.Monad (TransferCompileM, TransferRefM, TransferState, lookupAddress, runTransferCompileM, runTransferRefM)
import Test.Snarky.Example.Utils (chooseBigInt)
import Test.Spec (SpecT, describe, it)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- Spec

-- | Tree depths to test
treeDepths :: Array Int
treeDepths = [ 4, 8 ]

spec :: SpecT Aff Unit Aff Unit
spec =
  describe "Transfer Circuit Specs" do
    for_ treeDepths \depth ->
      describe ("depth " <> show depth) do
        it "Vesta" $ reifyType depth (transferSpec (Proxy @Vesta.ScalarField))
        it "Pallas" $ reifyType depth (transferSpec (Proxy @Pallas.ScalarField))

transferSpec
  :: forall f f' g' d _k
   . Kimchi.KimchiVerify f f'
  => CircuitGateConstructor f g'
  => FieldSizeInBits f 255
  => Reflectable d Int
  => PrimeField f
  => Add 64 _k 255
  => Ord f
  => Proxy f
  -> Proxy d
  -> Aff Unit
transferSpec _ _ = do
  initialState' <- liftEffect $ randomSampleOne genTreeWithAccounts

  let
    -- Test function: compute expected root after transfer
    -- Uses accountMap to look up addresses from public keys
    testFunction :: Transaction (F f) -> Digest (F f)
    testFunction { from, to, amount } =
      let
        -- Look up addresses from public keys
        fromAddr = unsafePartial fromJust $ lookupAddress initialState' from
        toAddr = unsafePartial fromJust $ lookupAddress initialState' to

        -- Get accounts using addresses
        Account senderAcc = unsafePartial fromJust $ Sparse.get initialState'.tree fromAddr
        Account receiverAcc = unsafePartial fromJust $ Sparse.get initialState'.tree toAddr

        -- Compute new balances
        newSenderBal = senderAcc.tokenBalance - amount
        newReceiverBal = receiverAcc.tokenBalance + amount

        -- Update accounts
        newSenderAcc = Account senderAcc { tokenBalance = newSenderBal }
        newReceiverAcc = Account receiverAcc { tokenBalance = newReceiverBal }

        -- Update tree
        tree' = unsafePartial fromJust $ Sparse.set fromAddr newSenderAcc initialState'.tree
        tree'' = unsafePartial fromJust $ Sparse.set toAddr newReceiverAcc tree'
      in
        Sparse.root tree''

    rootVar =
      let
        Digest (F r) = Sparse.root initialState'.tree
      in
        Digest $ const_ r

    -- The circuit takes a Transaction and looks up addresses via AccountMapM
    circuit
      :: forall t @m _k1
       . Reflectable d Int
      => PoseidonField f
      => FieldSizeInBits f 255
      => Add 64 _k1 255
      => AccountMapM m f d
      => CMT.MerkleRequestM m f (Account (F f)) d (Account (FVar f))
      => MerkleHashable (Account (FVar f)) (Snarky (KimchiConstraint f) t m (Digest (FVar f)))
      => CircuitM f (KimchiConstraint f) t m
      => Transaction (FVar f)
      -> Snarky (KimchiConstraint f) t m (Digest (FVar f))
    circuit tx = transfer @d rootVar tx

    solver = makeSolver (Proxy @(KimchiConstraint f)) circuit
    s =
      runTransferCompileM $
        compile
          (Proxy @(Transaction (F f)))
          (Proxy @(Digest (F f)))
          (Proxy @(KimchiConstraint f))
          (circuit @(TransferCompileM d f))
          initialState

  ref <- liftEffect $ Ref.new initialState'

  -- Reset state before each test case
  let
    natWithReset :: TransferRefM d f ~> Effect
    natWithReset m = do
      write initialState' ref
      runTransferRefM ref m

  Console.log "Checking the Valid case"
  circuitSpec' 100 natWithReset
    { builtState: s
    , checker: eval
    , solver: solver
    , testFunction: satisfied testFunction
    , postCondition: Kimchi.postCondition
    }
    (genValidTransaction initialState')

  liftEffect $ write initialState' ref
  liftEffect $ runTransferRefM ref $ verifyCircuitM { s, gen: genValidTransaction initialState', solver }

  Console.log "Checking the overdraft case"
  circuitSpec' 100 natWithReset
    { builtState: s
    , checker: eval
    , solver: solver
    , testFunction: unsatisfied
    , postCondition: Kimchi.postCondition
    }
    (genOverdraftTransaction initialState')
  liftEffect $ write initialState' ref

--------------------------------------------------------------------------------
-- Test data generation

-- | Number of accounts to generate for testing
numAccounts :: Int
numAccounts = 10

-- | Generate a random sparse merkle tree of accounts with sufficient balances for transfers.
-- | Addresses are assigned sequentially (0, 1, 2, ...) like Mina does.
genTreeWithAccounts
  :: forall d f
   . Reflectable d Int
  => PoseidonField f
  => PrimeField f
  => Gen (TransferState d f)
genTreeWithAccounts = do
  -- Generate accounts with distinct public keys and large balances
  accounts <- for (1 .. numAccounts) \i -> do
    let pk = PublicKey $ F $ fromInt i
    balance <- TokenAmount <<< F <<< fromInt <$> chooseInt 1000000 9999999
    pure $ Tuple pk (Account { publicKey: pk, tokenBalance: balance })

  -- Build the sparse tree by inserting accounts at sequential addresses
  -- Also build the account map (publicKey -> address)
  let
    insertAccount { tree, accountMap, nextAddress } (Tuple (PublicKey (F pk)) acc) =
      let
        addr = Sparse.Address nextAddress
      in
        { tree: unsafePartial fromJust $ Sparse.set addr acc tree
        , accountMap: Map.insert (toBigInt pk) addr accountMap
        , nextAddress: nextAddress + one
        }

    initialSt =
      { tree: Sparse.empty
      , accountMap: Map.empty
      , nextAddress: zero
      }

  pure $ foldl insertAccount initialSt accounts

-- | Pick two distinct public keys from the account map
genDistinctPublicKeys
  :: forall d f
   . PrimeField f
  => TransferState d f
  -> Gen { fromPk :: PublicKey (F f), toPk :: PublicKey (F f) }
genDistinctPublicKeys state = do
  let
    keys :: Array _
    keys = Set.toUnfoldable $ Map.keys state.accountMap
    maxIdx = length keys - 1
  fromIdx <- chooseInt 0 maxIdx
  toIdx <- chooseInt 0 maxIdx `suchThat` (\i -> i /= fromIdx)
  let
    fromPkBigInt = unsafePartial fromJust $ keys !! fromIdx
    toPkBigInt = unsafePartial fromJust $ keys !! toIdx
  pure
    { fromPk: PublicKey $ F $ fromBigInt fromPkBigInt
    , toPk: PublicKey $ F $ fromBigInt toPkBigInt
    }

-- | Generate a valid transfer transaction for a given state.
-- | The Transaction just contains public keys and amount - no addresses.
genValidTransaction
  :: forall d f
   . Reflectable d Int
  => PoseidonField f
  => PrimeField f
  => Ord f
  => TransferState d f
  -> Gen (Transaction (F f))
genValidTransaction state = do
  { fromPk, toPk } <- genDistinctPublicKeys state

  let
    -- Look up address to get sender's balance (for generating valid amount)
    fromAddr = unsafePartial fromJust $ lookupAddress state fromPk
    Account senderAcc = unsafePartial fromJust $ Sparse.get state.tree fromAddr
    TokenAmount (F senderBalance) = senderAcc.tokenBalance

  -- Pick a valid transfer amount (less than sender's balance)
  amountInt <- chooseBigInt one (max one (toBigInt senderBalance - one))
  let amount = TokenAmount $ F $ fromBigInt amountInt

  pure { from: fromPk, to: toPk, amount }

-- | Generate an invalid transfer transaction where the amount exceeds the sender's balance
genOverdraftTransaction
  :: forall d f
   . Reflectable d Int
  => PoseidonField f
  => PrimeField f
  => Ord f
  => TransferState d f
  -> Gen (Transaction (F f))
genOverdraftTransaction state = do
  { fromPk, toPk } <- genDistinctPublicKeys state

  let
    -- Look up address to get sender's balance
    fromAddr = unsafePartial fromJust $ lookupAddress state fromPk
    Account senderAcc = unsafePartial fromJust $ Sparse.get state.tree fromAddr
    TokenAmount (F senderBalance) = senderAcc.tokenBalance

    -- Set amount to one more than sender's balance (overdraft)
    amount = TokenAmount $ F $ senderBalance + one

  pure { from: fromPk, to: toPk, amount }
