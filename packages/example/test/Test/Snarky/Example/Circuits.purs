module Test.Snarky.Example.Circuits
  ( spec
  ) where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Data.Array (mapWithIndex, (..))
import Data.Array.NonEmpty as NEA
import Data.Foldable (foldl)
import Data.Identity (Identity(..))
import Data.Int (pow)
import Data.List as List
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust)
import Data.MerkleTree.Hashable (class MerkleHashable)
import Data.MerkleTree.Sized (Address(..))
import Data.MerkleTree.Sized as SMT
import Data.Newtype (class Newtype, un)
import Data.Reflectable (class Reflectable, reflectType, reifyType)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Class.Console as Console
import Effect.Exception (Error, error)
import Effect.Ref (Ref, read, write)
import Effect.Ref as Ref
import JS.BigInt (BigInt)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafeCrashWith, unsafePartial)
import Poseidon (class PoseidonField)
import Snarky.Backend.Compile (compile, makeSolver)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky)
import Snarky.Circuit.Kimchi.Utils (verifyCircuitM)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Circuit.Types (class CheckedType, class CircuitType)
import Snarky.Constraint.Kimchi (KimchiConstraint, eval, initialState)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class FieldSizeInBits, fromBigInt, fromInt, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Circuits (class AccountMapM, transfer)
import Snarky.Example.Types (Account(..), PublicKey(..), TokenAmount(..), Transaction(..))
import Test.QuickCheck.Gen (Gen, chooseInt, randomSampleOne, suchThat)
import Test.Snarky.Circuit.Utils (circuitSpec', satisfied, unsatisfied)
import Test.Spec (SpecT, beforeAll, describe, it)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- Test monad types

-- | State for the transfer test monad
type TransferState d f =
  { tree :: SMT.MerkleTree d (Digest (F f)) (Account (F f))
  , accountMap :: Map (PublicKey (F f)) (Address d)
  }

-- | Ref to the transfer state
type TransferStateRef d f = Ref (TransferState d f)

-- | Test monad that implements both MerkleRequestM and AccountMapM
newtype TransferRefM d f a = TransferRefM (ReaderT (TransferStateRef d f) Effect a)

derive instance Newtype (TransferRefM d f a) _
derive newtype instance Functor (TransferRefM d f)
derive newtype instance Apply (TransferRefM d f)
derive newtype instance Applicative (TransferRefM d f)
derive newtype instance Bind (TransferRefM d f)
derive newtype instance Monad (TransferRefM d f)
derive newtype instance MonadEffect (TransferRefM d f)
derive newtype instance MonadThrow Error (TransferRefM d f)

runTransferRefM :: forall d f. TransferStateRef d f -> TransferRefM d f ~> Effect
runTransferRefM ref (TransferRefM m) = runReaderT m ref

getStateRef :: forall d f. TransferRefM d f (TransferState d f)
getStateRef = TransferRefM $ ask >>= \ref -> liftEffect $ read ref

modifyStateRef
  :: forall d f
   . (TransferState d f -> TransferState d f)
  -> TransferRefM d f Unit
modifyStateRef f = TransferRefM $ ask >>= \ref -> liftEffect do
  state <- read ref
  write (f state) ref

-- | MerkleRequestM instance for TransferRefM
instance
  ( Reflectable d Int
  , PoseidonField f
  , CircuitType f (Account (F f)) (Account (FVar f))
  , CheckedType (Account (FVar f)) c
  , MerkleHashable (Account (F f)) (Digest (F f))
  ) =>
  CMT.MerkleRequestM (TransferRefM d f) f (Account (F f)) c d (Account (FVar f)) where
  getElement (SMT.Address addr) = do
    { tree } <- getStateRef
    let
      mval = SMT.get tree (SMT.Address addr)
      mpath = SMT.getPath tree (SMT.Address addr)
    case mval, mpath of
      Just v, Just p -> pure { value: v, path: p }
      _, _ -> throwError $ error "getElement: invalid address"

  getPath (SMT.Address addr) = do
    { tree } <- getStateRef
    case SMT.getPath tree (SMT.Address addr) of
      Just p -> pure p
      Nothing -> throwError $ error "getPath: invalid address"

  setValue (SMT.Address addr) v = do
    { tree } <- getStateRef
    case SMT.set tree (SMT.Address addr) v of
      Just tree' -> modifyStateRef \state -> state { tree = tree' }
      Nothing -> throwError $ error "setValue: invalid address"

-- | AccountMapM instance for TransferRefM
instance
  ( Reflectable d Int
  , PoseidonField f
  ) =>
  AccountMapM (TransferRefM d f) f d where
  getAccountId pubKey = do
    { accountMap } <- getStateRef
    case Map.lookup pubKey accountMap of
      Just addr -> pure addr
      Nothing -> throwError $ error $ "getAccountId: unknown public key"

--------------------------------------------------------------------------------
-- Compile-time monad (throws on any request)

newtype TransferCompileM :: Int -> Type -> Type -> Type
newtype TransferCompileM d f a = TransferCompileM (Identity a)

derive instance Newtype (TransferCompileM d f a) _
derive newtype instance Functor (TransferCompileM d f)
derive newtype instance Apply (TransferCompileM d f)
derive newtype instance Applicative (TransferCompileM d f)
derive newtype instance Bind (TransferCompileM d f)
derive newtype instance Monad (TransferCompileM d f)

runTransferCompileM :: forall d f a. TransferCompileM d f a -> a
runTransferCompileM (TransferCompileM m) = un Identity m

-- | MerkleRequestM instance for compilation phase
instance
  ( Reflectable d Int
  , PoseidonField f
  , CircuitType f (Account (F f)) (Account (FVar f))
  , CheckedType (Account (FVar f)) c
  ) =>
  CMT.MerkleRequestM (TransferCompileM d f) f (Account (F f)) c d (Account (FVar f)) where
  getElement _ = unsafeCrashWith "unhandled request: getElement"
  getPath _ = unsafeCrashWith "unhandled request: getPath"
  setValue _ _ = unsafeCrashWith "unhandled request: setValue"

-- | AccountMapM instance for compilation phase
instance
  ( Reflectable d Int
  , PoseidonField f
  ) =>
  AccountMapM (TransferCompileM d f) f d where
  getAccountId _ = unsafeCrashWith "unhandled request: getAccountId"

--------------------------------------------------------------------------------
-- Test data generation

-- | Generate a random merkle tree of accounts with sufficient balances for transfers
-- | Returns the tree and a map from public key to address
genTreeWithAccounts
  :: forall d f
   . Reflectable d Int
  => PoseidonField f
  => Proxy d
  -> Gen (TransferState d f)
genTreeWithAccounts _ = do
  let numElements = 2 `pow` (reflectType (Proxy @d))
  -- Generate accounts with large balances to allow transfers
  accounts <- for (0 .. (numElements - 1)) \i -> do
    -- Use address as public key for simplicity in tests
    let pk = PublicKey $ F $ fromInt i
    -- Give each account a large balance
    balance <- TokenAmount <<< F <<< fromInt <$> chooseInt 1000000 9999999
    pure $ Account { publicKey: pk, tokenBalance: balance }

  let
    nea = unsafePartial fromJust $ NEA.fromArray accounts
    { head: a, tail: as } = NEA.uncons nea

    base :: SMT.MerkleTree d (Digest (F f)) (Account (F f))
    base = SMT.create a
    tree = SMT.addMany base (List.fromFoldable as)

    -- Build the account map
    accountMap = Map.fromFoldable $ mapWithIndex
      ( \i (Account acc) ->
          Tuple acc.publicKey (Address $ BigInt.fromInt i)
      )
      accounts

  pure { tree, accountMap }

-- | Generate two distinct valid addresses for a tree
genDistinctAddresses
  :: forall d f
   . SMT.MerkleTree d (Digest (F f)) (Account (F f))
  -> Gen { fromAddr :: Address d, toAddr :: Address d }
genDistinctAddresses tree = do
  let maxAddr = SMT.size tree - one
  fromIdx <- chooseBigInt zero maxAddr
  toIdx <- chooseBigInt zero maxAddr `suchThat` (\i -> i /= fromIdx)
  pure { fromAddr: Address fromIdx, toAddr: Address toIdx }

-- | Generate a valid transfer transaction for a given tree
genValidTransfer
  :: forall d f
   . Reflectable d Int
  => PoseidonField f
  => Ord f
  => TransferState d f
  -> Gen (Transaction (F f))
genValidTransfer { tree } = do
  { fromAddr, toAddr } <- genDistinctAddresses tree

  let
    -- Get sender account to determine max transfer amount
    Account senderAcc = unsafePartial fromJust $ SMT.get tree fromAddr
    TokenAmount (F senderBalance) = senderAcc.tokenBalance

  -- Pick a valid transfer amount (less than sender's balance)
  amountInt <- chooseBigInt one (max one (toBigInt senderBalance - one))
  let amount = TokenAmount $ F $ fromBigInt amountInt

  let
    Account { publicKey: from } = unsafePartial fromJust $ SMT.get tree fromAddr
    Account { publicKey: to } = unsafePartial fromJust $ SMT.get tree toAddr

  pure $ Transaction { from, to, amount }

-- | Generate an invalid transfer transaction where the amount exceeds the sender's balance
genInvalidTransferOverdraft
  :: forall d f
   . Reflectable d Int
  => PoseidonField f
  => Ord f
  => TransferState d f
  -> Gen (Transaction (F f))
genInvalidTransferOverdraft { tree } = do
  { fromAddr, toAddr } <- genDistinctAddresses tree

  let
    -- Get sender account
    Account senderAcc = unsafePartial fromJust $ SMT.get tree fromAddr
    TokenAmount (F senderBalance) = senderAcc.tokenBalance

    -- Set amount to one more than sender's balance (overdraft)
    amount = TokenAmount $ F $ senderBalance + one

    Account { publicKey: from } = unsafePartial fromJust $ SMT.get tree fromAddr
    Account { publicKey: to } = unsafePartial fromJust $ SMT.get tree toAddr

  pure $ Transaction { from, to, amount }

--------------------------------------------------------------------------------
-- Transfer spec

transferSpec
  :: forall f f' g' d
   . Kimchi.KimchiVerify f f'
  => CircuitGateConstructor f g'
  => FieldSizeInBits f 255
  => Reflectable d Int
  => Ord f
  => Proxy f
  -> Proxy d
  -> Aff Unit
transferSpec _ pd = do
  initialState' <- liftEffect $ randomSampleOne (genTreeWithAccounts pd)

  let
    -- Test function: compute expected root after transfer
    testFunction :: Transaction (F f) -> Digest (F f)
    testFunction (Transaction { from, to, amount }) =
      let
        -- Look up addresses
        fromAddr = unsafePartial fromJust $ Map.lookup from initialState'.accountMap
        toAddr = unsafePartial fromJust $ Map.lookup to initialState'.accountMap

        -- Get accounts
        Account senderAcc = unsafePartial fromJust $ SMT.get initialState'.tree fromAddr
        Account receiverAcc = unsafePartial fromJust $ SMT.get initialState'.tree toAddr

        -- Compute new balances
        newSenderBal = senderAcc.tokenBalance - amount
        newReceiverBal = receiverAcc.tokenBalance + amount

        -- Update accounts
        newSenderAcc = Account senderAcc { tokenBalance = newSenderBal }
        newReceiverAcc = Account receiverAcc { tokenBalance = newReceiverBal }

        -- Update tree
        tree' = unsafePartial fromJust $ SMT.set initialState'.tree fromAddr newSenderAcc
        tree'' = unsafePartial fromJust $ SMT.set tree' toAddr newReceiverAcc
      in
        SMT.root tree''

    rootVar =
      let
        Digest (F r) = SMT.root initialState'.tree
      in
        Digest $ const_ r

    circuit
      :: forall t @m
       . AccountMapM m f d
      => CMT.MerkleRequestM m f (Account (F f)) (KimchiConstraint f) d (Account (FVar f))
      => MerkleHashable (Account (FVar f)) (Snarky (KimchiConstraint f) t m (Digest (FVar f)))
      => CircuitM f (KimchiConstraint f) t m
      => Transaction (FVar f)
      -> Snarky (KimchiConstraint f) t m (Digest (FVar f))
    circuit tx = transfer rootVar tx

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
  circuitSpec' natWithReset
    { builtState: s
    , checker: eval
    , solver: solver
    , testFunction: satisfied testFunction
    , postCondition: Kimchi.postCondition
    }
    (genValidTransfer initialState')

  liftEffect $ write initialState' ref
  liftEffect $ runTransferRefM ref $ verifyCircuitM { s, gen: genValidTransfer initialState', solver }

  Console.log "Checking the overdraft case"
  circuitSpec' natWithReset
    { builtState: s
    , checker: eval
    , solver: solver
    , testFunction: unsatisfied
    , postCondition: Kimchi.postCondition
    }
    (genInvalidTransferOverdraft initialState')
  liftEffect $ write initialState' ref

--------------------------------------------------------------------------------
-- Spec

spec :: SpecT Aff Unit Aff Unit
spec = beforeAll genSize $
  describe "Transfer Circuit Specs" do
    describe "valid transfer" do
      it "Vesta" \d ->
        reifyType d \pd ->
          transferSpec (Proxy @Vesta.ScalarField) pd
      it "Pallas" \d ->
        reifyType d \pd ->
          transferSpec (Proxy @Pallas.ScalarField) pd
  where
  genSize = liftEffect do
    d <- randomSampleOne $ chooseInt 3 6
    Console.log $ "Running Transfer Circuit Spec with tree depth " <> show d
    pure d

--------------------------------------------------------------------------------

-- | Generate a random BigInt in the range [a, b] (inclusive)
chooseBigInt :: BigInt -> BigInt -> Gen BigInt
chooseBigInt a b
  | a > b = chooseBigInt b a
  | otherwise = (\x -> x + a) <$> chooseBigInt' (b - a)

-- | Generate a random BigInt in the range [0, range] (inclusive)
chooseBigInt' :: BigInt -> Gen BigInt
chooseBigInt' range =
  case BigInt.toInt range of
    -- Common case: range fits in Int32
    Just n -> BigInt.fromInt <$> chooseInt 0 n
    -- Large range: generate random bits and mod
    Nothing -> do
      let
        numBits = bitLength range
        numChunks = (numBits + 30) / 31 -- 31 bits per chunk (safe Int)
      -- Generate random 31-bit chunks
      chunks <- for (1 .. numChunks) \_ -> BigInt.fromInt <$> chooseInt 0 0x7FFFFFFF
      -- Combine chunks into a single BigInt
      let randomBits = foldlChunks chunks
      -- Mod by (range + 1) to get value in [0, range]
      pure $ randomBits `mod` (range + BigInt.fromInt 1)
  where
  -- Combine chunks: each chunk contributes 31 bits
  foldlChunks :: Array BigInt -> BigInt
  foldlChunks =
    let
      base = BigInt.fromInt 0x40000000 * BigInt.fromInt 2 -- 2^31
    in
      foldl (\acc chunk -> acc * base + chunk) (BigInt.fromInt 0)

  -- Count bits needed to represent n
  bitLength :: BigInt -> Int
  bitLength n
    | n <= BigInt.fromInt 0 = 0
    | otherwise = 1 + bitLength (n / BigInt.fromInt 2)

