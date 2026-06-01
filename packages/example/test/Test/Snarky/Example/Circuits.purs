module Test.Snarky.Example.Circuits
  ( spec
  ) where

import Prelude

import Data.Foldable (for_)
import Data.Maybe (fromJust)
import Data.MerkleTree.Sparse as Sparse
import Data.Reflectable (class Reflectable, reifyType)
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
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, const_)
import Snarky.Circuit.Kimchi (verifyCircuitM)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Constraint.Kimchi (KimchiConstraint, eval, initialState)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Circuits (class AccountMapM, processTransaction)
import Snarky.Example.Types (Account(..), SignedTransaction(..), Transaction(..), Transfer(..))
import Test.QuickCheck (quickCheck')
import Test.QuickCheck.Gen (randomSampleOne)
import Test.Snarky.Circuit.Utils (runTestM, satisfied, unsatisfied)
import Test.Snarky.Example.Ledger (balanceOf, genOverdraftSignedTransaction, genTreeWithAccounts, genValidSignedTransaction, mkAmount)
import Test.Snarky.Example.Monad (TransferCompileM, TransferRefM, lookupAddress, runTransferCompileM, runTransferRefM)
import Test.Spec (SpecT, describe, it)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- | The example circuit is monomorphic to `Vesta.ScalarField` (the token
-- | amount range check and the in-circuit Schnorr verifier both pin it),
-- | so the whole test runs over that field.
type SF = Vesta.ScalarField

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
