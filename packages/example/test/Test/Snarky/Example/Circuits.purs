module Test.Snarky.Example.Circuits
  ( spec
  ) where

import Prelude

import Data.Foldable (for_)
import Data.Maybe (Maybe(Nothing))
import Data.MerkleTree.Sparse as Sparse
import Data.Reflectable (class Reflectable, reifyType)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Class.Console as Console
import Effect.Ref (write)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)
import Snarky.Backend.Compile (compile, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, const_)
import Snarky.Circuit.Kimchi (verifyCircuitM)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Constraint.Kimchi (KimchiConstraint, eval, initialState)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Transaction (class AccountMapM, SignedTransaction, TransferCompileM, TransferM, applyTx, applyTxChecked, runTransferCompileM, runTransferM)
import Snarky.Example.Types (Account)
import Test.QuickCheck (quickCheck')
import Test.QuickCheck.Gen (randomSampleOne)
import Test.Snarky.Circuit.Utils (runTestM, satisfied, unsatisfied)
import Test.Snarky.Example.Config (chainId)
import Test.Snarky.Example.Generators (genLedger, genOverdraftSignedTransaction, genValidSignedTransaction)
import Test.Spec (SpecT, describe, it)
import Type.Proxy (Proxy(..))

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
  { ledger, keys } <- liftEffect $ randomSampleOne (genLedger 10)

  let
    -- Expected root after applying the transfer: the pure ledger arrow.
    -- The in-circuit `processTransaction` must agree with this. `apply`
    -- is in `Effect` only to `throw` on bad inputs; the valid-case generator
    -- never produces those, so `unsafePerformEffect` is safe here.
    testFunction :: SignedTransaction (F Vesta.ScalarField) -> Digest (F Vesta.ScalarField)
    testFunction tx = Sparse.root (unsafePerformEffect (applyTx chainId tx ledger)).tree

    rootVar =
      let
        Digest (F r) = Sparse.root ledger.tree
      in
        Digest $ const_ r

    -- The circuit verifies the signature, then applies the transfer.
    circuit
      :: forall t @m
       . AccountMapM m Vesta.ScalarField d
      => CMT.MerkleRequestM m Vesta.ScalarField (Account (F Vesta.ScalarField)) d (Account (FVar Vesta.ScalarField))
      => CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t m
      => SignedTransaction (FVar Vesta.ScalarField)
      -> Snarky (KimchiConstraint Vesta.ScalarField) t m (Digest (FVar Vesta.ScalarField))
    circuit tx = applyTxChecked @d chainId rootVar tx

    solver = makeSolver (Proxy @(KimchiConstraint Vesta.ScalarField)) circuit
    s =
      runTransferCompileM $
        compile
          (Proxy @(SignedTransaction (F Vesta.ScalarField)))
          (Proxy @(Digest (F Vesta.ScalarField)))
          (Proxy @(KimchiConstraint Vesta.ScalarField))
          (circuit @(TransferCompileM d Vesta.ScalarField))
          initialState

  ref <- liftEffect $ Ref.new ledger

  let
    -- The transfer circuit takes its transaction explicitly, so the prover
    -- monad needs no current transaction — only the (mutable) ledger.
    env = { currentTransaction: Nothing, ledger: ref }

    -- Reset the ledger before each test case
    natWithReset :: TransferM d Vesta.ScalarField ~> Effect
    natWithReset m = do
      write ledger ref
      runTransferM env m

  Console.log "Checking the Valid case"
  liftEffect $ quickCheck' 100 $ genValidSignedTransaction chainId ledger keys <#> \a ->
    unsafePerformEffect $ natWithReset $ runTestM { builtState: s, solver, checker: eval, postCondition: Kimchi.postCondition } (satisfied testFunction) a

  liftEffect $ write ledger ref
  liftEffect $ runTransferM env $ verifyCircuitM { s, gen: genValidSignedTransaction chainId ledger keys, solver }

  Console.log "Checking the overdraft case"
  liftEffect $ quickCheck' 100 $ genOverdraftSignedTransaction chainId ledger keys <#> \a ->
    unsafePerformEffect $ natWithReset $ runTestM { builtState: s, solver, checker: eval, postCondition: Kimchi.postCondition } unsatisfied a
  liftEffect $ write ledger ref
