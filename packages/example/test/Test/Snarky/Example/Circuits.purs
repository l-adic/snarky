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
import Run (Run)
import Snarky.Backend.Compile (compile, makeSolver)
import Snarky.Circuit.DSL (FVar, Snarky, const_)
import Snarky.Circuit.Kimchi (verifyCircuitM)
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Constraint.Kimchi (KimchiConstraint, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Simulation (genGenesisLedger, genOverdraftSignedTransaction, genValidSignedTransaction)
import Snarky.Example.Transaction (SignedTransaction, TransferAdvice, applyTx, applyTxChecked, runTransferCompileM, runTransferM)
import Test.QuickCheck (quickCheck')
import Test.QuickCheck.Gen (randomSampleOne)
import Test.Snarky.Circuit.Utils (runTestM, satisfied, unsatisfied)
import Test.Snarky.Example.Config (chainId)
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
  { ledger, keys } <- liftEffect $ randomSampleOne (genGenesisLedger 10)

  let
    -- Expected root after applying the transfer: the pure ledger arrow.
    -- The in-circuit `processTransaction` must agree with this. `apply`
    -- is in `Effect` only to `throw` on bad inputs; the valid-case generator
    -- never produces those, so `unsafePerformEffect` is safe here.
    testFunction :: SignedTransaction Vesta.ScalarField -> Digest Vesta.ScalarField
    testFunction tx = Sparse.root (unsafePerformEffect (applyTx chainId tx ledger)).tree

    rootVar =
      let
        Digest r = Sparse.root ledger.tree
      in
        Digest $ const_ r

    -- The circuit verifies the signature, then applies the transfer.
    circuit
      :: SignedTransaction (FVar Vesta.ScalarField)
      -> Snarky Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) (TransferAdvice d) (Digest (FVar Vesta.ScalarField))
    circuit tx = applyTxChecked @d chainId rootVar tx

    solver = makeSolver (Proxy @(KimchiConstraint Vesta.ScalarField)) circuit
    s =
      unsafePerformEffect $
        compile runTransferCompileM
          (Proxy @(SignedTransaction Vesta.ScalarField))
          (Proxy @(Digest Vesta.ScalarField))
          (Proxy @(KimchiConstraint Vesta.ScalarField))
          circuit

  ref <- liftEffect $ Ref.new ledger

  let
    -- The transfer circuit takes its transaction explicitly, so the prover
    -- monad needs no current transaction — only the (mutable) ledger.
    env = { currentTransaction: Nothing, ledger: ref }

  Console.log "Checking the Valid case"
  liftEffect $ quickCheck' 100 $ genValidSignedTransaction chainId ledger keys <#> \a ->
    unsafePerformEffect do
      write ledger ref
      runTestM (runTransferM env) { builtState: s, solver, checker: eval, postCondition: Kimchi.postCondition } (satisfied testFunction) a

  liftEffect $ write ledger ref
  liftEffect $ verifyCircuitM (runTransferM env) { s, gen: genValidSignedTransaction chainId ledger keys, solver }

  Console.log "Checking the overdraft case"
  liftEffect $ quickCheck' 100 $ genOverdraftSignedTransaction chainId ledger keys <#> \a ->
    unsafePerformEffect do
      write ledger ref
      runTestM (runTransferM env) { builtState: s, solver, checker: eval, postCondition: Kimchi.postCondition } unsatisfied a
  liftEffect $ write ledger ref
