module Test.Snarky.Circuit.MerkleTree
  ( spec
  ) where

import Prelude

import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Data.Array.NonEmpty as NEA
import Data.Identity (Identity(..))
import Data.Int (pow)
import Data.List as List
import Data.Maybe (Maybe(..), fromJust)
import Data.MerkleTree.Hashable (hash)
import Data.MerkleTree.Sized (Address(..))
import Data.MerkleTree.Sized as SMT
import Data.Newtype (class Newtype, un)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Exception.Unsafe (unsafeThrow)
import Effect.Ref (Ref, read, write)
import Effect.Ref as Ref
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Poseidon.Class (class PoseidonField)
import Snarky.Backend.Compile (compile, makeSolver)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit, verifyCircuitM)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Circuit.Types (class CheckedType, class CircuitType)
import Snarky.Constraint.Kimchi (KimchiConstraint, eval, initialState)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen, chooseInt, randomSampleOne, vectorOf)
import Test.Snarky.Circuit.Utils (circuitSpec', circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

-- | Tree reference type alias
type TreeRef d f = Ref (SMT.MerkleTree d (Digest (F f)) (F f))

-- | Monad that reads tree from a Ref
newtype MerkleRefM d f a = MerkleRefM (ReaderT (TreeRef d f) Effect a)

derive instance Newtype (MerkleRefM d f a) _
derive newtype instance Functor (MerkleRefM d f)
derive newtype instance Apply (MerkleRefM d f)
derive newtype instance Applicative (MerkleRefM d f)
derive newtype instance Bind (MerkleRefM d f)
derive newtype instance Monad (MerkleRefM d f)
derive newtype instance MonadEffect (MerkleRefM d f)

runMerkleRefM :: forall d f. TreeRef d f -> MerkleRefM d f ~> Effect
runMerkleRefM tree (MerkleRefM m) = runReaderT m tree

getTreeRef :: forall d f. MerkleRefM d f (SMT.MerkleTree d (Digest (F f)) (F f))
getTreeRef = MerkleRefM $ ask >>= \ref -> liftEffect $ read ref

modifyTreeRef
  :: forall d f
   . (SMT.MerkleTree d (Digest (F f)) (F f) -> SMT.MerkleTree d (Digest (F f)) (F f))
  -> MerkleRefM d f Unit
modifyTreeRef f = MerkleRefM $ ask >>= \ref -> liftEffect do
  tree <- read ref
  write (f tree) ref

-- | Instance for Ref-based testing (reads/writes tree via Ref)
instance
  ( Reflectable d Int
  , PoseidonField f
  , CircuitType f (F f) (FVar f)
  , CheckedType (FVar f) c
  ) =>
  CMT.MerkleRequestM (MerkleRefM d f) f (F f) c d (FVar f) where
  getElement (SMT.Address addr) = do
    tree <- getTreeRef
    let
      mval = SMT.get tree (SMT.Address addr)
      mpath = SMT.getPath tree (SMT.Address addr)
    case mval, mpath of
      Just v, Just p -> pure { value: v, path: p }
      _, _ -> unsafeThrow "getElement: invalid address"

  getPath (SMT.Address addr) = do
    tree <- getTreeRef
    case SMT.getPath tree (SMT.Address addr) of
      Just p -> pure p
      Nothing -> unsafeThrow "getPath: invalid address"

  setValue (SMT.Address addr) v = do
    modifyTreeRef \tree ->
      case SMT.set tree (SMT.Address addr) v of
        Just tree' -> tree'
        Nothing -> unsafeThrow "setValue: invalid address"

-- | Newtype wrapper for compilation phase (throws on any request)
newtype MerkleCompileM :: Int -> Type -> Type -> Type
newtype MerkleCompileM d f a = MerkleCompileM (Identity a)

derive instance Newtype (MerkleCompileM d f a) _
derive newtype instance Functor (MerkleCompileM d f)
derive newtype instance Apply (MerkleCompileM d f)
derive newtype instance Applicative (MerkleCompileM d f)
derive newtype instance Bind (MerkleCompileM d f)
derive newtype instance Monad (MerkleCompileM d f)

runMerkleCompileM :: forall d f a. MerkleCompileM d f a -> a
runMerkleCompileM (MerkleCompileM m) = un Identity m

-- | Instance for compilation phase - throws on any request
instance
  ( Reflectable d Int
  , PoseidonField f
  , CircuitType f (F f) (FVar f)
  , CheckedType (FVar f) c
  ) =>
  CMT.MerkleRequestM (MerkleCompileM d f) f (F f) c d (FVar f) where
  getElement _ = unsafeThrow "unhandled request: getElement"
  getPath _ = unsafeThrow "unhandled request: getPath"
  setValue _ _ = unsafeThrow "unhandled request: setValue"

-- | Generate a random filled merkle tree of depth d
genTree
  :: forall d f
   . Reflectable d Int
  => PoseidonField f
  => Proxy d
  -> Gen (SMT.MerkleTree d (Digest (F f)) (F f))
genTree _ = do
  let numElements = 2 `pow` (reflectType (Proxy @d))
  vs <- vectorOf numElements (arbitrary @(F f))
  let
    nea = unsafePartial fromJust $ NEA.fromArray vs
    { head: a, tail: as } = NEA.uncons nea

    base :: SMT.MerkleTree d (Digest (F f)) (F f)
    base = SMT.create a
  pure $ SMT.addMany base (List.fromFoldable as)

--------------------------------------------------------------------------------

-- | Test for impliedRoot circuit - pure computation, no MerkleRequestM needed
impliedRootSpec
  :: forall f f' g' d
   . Kimchi.KimchiVerify f f'
  => CircuitGateConstructor f g'
  => Reflectable d Int
  => String
  -> Proxy f
  -> Proxy d
  -> Spec Unit
impliedRootSpec testName _ pd = describe ("impliedRoot: " <> testName) do
  it "computes correct root from address, hash, and path" do
    tree <- liftEffect $ randomSampleOne (genTree pd)

    let
      -- Expected: use pure impliedRoot
      testFunction
        :: Tuple (Address d) (Tuple (Digest (F f)) (SMT.Path d (Digest (F f))))
        -> Digest (F f)
      testFunction (Tuple addr (Tuple entryHash path)) =
        SMT.impliedRoot addr entryHash path

      circuit
        :: forall t
         . CircuitM f (KimchiConstraint f) t Identity
        => Tuple (SMT.AddressVar d f) (Tuple (Digest (FVar f)) (SMT.Path d (Digest (FVar f))))
        -> Snarky (KimchiConstraint f) t Identity (Digest (FVar f))
      circuit (Tuple addr (Tuple entryHash path)) =
        CMT.impliedRoot addr entryHash path

      solver = makeSolver (Proxy @(KimchiConstraint f)) circuit
      s = un Identity $
        compile
          (Proxy @(Tuple (Address d) (Tuple (Digest (F f)) (SMT.Path d (Digest (F f))))))
          (Proxy @(Digest (F f)))
          (Proxy @(KimchiConstraint f))
          circuit
          initialState

      -- Generator: produce valid (address, entryHash, path) triples from fixed tree
      gen = do
        addrInt <- chooseInt 0 ((2 `pow` reflectType pd) - 1)
        let
          addr = Address $ BigInt.fromInt addrInt
          elem = unsafePartial fromJust $ SMT.get tree addr
          entryHash = hash (Just elem)
          path = unsafePartial fromJust $ SMT.getPath tree addr
        pure $ Tuple addr (Tuple entryHash path)

    circuitSpecPure'
      { builtState: s
      , checker: eval
      , solver: solver
      , testFunction: satisfied testFunction
      , postCondition: Kimchi.postCondition
      }
      gen

    liftEffect $ verifyCircuit { s, gen, solver }

--------------------------------------------------------------------------------

-- | The get circuit for testing - polymorphic in monad m
getSpec
  :: forall f f' g' d
   . Kimchi.KimchiVerify f f'
  => CircuitGateConstructor f g'
  => Reflectable d Int
  => String
  -> Proxy f
  -> Proxy d
  -> Spec Unit
getSpec testName _ pd = describe ("Poseidon Circuit Tests: " <> testName) do
  it "factors Circuit is Valid" do
    tree <- liftEffect $ randomSampleOne (genTree pd)

    let
      testFunction :: SMT.Address d -> F f
      testFunction addr = unsafePartial $ fromJust $ SMT.get tree addr

      rootVar =
        let
          Digest (F r) = SMT.root tree
        in
          Digest $ const_ r

      circuit
        :: forall t @m
         . CMT.MerkleRequestM m f (F f) (KimchiConstraint f) d (FVar f)
        => CircuitM f (KimchiConstraint f) t m
        => SMT.AddressVar d f
        -> Snarky (KimchiConstraint f) t m (FVar f)
      circuit addr = CMT.get addr rootVar

      solver = makeSolver (Proxy @(KimchiConstraint f)) circuit
      s =
        runMerkleCompileM $
          compile
            (Proxy @(Address d))
            (Proxy @(F f))
            (Proxy @(KimchiConstraint f))
            (circuit @(MerkleCompileM d f))
            initialState
      gen =
        let
          maxAddress = (2 `pow` reflectType (Proxy @d)) - 1
        in
          Address <<< BigInt.fromInt <$> chooseInt 0 maxAddress

    ref <- liftEffect $ Ref.new tree

    circuitSpec' (runMerkleRefM ref)
      { builtState: s
      , checker: eval
      , solver: solver
      , testFunction: satisfied testFunction
      , postCondition: Kimchi.postCondition
      }
      gen

    liftEffect $ (runMerkleRefM ref) $ verifyCircuitM { s, gen, solver }

--------------------------------------------------------------------------------

-- | Test for fetchAndUpdate circuit - modifies tree state
fetchAndUpdateSpec
  :: forall f f' g' d
   . Kimchi.KimchiVerify f f'
  => CircuitGateConstructor f g'
  => Reflectable d Int
  => String
  -> Proxy f
  -> Proxy d
  -> Spec Unit
fetchAndUpdateSpec testName _ pd = describe ("fetchAndUpdate: " <> testName) do
  it "fetches element, applies modification, and updates tree" do
    initialTree <- liftEffect $ randomSampleOne (genTree pd)

    let
      -- Modification function: add one (uses Semiring instance for Snarky)
      modifyF :: forall t m. CircuitM f (KimchiConstraint f) t m => FVar f -> Snarky (KimchiConstraint f) t m (FVar f)
      modifyF x = pure x + one

      -- Pure modification for test function
      modifyPure :: F f -> F f
      modifyPure x = x + one

      -- Test function: compute expected output from initial tree state
      -- Note: tree gets reset before each test case
      testFunction :: SMT.Address d -> { root :: Digest (F f), old :: F f, new :: F f }
      testFunction addr =
        let
          oldVal = unsafePartial fromJust $ SMT.get initialTree addr
          newVal = modifyPure oldVal
          -- Compute new root by updating the tree
          updatedTree = unsafePartial fromJust $ SMT.set initialTree addr newVal
          newRoot = SMT.root updatedTree
        in
          { root: newRoot, old: oldVal, new: newVal }

      rootVar =
        let
          Digest (F r) = SMT.root initialTree
        in
          Digest $ const_ r

      circuit
        :: forall t @m
         . CMT.MerkleRequestM m f (F f) (KimchiConstraint f) d (FVar f)
        => CircuitM f (KimchiConstraint f) t m
        => SMT.AddressVar d f
        -> Snarky (KimchiConstraint f) t m { root :: Digest (FVar f), old :: FVar f, new :: FVar f }
      circuit addr = CMT.fetchAndUpdate addr rootVar modifyF

      solver = makeSolver (Proxy @(KimchiConstraint f)) circuit
      s =
        runMerkleCompileM $
          compile
            (Proxy @(Address d))
            (Proxy @{ root :: Digest (F f), old :: F f, new :: F f })
            (Proxy @(KimchiConstraint f))
            (circuit @(MerkleCompileM d f))
            initialState

      gen =
        let
          maxAddress = (2 `pow` reflectType (Proxy @d)) - 1
        in
          Address <<< BigInt.fromInt <$> chooseInt 0 maxAddress

    ref <- liftEffect $ Ref.new initialTree

    -- Reset tree before each test case
    let
      natWithReset :: MerkleRefM d f ~> Effect
      natWithReset m = do
        write initialTree ref
        runMerkleRefM ref m

    circuitSpec' natWithReset
      { builtState: s
      , checker: eval
      , solver: solver
      , testFunction: satisfied testFunction
      , postCondition: Kimchi.postCondition
      }
      gen

    -- Reset for verify
    liftEffect $ write initialTree ref
    liftEffect $ (runMerkleRefM ref) $ verifyCircuitM { s, gen, solver }

spec :: Spec Unit
spec = describe "Merkle Tree Circuit Specs" do
  describe "impliedRoot" do
    impliedRootSpec "Vesta" (Proxy @Vesta.ScalarField) (Proxy @4)
    impliedRootSpec "Pallas" (Proxy @Pallas.ScalarField) (Proxy @4)
  describe "get" do
    getSpec "Vesta" (Proxy @Vesta.ScalarField) (Proxy @4)
    getSpec "Pallas" (Proxy @Pallas.ScalarField) (Proxy @4)
  describe "fetchAndUpdate" do
    fetchAndUpdateSpec "Vesta" (Proxy @Vesta.ScalarField) (Proxy @4)
    fetchAndUpdateSpec "Pallas" (Proxy @Pallas.ScalarField) (Proxy @4)
