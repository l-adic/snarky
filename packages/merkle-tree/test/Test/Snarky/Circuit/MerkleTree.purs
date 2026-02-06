module Test.Snarky.Circuit.MerkleTree
  ( spec
  ) where

import Prelude

import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Data.Array.NonEmpty as NEA
import Data.Generic.Rep (class Generic)
import Data.Identity (Identity(..))
import Data.Int (pow)
import Data.List as List
import Data.Maybe (Maybe(..), fromJust)
import Data.MerkleTree.Hashable (class Hashable, class MerkleHashable, hash)
import Data.MerkleTree.Sized (Address(..))
import Data.MerkleTree.Sized as SMT
import Data.Newtype (class Newtype, un)
import Data.Reflectable (class Reflectable, reflectType, reifyType)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Class.Console as Console
import Effect.Exception.Unsafe (unsafeThrow)
import Effect.Ref (Ref, read, write)
import Effect.Ref as Ref
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Poseidon (class PoseidonField)
import Poseidon as Poseidon
import Snarky.Backend.Compile (compile, makeSolver)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.DSL (class CheckedType, class CircuitM, class CircuitType, F(..), FVar, Snarky, const_, genericCheck, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Circuit.Kimchi (verifyCircuit, verifyCircuitM)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Circuit.RandomOracle (Digest(..), hash2)
import Snarky.Constraint.Kimchi (KimchiConstraint, eval, initialState)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, chooseInt, randomSampleOne, vectorOf)
import Test.Snarky.Circuit.Utils (circuitSpec', circuitSpecPure', satisfied)
import Test.Spec (SpecT, beforeAll, describe, it)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------

-- | Tree reference type alias (using Account as leaf type)
type TreeRef d f v = Ref (SMT.MerkleTree d (Digest (F f)) v)

-- | Monad that reads tree from a Ref
newtype MerkleRefM d f v a = MerkleRefM (ReaderT (TreeRef d f v) Effect a)

derive instance Newtype (MerkleRefM d f v a) _
derive newtype instance Functor (MerkleRefM d f v)
derive newtype instance Apply (MerkleRefM d f v)
derive newtype instance Applicative (MerkleRefM d f v)
derive newtype instance Bind (MerkleRefM d f v)
derive newtype instance Monad (MerkleRefM d f v)
derive newtype instance MonadEffect (MerkleRefM d f v)

runMerkleRefM :: forall d f v. TreeRef d f v -> MerkleRefM d f v ~> Effect
runMerkleRefM tree (MerkleRefM m) = runReaderT m tree

getTreeRef :: forall d f v. MerkleRefM d f v (SMT.MerkleTree d (Digest (F f)) v)
getTreeRef = MerkleRefM $ ask >>= \ref -> liftEffect $ read ref

modifyTreeRef
  :: forall d f v
   . (SMT.MerkleTree d (Digest (F f)) v -> SMT.MerkleTree d (Digest (F f)) v)
  -> MerkleRefM d f v Unit
modifyTreeRef f = MerkleRefM $ ask >>= \ref -> liftEffect do
  tree <- read ref
  write (f tree) ref

-- | Instance for Ref-based testing (reads/writes tree via Ref)
instance
  ( Reflectable d Int
  , PoseidonField f
  , CircuitType f v var
  , CheckedType f (KimchiConstraint f) var
  , MerkleHashable v (Digest (F f))
  ) =>
  CMT.MerkleRequestM (MerkleRefM d f v) f v d var where
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
  , CircuitType f (Account (F f)) (Account (FVar f))
  ) =>
  CMT.MerkleRequestM (MerkleCompileM d f) f (Account (F f)) d (Account (FVar f)) where
  getElement _ = unsafeThrow "unhandled request: getElement"
  getPath _ = unsafeThrow "unhandled request: getPath"
  setValue _ _ = unsafeThrow "unhandled request: setValue"

-- | Generate a random filled merkle tree of depth d (with Account leaves)
genTree
  :: forall d f
   . Reflectable d Int
  => PoseidonField f
  => Proxy d
  -> Gen (SMT.MerkleTree d (Digest (F f)) (Account (F f)))
genTree _ = do
  let numElements = 2 `pow` (reflectType (Proxy @d))
  vs <- vectorOf numElements (arbitrary @(Account (F f)))
  let
    nea = unsafePartial fromJust $ NEA.fromArray vs
    { head: a, tail: as } = NEA.uncons nea

    base :: SMT.MerkleTree d (Digest (F f)) (Account (F f))
    base = SMT.create a
  pure $ SMT.addMany base (List.fromFoldable as)

--------------------------------------------------------------------------------
-- | Account type for merkle tree leaves
-- | Uses two field elements: publicKey and tokenBalance
newtype Account f = Account { publicKey :: f, tokenBalance :: f }

derive instance Newtype (Account f) _
derive instance Generic (Account f) _
derive instance Eq f => Eq (Account f)
derive instance Functor Account

instance Show f => Show (Account f) where
  show (Account { publicKey, tokenBalance }) =
    "Account { publicKey: " <> show publicKey <> ", tokenBalance: " <> show tokenBalance <> " }"

instance Arbitrary f => Arbitrary (Account f) where
  arbitrary = Account <$> ({ publicKey: _, tokenBalance: _ } <$> arbitrary <*> arbitrary)

-- | CircuitType instance: Account (F f) <-> Account (FVar f)
instance CircuitType f (Account (F f)) (Account (FVar f)) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(Account (F f))
  fieldsToVar = genericFieldsToVar @(Account (F f))

instance CheckedType f c (Account (FVar f)) where
  check = genericCheck

-- | Pure Hashable instance for Account (F f)
instance PoseidonField f => Hashable (Account (F f)) (Digest (F f)) where
  hash = case _ of
    Nothing -> Digest $ F $ Poseidon.hash []
    Just (Account { publicKey: F pk, tokenBalance: F tb }) ->
      Digest $ F $ Poseidon.hash [ pk, tb ]

-- | Circuit Hashable instance for Account (FVar f)
instance
  ( CircuitM f (KimchiConstraint f) t m
  , PoseidonField f
  ) =>
  Hashable (Account (FVar f)) (Snarky (KimchiConstraint f) t m (Digest (FVar f))) where
  hash = case _ of
    Nothing -> hash2 (const_ zero) (const_ zero)
    Just (Account { publicKey, tokenBalance }) -> hash2 publicKey tokenBalance

-- | MerkleHashable instance for pure Account
instance PoseidonField f => MerkleHashable (Account (F f)) (Digest (F f))

-- | MerkleHashable instance for circuit Account
instance
  ( CircuitM f (KimchiConstraint f) t m
  , PoseidonField f
  ) =>
  MerkleHashable (Account (FVar f)) (Snarky (KimchiConstraint f) t m (Digest (FVar f)))

--------------------------------------------------------------------------------

-- | Test for impliedRoot circuit - pure computation, no MerkleRequestM needed
impliedRootSpec
  :: forall f f' g' d
   . Kimchi.KimchiVerify f f'
  => CircuitGateConstructor f g'
  => Reflectable d Int
  => Proxy f
  -> Proxy d
  -> Aff Unit
impliedRootSpec _ pd = do
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

  circuitSpecPure' 100
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
  => Proxy f
  -> Proxy d
  -> Aff Unit
getSpec _ pd = do
  tree <- liftEffect $ randomSampleOne (genTree pd)

  let
    testFunction :: SMT.Address d -> Account (F f)
    testFunction addr = unsafePartial $ fromJust $ SMT.get tree addr

    rootVar =
      let
        Digest (F r) = SMT.root tree
      in
        Digest $ const_ r

    circuit
      :: forall t @m
       . CMT.MerkleRequestM m f (Account (F f)) d (Account (FVar f))
      => CircuitM f (KimchiConstraint f) t m
      => SMT.AddressVar d f
      -> Snarky (KimchiConstraint f) t m (Account (FVar f))
    circuit addr = CMT.get addr rootVar

    solver = makeSolver (Proxy @(KimchiConstraint f)) circuit
    s =
      runMerkleCompileM $
        compile
          (Proxy @(Address d))
          (Proxy @(Account (F f)))
          (Proxy @(KimchiConstraint f))
          (circuit @(MerkleCompileM d f))
          initialState
    gen =
      let
        maxAddress = (2 `pow` reflectType (Proxy @d)) - 1
      in
        Address <<< BigInt.fromInt <$> chooseInt 0 maxAddress

  ref <- liftEffect $ Ref.new tree

  circuitSpec' 100 (runMerkleRefM ref)
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
  => Proxy f
  -> Proxy d
  -> Aff Unit
fetchAndUpdateSpec _ pd = do
  initialTree <- liftEffect $ randomSampleOne (genTree pd)

  let
    -- Modification function: add one to tokenBalance (uses Semiring instance for Snarky)
    modifyF
      :: forall t m
       . CircuitM f (KimchiConstraint f) t m
      => Account (FVar f)
      -> Snarky (KimchiConstraint f) t m (Account (FVar f))
    modifyF (Account { publicKey, tokenBalance }) = do
      newBalance <- pure tokenBalance + one
      pure $ Account { publicKey, tokenBalance: newBalance }

    -- Pure modification for test function
    modifyPure :: Account (F f) -> Account (F f)
    modifyPure (Account { publicKey, tokenBalance }) =
      Account { publicKey, tokenBalance: tokenBalance + one }

    -- Test function: compute expected output from initial tree state
    -- Note: tree gets reset before each test case
    testFunction :: SMT.Address d -> { root :: Digest (F f), old :: Account (F f), new :: Account (F f) }
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
       . CMT.MerkleRequestM m f (Account (F f)) d (Account (FVar f))
      => CircuitM f (KimchiConstraint f) t m
      => SMT.AddressVar d f
      -> Snarky (KimchiConstraint f) t m { root :: Digest (FVar f), old :: Account (FVar f), new :: Account (FVar f) }
    circuit addr = CMT.fetchAndUpdate addr rootVar modifyF

    solver = makeSolver (Proxy @(KimchiConstraint f)) circuit
    s =
      runMerkleCompileM $
        compile
          (Proxy @(Address d))
          (Proxy @{ root :: Digest (F f), old :: Account (F f), new :: Account (F f) })
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
    natWithReset :: MerkleRefM d f (Account (F f)) ~> Effect
    natWithReset m = do
      write initialTree ref
      runMerkleRefM ref m

  circuitSpec' 100 natWithReset
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

--------------------------------------------------------------------------------

-- | Test for update circuit - takes old and new values as inputs
updateSpec
  :: forall f f' g' d
   . Kimchi.KimchiVerify f f'
  => CircuitGateConstructor f g'
  => Reflectable d Int
  => Proxy f
  -> Proxy d
  -> Aff Unit
updateSpec _ pd = do
  initialTree <- liftEffect $ randomSampleOne (genTree pd)

  let
    -- Test function: compute expected new root
    testFunction
      :: Tuple (Address d) (Tuple (Account (F f)) (Account (F f)))
      -> Digest (F f)
    testFunction (Tuple addr (Tuple _old new)) =
      let
        -- Update the tree and get new root
        updatedTree = unsafePartial fromJust $ SMT.set initialTree addr new
      in
        SMT.root updatedTree

    rootVar =
      let
        Digest (F r) = SMT.root initialTree
      in
        Digest $ const_ r

    circuit
      :: forall t @m
       . CMT.MerkleRequestM m f (Account (F f)) d (Account (FVar f))
      => CircuitM f (KimchiConstraint f) t m
      => Tuple (SMT.AddressVar d f) (Tuple (Account (FVar f)) (Account (FVar f)))
      -> Snarky (KimchiConstraint f) t m (Digest (FVar f))
    circuit (Tuple addr (Tuple old new)) = CMT.update addr rootVar old new

    solver = makeSolver (Proxy @(KimchiConstraint f)) circuit
    s =
      runMerkleCompileM $
        compile
          (Proxy @(Tuple (Address d) (Tuple (Account (F f)) (Account (F f)))))
          (Proxy @(Digest (F f)))
          (Proxy @(KimchiConstraint f))
          (circuit @(MerkleCompileM d f))
          initialState

    -- Generator: produce (address, oldValue, newValue) from fixed tree
    gen = do
      addrInt <- chooseInt 0 ((2 `pow` reflectType pd) - 1)
      newVal <- arbitrary
      let
        addr = Address $ BigInt.fromInt addrInt
        oldVal = unsafePartial fromJust $ SMT.get initialTree addr
      pure $ Tuple addr (Tuple oldVal newVal)

  ref <- liftEffect $ Ref.new initialTree

  -- Reset tree before each test case
  let
    natWithReset :: MerkleRefM d f (Account (F f)) ~> Effect
    natWithReset m = do
      write initialTree ref
      runMerkleRefM ref m

  circuitSpec' 100 natWithReset
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

spec :: SpecT Aff Unit Aff Unit
spec = beforeAll genSize $
  describe "Merkle Tree Circuit Specs" do
    describe "impliedRoot" do
      it "Vesta" \d ->
        reifyType d \pd -> do
          impliedRootSpec (Proxy @Vesta.ScalarField) pd
      it "Pallas" \d ->
        reifyType d \pd ->
          impliedRootSpec (Proxy @Pallas.ScalarField) pd
    describe "get" do
      it "Vesta" \d ->
        reifyType d \pd -> do
          getSpec (Proxy @Vesta.ScalarField) pd
      it "Pallas" \d ->
        reifyType d \pd ->
          getSpec (Proxy @Pallas.ScalarField) pd
    describe "fetchAndUpdate" do
      it "Vesta" \d ->
        reifyType d \pd ->
          fetchAndUpdateSpec (Proxy @Vesta.ScalarField) pd
      it "Pallas" \d ->
        reifyType d \pd ->
          fetchAndUpdateSpec (Proxy @Pallas.ScalarField) pd
    describe "update" do
      it "Vesta" \d ->
        reifyType d \pd ->
          updateSpec (Proxy @Vesta.ScalarField) pd
      it "Pallas" \d ->
        reifyType d \pd ->
          updateSpec (Proxy @Pallas.ScalarField) pd
  where
  genSize = liftEffect do
    d <- randomSampleOne $ chooseInt 3 8
    Console.log $ "Running MerkleTreeSpec Circuit Spec with depth " <> show d
    pure d