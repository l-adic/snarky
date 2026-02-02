module Test.Snarky.Circuit.SparseMerkleTree
  ( spec
  ) where

import Prelude

import Control.Monad.Reader (ReaderT, ask)
import Data.Generic.Rep (class Generic)
import Data.Identity (Identity(..))
import Data.Int (pow)
import Data.Maybe (Maybe(..))
import Data.MerkleTree.Hashable (class Hashable, class MerkleHashable, defaultHash, hash)
import Data.MerkleTree.Sized (Address(..), AddressVar, Path(..))
import Data.MerkleTree.Sized as Sized
import Data.MerkleTree.Sparse as Sparse
import Data.Newtype (class Newtype, un)
import Data.Reflectable (class Reflectable, reflectType, reifyType)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Class.Console as Console
import Effect.Exception.Unsafe (unsafeThrow)
import Effect.Ref (Ref, read, write)
import JS.BigInt as BigInt
import Poseidon (class PoseidonField)
import Poseidon as Poseidon
import Snarky.Backend.Compile (compile, makeSolver)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.DSL (class CheckedType, class CircuitM, class CircuitType, F(..), FVar, Snarky, genericCheck, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Circuit.MerkleTree.Sparse as SparseCircuit
import Snarky.Circuit.RandomOracle (Digest(..), hash2)
import Snarky.Constraint.Kimchi (KimchiConstraint, eval, initialState)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, chooseInt, randomSampleOne)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (SpecT, beforeAll, describe, it)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------

-- | Sparse tree reference type alias
type SparseTreeRef d f v = Ref (Sparse.SparseMerkleTree d (Digest (F f)) v)

-- | Monad that reads sparse tree from a Ref
newtype SparseMerkleRefM d f v a = SparseMerkleRefM (ReaderT (SparseTreeRef d f v) Effect a)

derive instance Newtype (SparseMerkleRefM d f v a) _
derive newtype instance Functor (SparseMerkleRefM d f v)
derive newtype instance Apply (SparseMerkleRefM d f v)
derive newtype instance Applicative (SparseMerkleRefM d f v)
derive newtype instance Bind (SparseMerkleRefM d f v)
derive newtype instance Monad (SparseMerkleRefM d f v)
derive newtype instance MonadEffect (SparseMerkleRefM d f v)

getSparseTreeRef :: forall d f v. SparseMerkleRefM d f v (Sparse.SparseMerkleTree d (Digest (F f)) v)
getSparseTreeRef = SparseMerkleRefM $ ask >>= \ref -> liftEffect $ read ref

modifySparseTreeRef
  :: forall d f v
   . (Sparse.SparseMerkleTree d (Digest (F f)) v -> Sparse.SparseMerkleTree d (Digest (F f)) v)
  -> SparseMerkleRefM d f v Unit
modifySparseTreeRef f = SparseMerkleRefM $ ask >>= \ref -> liftEffect do
  tree <- read ref
  write (f tree) ref

-- | Convert between Sized.Address and Sparse.Address (they're structurally identical)
toSparseAddr :: forall d. Address d -> Sparse.Address d
toSparseAddr (Address a) = Sparse.Address a

-- | Convert between Sized.Path and Sparse.Path (they're structurally identical)
fromSparsePath :: forall d hash. Sparse.Path d hash -> Path d hash
fromSparsePath (Sparse.Path v) = Path v

-- | Instance for Ref-based testing (reads/writes sparse tree via Ref)
instance
  ( Reflectable d Int
  , PoseidonField f
  , CircuitType f v var
  , CheckedType f (KimchiConstraint f) var
  , MerkleHashable v (Digest (F f))
  ) =>
  CMT.MerkleRequestM (SparseMerkleRefM d f v) f v d var where
  getElement (Address addr) = do
    tree <- getSparseTreeRef
    let
      sparseAddr = Sparse.Address addr
      mval = Sparse.get tree sparseAddr
      path = Sparse.getWitness sparseAddr tree
    case mval of
      Just v -> pure { value: v, path: fromSparsePath path }
      Nothing ->
        -- For sparse trees, "empty" addresses are valid - they just have the default hash
        -- We need the value type to have a default, but for now we fail
        unsafeThrow "getElement: address not set in sparse tree"

  getPath (Address addr) = do
    tree <- getSparseTreeRef
    let sparseAddr = Sparse.Address addr
    pure $ fromSparsePath $ Sparse.getWitness sparseAddr tree

  setValue (Address addr) v = do
    modifySparseTreeRef \tree ->
      case Sparse.set (Sparse.Address addr) v tree of
        Just tree' -> tree'
        Nothing -> unsafeThrow "setValue: invalid address"

-- | Newtype wrapper for compilation phase (throws on any request)
newtype SparseCompileM :: Int -> Type -> Type -> Type
newtype SparseCompileM d f a = SparseCompileM (Identity a)

derive instance Newtype (SparseCompileM d f a) _
derive newtype instance Functor (SparseCompileM d f)
derive newtype instance Apply (SparseCompileM d f)
derive newtype instance Applicative (SparseCompileM d f)
derive newtype instance Bind (SparseCompileM d f)
derive newtype instance Monad (SparseCompileM d f)

-- | Instance for compilation phase - throws on any request
instance
  ( Reflectable d Int
  , PoseidonField f
  , CircuitType f (Account (F f)) (Account (FVar f))
  ) =>
  CMT.MerkleRequestM (SparseCompileM d f) f (Account (F f)) d (Account (FVar f)) where
  getElement _ = unsafeThrow "unhandled request: getElement"
  getPath _ = unsafeThrow "unhandled request: getPath"
  setValue _ _ = unsafeThrow "unhandled request: setValue"

--------------------------------------------------------------------------------
-- | Account type for merkle tree leaves (reusing from circuit tests)
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

-- | Generate a sparse tree with some random addresses populated
genSparseTree
  :: forall d f
   . Reflectable d Int
  => PoseidonField f
  => Proxy d
  -> Gen (Sparse.SparseMerkleTree d (Digest (F f)) (Account (F f)))
genSparseTree _ = go 0 Sparse.empty
  where
  go i tree
    | i >= 10 = pure tree
    | otherwise = do
        addr <- chooseInt 0 ((2 `pow` (reflectType (Proxy @d))) - 1)
        value <- arbitrary @(Account (F f))
        let
          tree' = case Sparse.set (Sparse.Address $ BigInt.fromInt addr) value tree of
            Just t -> t
            Nothing -> tree
        go (i + 1) tree'

--------------------------------------------------------------------------------

-- | Test for impliedRoot circuit - pure computation
sparseImpliedRootSpec
  :: forall f f' g' d
   . Kimchi.KimchiVerify f f'
  => CircuitGateConstructor f g'
  => Reflectable d Int
  => Proxy f
  -> Proxy d
  -> Aff Unit
sparseImpliedRootSpec _ pd = do
  tree <- liftEffect $ randomSampleOne (genSparseTree pd)

  let
    -- Expected: use pure impliedRoot from Sized
    testFunction
      :: Tuple (Address d) (Tuple (Digest (F f)) (Path d (Digest (F f))))
      -> Digest (F f)
    testFunction (Tuple addr (Tuple entryHash path)) =
      Sized.impliedRoot addr entryHash path

    circuit
      :: forall t
       . CircuitM f (KimchiConstraint f) t Identity
      => Tuple (AddressVar d f) (Tuple (Digest (FVar f)) (Path d (Digest (FVar f))))
      -> Snarky (KimchiConstraint f) t Identity (Digest (FVar f))
    circuit (Tuple addr (Tuple entryHash (Path pathVec))) =
      SparseCircuit.impliedRoot addr entryHash (Sized.Path pathVec)

    solver = makeSolver (Proxy @(KimchiConstraint f)) circuit
    s = un Identity $
      compile
        (Proxy @(Tuple (Address d) (Tuple (Digest (F f)) (Path d (Digest (F f))))))
        (Proxy @(Digest (F f)))
        (Proxy @(KimchiConstraint f))
        circuit
        initialState

    -- Generator: produce valid (address, entryHash, path) triples from sparse tree
    gen = do
      addrInt <- chooseInt 0 ((2 `pow` reflectType pd) - 1)
      let
        addr = Address $ BigInt.fromInt addrInt
        sparseAddr = toSparseAddr addr
        melem = Sparse.get tree sparseAddr
        entryHash = case melem of
          Just v -> hash (Just v)
          Nothing -> defaultHash @(Account (F f))
        path = fromSparsePath $ Sparse.getWitness sparseAddr tree
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

-- | Test for checkAndUpdate circuit
sparseCheckAndUpdateSpec
  :: forall f f' g' d
   . Kimchi.KimchiVerify f f'
  => CircuitGateConstructor f g'
  => Reflectable d Int
  => Proxy f
  -> Proxy d
  -> Aff Unit
sparseCheckAndUpdateSpec _ pd = do
  tree <- liftEffect $ randomSampleOne (genSparseTree pd)

  let
    -- Test function: given (addr, oldHash, newHash, path, oldRoot), compute new root
    testFunction
      :: { addr :: Address d
         , oldValueHash :: Digest (F f)
         , newValueHash :: Digest (F f)
         , path :: Path d (Digest (F f))
         , oldRoot :: Digest (F f)
         }
      -> Digest (F f)
    testFunction { addr, newValueHash, path } =
      Sized.impliedRoot addr newValueHash path

    circuit
      :: forall t
       . CircuitM f (KimchiConstraint f) t Identity
      => { addr :: AddressVar d f
         , oldValueHash :: Digest (FVar f)
         , newValueHash :: Digest (FVar f)
         , path :: Path d (Digest (FVar f))
         , oldRoot :: Digest (FVar f)
         }
      -> Snarky (KimchiConstraint f) t Identity (Digest (FVar f))
    circuit { addr, oldValueHash, newValueHash, path: Path pathVec, oldRoot } =
      SparseCircuit.checkAndUpdate addr oldValueHash newValueHash (Sized.Path pathVec) oldRoot

    solver = makeSolver (Proxy @(KimchiConstraint f)) circuit
    s = un Identity $
      compile
        ( Proxy
            @
            { addr :: Address d
            , oldValueHash :: Digest (F f)
            , newValueHash :: Digest (F f)
            , path :: Path d (Digest (F f))
            , oldRoot :: Digest (F f)
            }
        )
        (Proxy @(Digest (F f)))
        (Proxy @(KimchiConstraint f))
        circuit
        initialState

    -- Generator: produce valid inputs
    gen = do
      addrInt <- chooseInt 0 ((2 `pow` reflectType pd) - 1)
      newValue <- arbitrary @(Account (F f))
      let
        addr = Address $ BigInt.fromInt addrInt
        sparseAddr = toSparseAddr addr
        melem = Sparse.get tree sparseAddr
        oldValueHash = case melem of
          Just v -> hash (Just v)
          Nothing -> defaultHash @(Account (F f))
        newValueHash = hash (Just newValue)
        path = fromSparsePath $ Sparse.getWitness sparseAddr tree
        oldRoot = Sparse.root tree
      pure { addr, oldValueHash, newValueHash, path, oldRoot }

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

spec :: SpecT Aff Unit Aff Unit
spec = beforeAll genSize $
  describe "Sparse Merkle Tree Circuit Specs" do
    describe "impliedRoot" do
      it "Vesta" \d ->
        reifyType d \pd -> do
          sparseImpliedRootSpec (Proxy @Vesta.ScalarField) pd
      it "Pallas" \d ->
        reifyType d \pd ->
          sparseImpliedRootSpec (Proxy @Pallas.ScalarField) pd
    describe "checkAndUpdate" do
      it "Vesta" \d ->
        reifyType d \pd -> do
          sparseCheckAndUpdateSpec (Proxy @Vesta.ScalarField) pd
      it "Pallas" \d ->
        reifyType d \pd ->
          sparseCheckAndUpdateSpec (Proxy @Pallas.ScalarField) pd
  where
  genSize = liftEffect do
    d <- randomSampleOne $ chooseInt 3 6
    Console.log $ "Running Sparse MerkleTree Circuit Spec with depth " <> show d
    pure d
