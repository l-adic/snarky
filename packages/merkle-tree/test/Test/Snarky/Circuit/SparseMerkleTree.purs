module Test.Snarky.Circuit.SparseMerkleTree
  ( spec
  ) where

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Generic.Rep (class Generic)
import Data.Int (pow)
import Data.Maybe (Maybe(..))
import Data.MerkleTree.Hashable (class Hashable, defaultHash, hashLeaf)
import Data.MerkleTree.Sized (Address(..), AddressVar, Path(..))
import Data.MerkleTree.Sized as Sized
import Data.MerkleTree.Sparse as Sparse
import Data.Newtype (class Newtype)
import Data.Reflectable (class Reflectable, reflectType, reifyType)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Class.Console as Console
import JS.BigInt as BigInt
import Poseidon (class PoseidonField)
import Run (EFFECT)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, F(..), FVar, Snarky, genericCheck, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Circuit.Kimchi (verifyCircuit)
import Snarky.Circuit.MerkleTree.Sparse as SparseCircuit
import Snarky.Circuit.RandomOracle (Digest)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, chooseInt, randomSampleOne)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTest', satisfied)
import Test.Spec (SpecT, beforeAll, describe, it)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))

--------------------------------------------------------------------------------

-- | Convert between Sized.Address and Sparse.Address (they're structurally identical)
toSparseAddr :: forall d. Address d -> Sparse.Address d
toSparseAddr (Address a) = Sparse.Address a

-- | Convert between Sized.Path and Sparse.Path (they're structurally identical)
fromSparsePath :: forall d hash. Sparse.Path d hash -> Path d hash
fromSparsePath (Sparse.Path v) = Path v

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

-- | CircuitType instance: value side is raw `f`; `F f` is the internal
-- | leaf marker the generic deriving needs (reached by `coerce`).
instance CircuitType f (Account f) (Account (FVar f)) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy :: Proxy (Account (F f)))
  valueToFields a = genericValueToFields (coerce a :: Account (F f))
  fieldsToValue fs = coerce (genericFieldsToValue fs :: Account (F f))
  varToFields = genericVarToFields @(Account (F f))
  fieldsToVar = genericFieldsToVar @(Account (F f))

instance CheckedType f c (Account (FVar f)) where
  check = genericCheck

-- | Flatten an account to its leaf field elements; the merkle layer's
-- | `hashLeaf` turns this into a digest (and `MerkleHashable` is derived).
instance Hashable (Account a) a where
  toHashInput (Account { publicKey, tokenBalance }) = [ publicKey, tokenBalance ]

--------------------------------------------------------------------------------

-- | Generate a sparse tree with some random addresses populated
genSparseTree
  :: forall d f
   . Reflectable d Int
  => PoseidonField f
  => Proxy d
  -> Gen (Sparse.SparseMerkleTree d (Digest f) (Account f))
genSparseTree _ = go 0 Sparse.empty
  where
  go i tree
    | i >= 10 = pure tree
    | otherwise = do
        addr <- chooseInt 0 ((2 `pow` (reflectType (Proxy @d))) - 1)
        value <- arbitrary @(Account f)
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
  => TestConfig f (KimchiGate f) (AuxState f)
  -> Proxy f
  -> Proxy d
  -> Aff Unit
sparseImpliedRootSpec cfg _ pd = do
  tree <- liftEffect $ randomSampleOne (genSparseTree pd)

  let
    -- Expected: use pure impliedRoot from Sized
    testFunction
      :: Tuple (Address d) (Tuple (Digest f) (Path d (Digest f)))
      -> Digest f
    testFunction (Tuple addr (Tuple entryHash path)) =
      Sized.impliedRoot addr entryHash path

    circuit
      :: Tuple (AddressVar d f) (Tuple (Digest (FVar f)) (Path d (Digest (FVar f))))
      -> Snarky f (KimchiConstraint f) () (Digest (FVar f))
    circuit (Tuple addr (Tuple entryHash (Path pathVec))) =
      SparseCircuit.impliedRoot addr entryHash (Sized.Path pathVec)

    -- Generator: produce valid (address, entryHash, path) triples from sparse tree
    gen = do
      addrInt <- chooseInt 0 ((2 `pow` reflectType pd) - 1)
      let
        addr = Address $ BigInt.fromInt addrInt
        sparseAddr = toSparseAddr addr
        melem = Sparse.get tree sparseAddr
        entryHash = case melem of
          Just v -> hashLeaf (Just v)
          Nothing -> defaultHash @(Account f)
        path = fromSparsePath $ Sparse.getWitness sparseAddr tree
      pure $ Tuple addr (Tuple entryHash path)

  { builtState: s, solver } <- circuitTest' @f
    cfg
    (NEA.singleton { testFunction: satisfied testFunction, input: QuickCheck 100 gen })
    circuit

  liftEffect $ verifyCircuit { s, gen, solver }

--------------------------------------------------------------------------------

-- | Test for checkAndUpdate circuit
sparseCheckAndUpdateSpec
  :: forall f f' g' d
   . Kimchi.KimchiVerify f f'
  => CircuitGateConstructor f g'
  => Reflectable d Int
  => TestConfig f (KimchiGate f) (AuxState f)
  -> Proxy f
  -> Proxy d
  -> Aff Unit
sparseCheckAndUpdateSpec cfg _ pd = do
  tree <- liftEffect $ randomSampleOne (genSparseTree pd)

  let
    -- Test function: given (addr, oldHash, newHash, path, oldRoot), compute new root
    testFunction
      :: { addr :: Address d
         , oldValueHash :: Digest f
         , newValueHash :: Digest f
         , path :: Path d (Digest f)
         , oldRoot :: Digest f
         }
      -> Digest f
    testFunction { addr, newValueHash, path } =
      Sized.impliedRoot addr newValueHash path

    circuit
      :: { addr :: AddressVar d f
         , oldValueHash :: Digest (FVar f)
         , newValueHash :: Digest (FVar f)
         , path :: Path d (Digest (FVar f))
         , oldRoot :: Digest (FVar f)
         }
      -> Snarky f (KimchiConstraint f) () (Digest (FVar f))
    circuit { addr, oldValueHash, newValueHash, path: Path pathVec, oldRoot } =
      SparseCircuit.checkAndUpdate addr oldValueHash newValueHash (Sized.Path pathVec) oldRoot

    -- Generator: produce valid inputs
    gen = do
      addrInt <- chooseInt 0 ((2 `pow` reflectType pd) - 1)
      newValue <- arbitrary @(Account f)
      let
        addr = Address $ BigInt.fromInt addrInt
        sparseAddr = toSparseAddr addr
        melem = Sparse.get tree sparseAddr
        oldValueHash = case melem of
          Just v -> hashLeaf (Just v)
          Nothing -> defaultHash @(Account f)
        newValueHash = hashLeaf (Just newValue)
        path = fromSparsePath $ Sparse.getWitness sparseAddr tree
        oldRoot = Sparse.root tree
      pure { addr, oldValueHash, newValueHash, path, oldRoot }

  { builtState: s, solver } <- circuitTest' @f
    cfg
    (NEA.singleton { testFunction: satisfied testFunction, input: QuickCheck 100 gen })
    circuit

  liftEffect $ verifyCircuit { s, gen, solver }

--------------------------------------------------------------------------------

spec :: (forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)) -> SpecT Aff Unit Aff Unit
spec cfg = beforeAll genSize $
  describe "Sparse Merkle Tree Circuit Specs" do
    describe "impliedRoot" do
      it "Vesta" \d ->
        reifyType d \pd -> do
          sparseImpliedRootSpec cfg (Proxy @Vesta.ScalarField) pd
      it "Pallas" \d ->
        reifyType d \pd ->
          sparseImpliedRootSpec cfg (Proxy @Pallas.ScalarField) pd
    describe "checkAndUpdate" do
      it "Vesta" \d ->
        reifyType d \pd -> do
          sparseCheckAndUpdateSpec cfg (Proxy @Vesta.ScalarField) pd
      it "Pallas" \d ->
        reifyType d \pd ->
          sparseCheckAndUpdateSpec cfg (Proxy @Pallas.ScalarField) pd
  where
  genSize = liftEffect do
    d <- randomSampleOne $ chooseInt 3 6
    Console.log $ "Running Sparse MerkleTree Circuit Spec with depth " <> show d
    pure d
