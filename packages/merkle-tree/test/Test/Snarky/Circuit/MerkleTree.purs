module Test.Snarky.Circuit.MerkleTree
  ( spec
  ) where

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Functor.Variant (case_, on)
import Data.Generic.Rep (class Generic)
import Data.Int (pow)
import Data.List as List
import Data.Maybe (Maybe(..), fromJust)
import Data.MerkleTree.Hashable (class Hashable, class MerkleHashable, hashLeaf)
import Data.MerkleTree.Sized (Address(..))
import Data.MerkleTree.Sized as SMT
import Data.Newtype (class Newtype)
import Data.Reflectable (class Reflectable, reflectType, reifyType)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Class.Console as Console
import Effect.Exception (throw)
import Effect.Ref (Ref, read, write)
import Effect.Ref as Ref
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Poseidon (class PoseidonField)
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (AdviceHandler(..))
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, F(..), FVar, Snarky, const_, genericCheck, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Circuit.Kimchi (verifyCircuit, verifyCircuitM)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, chooseInt, randomSampleOne, vectorOf)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTest', circuitTestM', satisfied)
import Test.Spec (SpecT, beforeAll, describe, it)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))

--------------------------------------------------------------------------------

-- | Tree reference type alias (using Account as leaf type)
type TreeRef d f v = Ref (SMT.MerkleTree d (Digest f) v)

-- | Monad that reads tree from a Ref
-- | Run handler answering MERKLE requests against a Ref-held tree.
type MerkleRow d f v = CMT.MERKLE f v d + ()

runMerkleRef
  :: forall d f v
   . Reflectable d Int
  => PoseidonField f
  => MerkleHashable v (Digest f)
  => TreeRef d f v
  -> AdviceHandler (MerkleRow d f v)
runMerkleRef ref = AdviceHandler (on CMT._merkle handler case_)
  where
  readTree = read ref

  handler :: CMT.MerkleF f v d ~> Effect
  handler = case _ of
    CMT.GetElement addr k -> readTree >>= \tree ->
      case SMT.get tree addr, SMT.getPath tree addr of
        Just v, Just pth -> pure (k { value: v, path: pth })
        _, _ -> throw "getElement: invalid address"
    CMT.GetPath addr k -> readTree >>= \tree ->
      case SMT.getPath tree addr of
        Just pth -> pure (k pth)
        Nothing -> throw "getPath: invalid address"
    CMT.SetValue addr v k -> do
      tree <- readTree
      case SMT.set tree addr v of
        Just tree' -> Ref.write tree' ref
        Nothing -> throw "setValue: invalid address"
      pure k

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

-- | CircuitType instance: value side is the raw field `f`; `F f` survives
-- | only as the internal leaf marker the generic deriving needs.
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

-- | Generate a random filled merkle tree of depth d (with Account leaves)
genTree
  :: forall d f
   . Reflectable d Int
  => PoseidonField f
  => Proxy d
  -> Gen (SMT.MerkleTree d (Digest f) (Account f))
genTree _ = do
  let numElements = 2 `pow` (reflectType (Proxy @d))
  vs <- vectorOf numElements (arbitrary @(Account f))
  let
    nea = unsafePartial fromJust $ NEA.fromArray vs
    { head: a, tail: as } = NEA.uncons nea

    base :: SMT.MerkleTree d (Digest f) (Account f)
    base = SMT.create a
  pure $ SMT.addMany base (List.fromFoldable as)

--------------------------------------------------------------------------------

-- | Test for impliedRoot circuit - pure computation, no MerkleRequestM needed
impliedRootSpec
  :: forall f f' g' d
   . Kimchi.KimchiVerify f f'
  => CircuitGateConstructor f g'
  => Reflectable d Int
  => TestConfig f (KimchiGate f) (AuxState f)
  -> Proxy f
  -> Proxy d
  -> Aff Unit
impliedRootSpec cfg _ pd = do
  tree <- liftEffect $ randomSampleOne (genTree pd)

  let
    -- Expected: use pure impliedRoot
    testFunction
      :: Tuple (Address d) (Tuple (Digest f) (SMT.Path d (Digest f)))
      -> Digest f
    testFunction (Tuple addr (Tuple entryHash path)) =
      SMT.impliedRoot addr entryHash path

    circuit
      :: Tuple (SMT.AddressVar d f) (Tuple (Digest (FVar f)) (SMT.Path d (Digest (FVar f))))
      -> Snarky f (KimchiConstraint f) () (Digest (FVar f))
    circuit (Tuple addr (Tuple entryHash path)) =
      CMT.impliedRoot addr entryHash path

    -- Generator: produce valid (address, entryHash, path) triples from fixed tree
    gen = do
      addrInt <- chooseInt 0 ((2 `pow` reflectType pd) - 1)
      let
        addr = Address $ BigInt.fromInt addrInt
        elem = unsafePartial fromJust $ SMT.get tree addr
        entryHash = hashLeaf (Just elem)
        path = unsafePartial fromJust $ SMT.getPath tree addr
      pure $ Tuple addr (Tuple entryHash path)

  { builtState: s, solver } <- circuitTest' @f
    cfg
    (NEA.singleton { testFunction: satisfied testFunction, input: QuickCheck 100 gen })
    circuit

  liftEffect $ verifyCircuit { s, gen, solver }

--------------------------------------------------------------------------------

-- | The get circuit for testing - polymorphic in monad m
getSpec
  :: forall f f' g' d
   . Kimchi.KimchiVerify f f'
  => CircuitGateConstructor f g'
  => Reflectable d Int
  => TestConfig f (KimchiGate f) (AuxState f)
  -> Proxy f
  -> Proxy d
  -> Aff Unit
getSpec cfg _ pd = do
  tree <- liftEffect $ randomSampleOne (genTree pd)

  let
    testFunction :: SMT.Address d -> Account f
    testFunction addr = unsafePartial $ fromJust $ SMT.get tree addr

    rootVar :: Digest (FVar f)
    rootVar =
      let
        Digest r = SMT.root tree
      in
        Digest $ const_ r

    circuit
      :: SMT.AddressVar d f
      -> Snarky f (KimchiConstraint f) (MerkleRow d f (Account f)) (Account (FVar f))
    circuit addr = CMT.get @(Account f) addr rootVar

    gen =
      let
        maxAddress = (2 `pow` reflectType (Proxy @d)) - 1
      in
        Address <<< BigInt.fromInt <$> chooseInt 0 maxAddress

  ref <- liftEffect $ Ref.new tree

  { builtState: s, solver } <- circuitTestM' @f
    { handler: runMerkleRef ref, beforeEach: pure unit }
    cfg
    (NEA.singleton { testFunction: satisfied testFunction, input: QuickCheck 100 gen })
    circuit

  liftEffect $ verifyCircuitM (runMerkleRef ref) { s, gen, solver }

--------------------------------------------------------------------------------

-- | Test for fetchAndUpdate circuit - modifies tree state
fetchAndUpdateSpec
  :: forall f f' g' d
   . Kimchi.KimchiVerify f f'
  => CircuitGateConstructor f g'
  => Reflectable d Int
  => TestConfig f (KimchiGate f) (AuxState f)
  -> Proxy f
  -> Proxy d
  -> Aff Unit
fetchAndUpdateSpec cfg _ pd = do
  initialTree <- liftEffect $ randomSampleOne (genTree pd)

  let
    -- Modification function: add one to tokenBalance (uses Semiring instance for Snarky)
    modifyF
      :: forall rr
       . Account (FVar f)
      -> Snarky f (KimchiConstraint f) rr (Account (FVar f))
    modifyF (Account { publicKey, tokenBalance }) = do
      newBalance <- pure tokenBalance + one
      pure $ Account { publicKey, tokenBalance: newBalance }

    -- Pure modification for test function
    modifyPure :: forall a. Semiring a => Account a -> Account a
    modifyPure (Account { publicKey, tokenBalance }) =
      Account { publicKey, tokenBalance: tokenBalance + one }

    -- Test function: compute expected output from initial tree state
    -- Note: tree gets reset before each test case
    testFunction :: SMT.Address d -> { root :: Digest f, old :: Account f, new :: Account f }
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
        Digest r = SMT.root initialTree
      in
        Digest $ const_ r

    circuit
      :: SMT.AddressVar d f
      -> Snarky f (KimchiConstraint f) (MerkleRow d f (Account f)) { root :: Digest (FVar f), old :: Account (FVar f), new :: Account (FVar f) }
    circuit addr = CMT.fetchAndUpdate @(Account f) addr rootVar modifyF

    gen =
      let
        maxAddress = (2 `pow` reflectType (Proxy @d)) - 1
      in
        Address <<< BigInt.fromInt <$> chooseInt 0 maxAddress

  ref <- liftEffect $ Ref.new initialTree

  -- Reset tree before each test case
  { builtState: s, solver } <- circuitTestM' @f
    { handler: runMerkleRef ref, beforeEach: write initialTree ref }
    cfg
    (NEA.singleton { testFunction: satisfied testFunction, input: QuickCheck 100 gen })
    circuit

  -- Reset for verify
  liftEffect $ write initialTree ref
  liftEffect $ verifyCircuitM (runMerkleRef ref) { s, gen, solver }

--------------------------------------------------------------------------------

-- | Test for update circuit - takes old and new values as inputs
updateSpec
  :: forall f f' g' d
   . Kimchi.KimchiVerify f f'
  => CircuitGateConstructor f g'
  => Reflectable d Int
  => TestConfig f (KimchiGate f) (AuxState f)
  -> Proxy f
  -> Proxy d
  -> Aff Unit
updateSpec cfg _ pd = do
  initialTree <- liftEffect $ randomSampleOne (genTree pd)

  let
    -- Test function: compute expected new root
    testFunction
      :: Tuple (Address d) (Tuple (Account f) (Account f))
      -> Digest f
    testFunction (Tuple addr (Tuple _old new)) =
      let
        -- Update the tree and get new root
        updatedTree = unsafePartial fromJust $ SMT.set initialTree addr new
      in
        SMT.root updatedTree

    rootVar =
      let
        Digest r = SMT.root initialTree
      in
        Digest $ const_ r

    circuit
      :: Tuple (SMT.AddressVar d f) (Tuple (Account (FVar f)) (Account (FVar f)))
      -> Snarky f (KimchiConstraint f) (MerkleRow d f (Account f)) (Digest (FVar f))
    circuit (Tuple addr (Tuple old new)) = CMT.update @(Account f) addr rootVar old new

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
  { builtState: s, solver } <- circuitTestM' @f
    { handler: runMerkleRef ref, beforeEach: write initialTree ref }
    cfg
    (NEA.singleton { testFunction: satisfied testFunction, input: QuickCheck 100 gen })
    circuit

  -- Reset for verify
  liftEffect $ write initialTree ref
  liftEffect $ verifyCircuitM (runMerkleRef ref) { s, gen, solver }

spec :: (forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)) -> SpecT Aff Unit Aff Unit
spec cfg = beforeAll genSize $
  describe "Merkle Tree Circuit Specs" do
    describe "impliedRoot" do
      it "Vesta" \d ->
        reifyType d \pd -> do
          impliedRootSpec cfg (Proxy @Vesta.ScalarField) pd
      it "Pallas" \d ->
        reifyType d \pd ->
          impliedRootSpec cfg (Proxy @Pallas.ScalarField) pd
    describe "get" do
      it "Vesta" \d ->
        reifyType d \pd -> do
          getSpec cfg (Proxy @Vesta.ScalarField) pd
      it "Pallas" \d ->
        reifyType d \pd ->
          getSpec cfg (Proxy @Pallas.ScalarField) pd
    describe "fetchAndUpdate" do
      it "Vesta" \d ->
        reifyType d \pd ->
          fetchAndUpdateSpec cfg (Proxy @Vesta.ScalarField) pd
      it "Pallas" \d ->
        reifyType d \pd ->
          fetchAndUpdateSpec cfg (Proxy @Pallas.ScalarField) pd
    describe "update" do
      it "Vesta" \d ->
        reifyType d \pd ->
          updateSpec cfg (Proxy @Vesta.ScalarField) pd
      it "Pallas" \d ->
        reifyType d \pd ->
          updateSpec cfg (Proxy @Pallas.ScalarField) pd
  where
  genSize = liftEffect do
    d <- randomSampleOne $ chooseInt 3 8
    Console.log $ "Running MerkleTreeSpec Circuit Spec with depth " <> show d
    pure d
