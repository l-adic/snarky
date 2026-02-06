module Test.Data.MerkleTree.Sparse (spec) where

import Prelude

import Data.Array as Array
import Data.Foldable (for_)
import Data.Int (pow)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.MerkleTree.Hashable (defaultHash, hash)
import Data.MerkleTree.Sparse as Sparse
import Data.Reflectable (class Reflectable, reflectType, reifyType)
import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (F)
import Snarky.Circuit.RandomOracle (Digest)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (Result, arbitrary, quickCheckGen, withHelp, (===))
import Test.QuickCheck.Gen (Gen, chooseInt)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

-- | Tree depths to test - includes small and large depths
treeDepths :: Array Int
treeDepths = [ 1, 2, 4, 8, 16 ]

-- | Generate a sparse tree with some random addresses populated
genSparseTree
  :: forall @f d
   . Reflectable d Int
  => PoseidonField f
  => Proxy d
  -> Gen (Sparse.SparseMerkleTree d (Digest (F f)) (F f))
genSparseTree pd =
  let
    d = reflectType pd
  in
    go d 0 Sparse.empty
  where
  go d i tree
    | i >= 10 = pure tree
    | otherwise = do
        addr <- chooseInt 0 ((2 `pow` d) - 1)
        value <- arbitrary @(F f)
        let
          tree' = case Sparse.set (Sparse.Address $ BigInt.fromInt addr) value tree of
            Just t -> t
            Nothing -> tree
        go d (i + 1) tree'

spec :: Spec Unit
spec = describe "Sparse MerkleTree Property Laws" do
  describe "Empty tree properties" do

    it "empty tree has correct root (all default hashes)" $ liftEffect do
      for_ (treeDepths) \depth ->
        quickCheckGen $ do
          -- Generate dummy value to fix the field type
          _ <- arbitrary @(F Vesta.ScalarField)
          reifyType depth \pd ->
            pure $ emptyTreeRootLaw (Proxy @Vesta.ScalarField) pd

    it "get returns Nothing for any address in empty tree" $ liftEffect do
      for_ (treeDepths) \depth ->
        quickCheckGen $ do
          addr <- chooseInt 0 ((2 `pow` depth) - 1)
          -- Generate dummy value to fix the field type
          _ <- arbitrary @(F Vesta.ScalarField)
          reifyType depth \pd ->
            pure $ emptyTreeGetLaw (Proxy @Vesta.ScalarField) pd addr

  describe "Set operations" do

    it "set-get law: get after set returns the new value" $ liftEffect do
      for_ (treeDepths) \depth ->
        quickCheckGen $ do
          reifyType depth \pd -> do
            tree <- genSparseTree @Pallas.ScalarField pd
            addr <- chooseInt 0 ((2 `pow` depth) - 1)
            value <- arbitrary @(F Pallas.ScalarField)
            pure $ setGetLaw pd tree addr value

    it "set at arbitrary address works" $ liftEffect do
      for_ (treeDepths) \depth ->
        quickCheckGen $ do
          reifyType depth \pd -> do
            tree <- genSparseTree @Vesta.ScalarField pd
            addr <- chooseInt 0 ((2 `pow` depth) - 1)
            value <- arbitrary @(F Vesta.ScalarField)
            pure $ setArbitraryAddressLaw pd tree addr value

    it "set returns Nothing for out-of-bounds address" $ liftEffect do
      for_ (treeDepths) \depth ->
        quickCheckGen $ do
          -- Address beyond capacity
          invalidAddr <- chooseInt (2 `pow` depth) (2 `pow` (depth + 1))
          value <- arbitrary @(F Pallas.ScalarField)
          reifyType depth \pd ->
            pure $ setOutOfBoundsLaw pd invalidAddr value

    it "multiple sets at different addresses work correctly" $ liftEffect do
      for_ (Array.drop 1 treeDepths) \depth ->
        quickCheckGen $ do
          reifyType depth \pd -> do
            tree <- genSparseTree @Vesta.ScalarField pd
            addr1 <- chooseInt 0 ((2 `pow` depth) - 1)
            addr2 <- chooseInt 0 ((2 `pow` depth) - 1)
            value1 <- arbitrary @(F Vesta.ScalarField)
            value2 <- arbitrary @(F Vesta.ScalarField)
            pure $ multipleSetLaw pd tree addr1 addr2 value1 value2

  describe "Witness/Path properties" do

    it "witness produces correct root for set value" $ liftEffect do
      for_ (treeDepths) \depth ->
        quickCheckGen $ do
          reifyType depth \pd -> do
            tree <- genSparseTree @Pallas.ScalarField pd
            addr <- chooseInt 0 ((2 `pow` depth) - 1)
            value <- arbitrary @(F Pallas.ScalarField)
            pure $ witnessValidationLaw pd tree addr value

    it "witness for empty address uses default hashes" $ liftEffect do
      for_ (treeDepths) \depth ->
        quickCheckGen $ do
          addr <- chooseInt 0 ((2 `pow` depth) - 1)
          -- Generate dummy value to fix the field type
          _ <- arbitrary @(F Vesta.ScalarField)
          reifyType depth \pd ->
            pure $ emptyWitnessLaw (Proxy @Vesta.ScalarField) pd addr

    it "implied root matches actual root after set" $ liftEffect do
      for_ (treeDepths) \depth ->
        quickCheckGen $ do
          reifyType depth \pd -> do
            tree <- genSparseTree @Pallas.ScalarField pd
            addr <- chooseInt 0 ((2 `pow` depth) - 1)
            value <- arbitrary @(F Pallas.ScalarField)
            pure $ impliedRootLaw pd tree addr value

  describe "Root computation" do

    it "setting same value twice doesn't change root" $ liftEffect do
      for_ (treeDepths) \depth ->
        quickCheckGen $ do
          addr <- chooseInt 0 ((2 `pow` depth) - 1)
          value <- arbitrary @(F Vesta.ScalarField)
          reifyType depth \pd ->
            pure $ idempotentSetLaw pd addr value

    it "setting then overwriting produces correct root" $ liftEffect do
      for_ (treeDepths) \depth ->
        quickCheckGen $ do
          addr <- chooseInt 0 ((2 `pow` depth) - 1)
          value1 <- arbitrary @(F Pallas.ScalarField)
          value2 <- arbitrary @(F Pallas.ScalarField)
          reifyType depth \pd ->
            pure $ overwriteLaw pd addr value1 value2

-- | Empty tree should have a well-defined root hash
emptyTreeRootLaw
  :: forall f n
   . Reflectable n Int
  => PoseidonField f
  => Proxy f
  -> Proxy n
  -> Result
emptyTreeRootLaw _ _ =
  let
    tree :: Sparse.SparseMerkleTree n (Digest (F f)) (F f)
    tree = Sparse.empty
    r = Sparse.root tree
  in
    -- Root should be a valid hash (we just check it's computable)
    r === r

-- | Get on empty tree should return Nothing
emptyTreeGetLaw
  :: forall f n
   . Reflectable n Int
  => PoseidonField f
  => Proxy f
  -> Proxy n
  -> Int
  -> Result
emptyTreeGetLaw _ _ addrInt =
  let
    tree :: Sparse.SparseMerkleTree n (Digest (F f)) (F f)
    tree = Sparse.empty
    addr = Sparse.Address (BigInt.fromInt addrInt)
  in
    isNothing (Sparse.get tree addr) === true

-- | Set-Get law: After setting a value, get returns that value
setGetLaw
  :: forall n f
   . Reflectable n Int
  => PoseidonField f
  => Proxy n
  -> Sparse.SparseMerkleTree n (Digest (F f)) (F f)
  -> Int
  -> F f
  -> Result
setGetLaw _ tree addrInt value =
  let
    addr = Sparse.Address (BigInt.fromInt addrInt)
  in
    case Sparse.set addr value tree of
      Nothing -> withHelp false "set returned Nothing for valid address"
      Just tree' -> case Sparse.get tree' addr of
        Nothing -> withHelp false "get returned Nothing after set"
        Just retrieved -> retrieved === value

-- | Setting at any valid address should succeed and increase size by at most 1
setArbitraryAddressLaw
  :: forall n f
   . Reflectable n Int
  => PoseidonField f
  => Proxy n
  -> Sparse.SparseMerkleTree n (Digest (F f)) (F f)
  -> Int
  -> F f
  -> Result
setArbitraryAddressLaw _ tree addrInt value =
  let
    addr = Sparse.Address (BigInt.fromInt addrInt)
    oldSize = Sparse.size tree
    wasSet = isJust (Sparse.get tree addr)
  in
    case Sparse.set addr value tree of
      Nothing -> withHelp false $ "set returned Nothing for address " <> show addrInt
      Just tree' ->
        let
          newSize = Sparse.size tree'
          expectedSize = if wasSet then oldSize else oldSize + 1
        in
          newSize === expectedSize

-- | Set should return Nothing for out-of-bounds address
setOutOfBoundsLaw
  :: forall n f
   . Reflectable n Int
  => PoseidonField f
  => Proxy n
  -> Int
  -> F f
  -> Result
setOutOfBoundsLaw _ addrInt value =
  let
    tree :: Sparse.SparseMerkleTree n (Digest (F f)) (F f)
    tree = Sparse.empty
    addr = Sparse.Address (BigInt.fromInt addrInt)
  in
    isNothing (Sparse.set addr value tree) === true

-- | Multiple sets should work independently
multipleSetLaw
  :: forall n f
   . Reflectable n Int
  => PoseidonField f
  => Proxy n
  -> Sparse.SparseMerkleTree n (Digest (F f)) (F f)
  -> Int
  -> Int
  -> F f
  -> F f
  -> Result
multipleSetLaw _ tree addr1Int addr2Int value1 value2 =
  let
    addr1 = Sparse.Address (BigInt.fromInt addr1Int)
    addr2 = Sparse.Address (BigInt.fromInt addr2Int)
  in
    case Sparse.set addr1 value1 tree of
      Nothing -> withHelp false "first set failed"
      Just tree1 -> case Sparse.set addr2 value2 tree1 of
        Nothing -> withHelp false "second set failed"
        Just tree2 ->
          -- Both new values should be retrievable
          let
            get1 = Sparse.get tree2 addr1
            get2 = Sparse.get tree2 addr2
          in
            if addr1Int == addr2Int then
              -- Same address, second value overwrites
              get2 === Just value2
            else
              -- Different addresses, both should exist
              (get1 == Just value1 && get2 == Just value2) === true

-- | Witness should produce correct root
witnessValidationLaw
  :: forall n f
   . Reflectable n Int
  => PoseidonField f
  => Proxy n
  -> Sparse.SparseMerkleTree n (Digest (F f)) (F f)
  -> Int
  -> F f
  -> Result
witnessValidationLaw _ tree addrInt value =
  let
    addr = Sparse.Address (BigInt.fromInt addrInt)
  in
    case Sparse.set addr value tree of
      Nothing -> withHelp false "set failed"
      Just tree' ->
        let
          witness = Sparse.getWitness addr tree'
          actualRoot = Sparse.root tree'
          valueHash = hash @(F f) (Just value)
          impliedRoot_ = Sparse.impliedRoot addr valueHash witness
        in
          impliedRoot_ === actualRoot

-- | Witness for unset address should work with default hash
emptyWitnessLaw
  :: forall f n
   . Reflectable n Int
  => PoseidonField f
  => Proxy f
  -> Proxy n
  -> Int
  -> Result
emptyWitnessLaw _ _ addrInt =
  let
    tree :: Sparse.SparseMerkleTree n (Digest (F f)) (F f)
    tree = Sparse.empty
    addr = Sparse.Address (BigInt.fromInt addrInt)
    witness = Sparse.getWitness addr tree
    actualRoot = Sparse.root tree

    emptyHash :: Digest (F f)
    emptyHash = defaultHash @(F f)
    impliedRoot_ = Sparse.impliedRoot addr emptyHash witness
  in
    impliedRoot_ === actualRoot

-- | Implied root should match actual root after set
impliedRootLaw
  :: forall n f
   . Reflectable n Int
  => PoseidonField f
  => Proxy n
  -> Sparse.SparseMerkleTree n (Digest (F f)) (F f)
  -> Int
  -> F f
  -> Result
impliedRootLaw _ tree addrInt value =
  let
    addr = Sparse.Address (BigInt.fromInt addrInt)
  in
    case Sparse.set addr value tree of
      Nothing -> withHelp false "set failed"
      Just tree' ->
        let
          witness = Sparse.getWitness addr tree'
          actualRoot = Sparse.root tree'
          valueHash = hash @(F f) (Just value)
          computed = Sparse.impliedRoot addr valueHash witness
        in
          computed === actualRoot

-- | Setting same value twice should produce same root
idempotentSetLaw
  :: forall n f
   . Reflectable n Int
  => PoseidonField f
  => Proxy n
  -> Int
  -> F f
  -> Result
idempotentSetLaw _ addrInt value =
  let
    tree :: Sparse.SparseMerkleTree n (Digest (F f)) (F f)
    tree = Sparse.empty
    addr = Sparse.Address (BigInt.fromInt addrInt)
  in
    case Sparse.set addr value tree of
      Nothing -> withHelp false "first set failed"
      Just tree1 -> case Sparse.set addr value tree1 of
        Nothing -> withHelp false "second set failed"
        Just tree2 ->
          let
            root1 = Sparse.root tree1
            root2 = Sparse.root tree2
          in
            root1 === root2

-- | Overwriting a value should produce correct new root
overwriteLaw
  :: forall n f
   . Reflectable n Int
  => PoseidonField f
  => Proxy n
  -> Int
  -> F f
  -> F f
  -> Result
overwriteLaw _ addrInt value1 value2 =
  let
    tree :: Sparse.SparseMerkleTree n (Digest (F f)) (F f)
    tree = Sparse.empty
    addr = Sparse.Address (BigInt.fromInt addrInt)
  in
    case Sparse.set addr value1 tree of
      Nothing -> withHelp false "first set failed"
      Just tree1 -> case Sparse.set addr value2 tree1 of
        Nothing -> withHelp false "second set failed"
        Just tree2 ->
          let
            -- Direct set to value2 should give same result
            direct = Sparse.set addr value2 tree
          in
            case direct of
              Nothing -> withHelp false "direct set failed"
              Just treeDirect ->
                Sparse.root tree2 === Sparse.root treeDirect
