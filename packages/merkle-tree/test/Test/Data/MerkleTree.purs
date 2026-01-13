module Test.Data.MerkleTree where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Foldable (foldl, for_)
import Data.Int (pow)
import Data.List ((:))
import Data.List as List
import Data.List.Types (NonEmptyList(..))
import Data.Maybe (Maybe(..), fromJust)
import Data.MerkleTree as MT
import Data.NonEmpty (NonEmpty(..))
import Data.Tuple (Tuple(..))
import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Poseidon.Class (class PoseidonField)
import Snarky.Circuit.RandomOracle (Digest)
import Snarky.Circuit.Types (F)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (Result, arbitrary, quickCheck, quickCheckGen, withHelp, (===))
import Test.QuickCheck.Gen (Gen, chooseInt, vectorOf)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec :: Spec Unit
spec = describe "Dynamic MerkleTree Property Laws" do
  describe "Element recovery with dynamic growth" do

    it "preserves all elements when using individual add_ operations (natural tree growth)" do
      liftEffect $ quickCheck $ canRecoverElementsAdd (Proxy @Pallas.ScalarField)

    it "preserves all elements when using addMany (batch insertion with automatic expansion)" do
      liftEffect $ quickCheck $ canRecoverElementsAddMany (Proxy @Vesta.ScalarField)

    it "validates merkle paths for all elements (cryptographic proof correctness)" do
      liftEffect $ quickCheck $ pathValidationLaw (Proxy @Pallas.ScalarField)

    it "increases depth by 1 when exceeding 2^d capacity (automatic expansion)" $ liftEffect do
      for_ (Array.range 1 5) \targetDepth ->
        quickCheckGen $ depthExpansionLaw targetDepth

  describe "Set operations" do

    it "set-get law: get after set returns the new value" $ liftEffect do
      for_ (Array.range 1 4) \depth ->
        quickCheckGen $ setGetLaw depth

    it "set preserves other elements: setting at one address doesn't affect others" $ liftEffect do
      for_ (Array.range 2 4) \depth ->
        quickCheckGen $ setPreservesOthersLaw depth

    it "set updates root correctly: path validates against new root" $ liftEffect do
      for_ (Array.range 1 4) \depth ->
        quickCheckGen $ setUpdatesRootLaw depth

    it "set returns Nothing for invalid address" $ liftEffect do
      -- Start from depth 2 to ensure we always have room for invalid indices
      for_ (Array.range 2 4) \depth ->
        quickCheckGen $ setInvalidAddressLaw depth

canRecoverElementsAddMany :: forall f. PoseidonField f => Proxy f -> NonEmptyList (F f) -> Result
canRecoverElementsAddMany _ expected@(NonEmptyList (NonEmpty a as)) =
  let
    base :: MT.MerkleTree (Digest (F f)) (F f)
    base = MT.create a
    mt = MT.addMany base (List.fromFoldable as)
    elems = MT.toUnfoldable mt
  in
    Array.fromFoldable expected === elems

canRecoverElementsAdd :: forall f. PoseidonField f => Proxy f -> NonEmptyList (F f) -> Result
canRecoverElementsAdd _ expected@(NonEmptyList (NonEmpty a as)) =
  let
    base :: MT.MerkleTree (Digest (F f)) (F f)
    base = MT.create a
    mt = foldl MT.add_ base as
    elems = MT.toUnfoldable mt
  in
    Array.fromFoldable expected === elems

-- Path validation law: For any element in the tree, its path should validate against the root
pathValidationLaw :: forall f. PoseidonField f => Proxy f -> NonEmptyList (F f) -> Result
pathValidationLaw _ (NonEmptyList (NonEmpty a as)) =
  let
    base :: MT.MerkleTree (Digest (F f)) (F f)
    base = MT.create a
    mt = MT.addMany base (List.fromFoldable as)
    rootHash = MT.root mt
    allElements = a : as

    -- Check path validation for each element at its index
    pathValidations = Array.mapWithIndex
      ( \index element ->
          let
            addr = MT.Address (BigInt.fromInt index)
          in
            case MT.getPath mt addr of
              Nothing -> false -- Path should exist for valid index
              Just path ->
                let
                  leafHash = MT.hash $ Just element
                  computedRoot = MT.impliedRoot addr leafHash path
                in
                  computedRoot == rootHash
      )
      (Array.fromFoldable allElements)

    -- All path validations should succeed
    allValid = Array.all identity pathValidations
  in
    true === allValid

-- Depth expansion law: Adding one element beyond 2^d capacity should increase depth by 1
depthExpansionLaw :: Int -> Gen Result
depthExpansionLaw targetDepth = do
  -- Generate exactly 2^d elements to fill tree to capacity
  vs <- vectorOf (2 `pow` targetDepth) (arbitrary @(F Pallas.ScalarField))
  extraElement <- arbitrary @(F Pallas.ScalarField)
  let
    nea = unsafePartial $ fromJust $ NEA.fromArray vs
    { head: a, tail: as } = NEA.uncons nea

    base :: MT.MerkleTree (Digest (F Pallas.ScalarField)) (F Pallas.ScalarField)
    base = MT.create a
    fullTree = MT.addMany base (List.fromFoldable as)
    depthBefore = MT.depth fullTree
    expandedTree = MT.add_ fullTree extraElement
    depthAfter = MT.depth expandedTree
  pure $ (depthBefore == targetDepth && depthAfter == targetDepth + 1) === true

-- Set-Get Law: After setting a value at an address, get should return that value
setGetLaw :: Int -> Gen Result
setGetLaw depth = do
  let numElements = 2 `pow` depth
  vs <- vectorOf numElements (arbitrary @(F Pallas.ScalarField))
  setIndex <- chooseInt 0 (numElements - 1)
  newValue <- arbitrary @(F Pallas.ScalarField)
  let
    nea = unsafePartial $ fromJust $ NEA.fromArray vs
    { head: a, tail: as } = NEA.uncons nea

    base :: MT.MerkleTree (Digest (F Pallas.ScalarField)) (F Pallas.ScalarField)
    base = MT.create a
    mt = MT.addMany base (List.fromFoldable as)
    addr = MT.Address (BigInt.fromInt setIndex)
  pure $ case MT.set mt addr newValue of
    Nothing -> withHelp false "set returned Nothing for valid address"
    Just mt' -> case MT.get mt' addr of
      Nothing -> withHelp false "get returned Nothing after set"
      Just retrieved -> retrieved === newValue

-- Set preserves other elements: the element list should be the same except at the updated index
setPreservesOthersLaw :: Int -> Gen Result
setPreservesOthersLaw depth = do
  let numElements = 2 `pow` depth
  vs <- vectorOf numElements (arbitrary @(F Pallas.ScalarField))
  setIndex <- chooseInt 0 (numElements - 1)
  newValue <- arbitrary @(F Pallas.ScalarField)
  let
    nea = unsafePartial $ fromJust $ NEA.fromArray vs
    { head: a, tail: as } = NEA.uncons nea

    base :: MT.MerkleTree (Digest (F Pallas.ScalarField)) (F Pallas.ScalarField)
    base = MT.create a
    mt = MT.addMany base (List.fromFoldable as)

    originalElems :: Array (F Pallas.ScalarField)
    originalElems = MT.toUnfoldable mt
    expectedElems = Array.modifyAt setIndex (const newValue) originalElems
  pure $ case Tuple (MT.set mt (MT.Address (BigInt.fromInt setIndex)) newValue) expectedElems of
    Tuple Nothing _ -> withHelp false "set returned Nothing for valid address"
    Tuple _ Nothing -> withHelp false "modifyAt returned Nothing"
    Tuple (Just mt') (Just expected) ->
      let
        actual :: Array (F Pallas.ScalarField)
        actual = MT.toUnfoldable mt'
      in
        actual === expected

-- Set updates root correctly: after set, path from new value validates against new root
setUpdatesRootLaw :: Int -> Gen Result
setUpdatesRootLaw depth = do
  let numElements = 2 `pow` depth
  vs <- vectorOf numElements (arbitrary @(F Pallas.ScalarField))
  setIndex <- chooseInt 0 (numElements - 1)
  newValue <- arbitrary @(F Pallas.ScalarField)
  let
    nea = unsafePartial $ fromJust $ NEA.fromArray vs
    { head: a, tail: as } = NEA.uncons nea

    base :: MT.MerkleTree (Digest (F Pallas.ScalarField)) (F Pallas.ScalarField)
    base = MT.create a
    mt = MT.addMany base (List.fromFoldable as)
    addr = MT.Address (BigInt.fromInt setIndex)
  pure $ case MT.set mt addr newValue of
    Nothing -> withHelp false "set returned Nothing for valid address"
    Just mt' ->
      let
        newRoot = MT.root mt'
      in
        case MT.getPath mt' addr of
          Nothing -> withHelp false "getPath returned Nothing after set"
          Just path ->
            let
              leafHash = MT.hash $ Just newValue
              computedRoot = MT.impliedRoot addr leafHash path
            in
              withHelp (computedRoot == newRoot)
                ("Computed root doesn't match: computed " <> show computedRoot <> ", actual " <> show newRoot)

-- Set returns Nothing for an address that doesn't exist in the tree
-- We create a partially filled tree and try to set at an empty slot
setInvalidAddressLaw :: Int -> Gen Result
setInvalidAddressLaw depth = do
  let maxElements = 2 `pow` depth
  -- Generate a tree with 1 to maxElements-2 elements (leaving at least 2 empty slots)
  numElements <- chooseInt 1 (maxElements - 2)
  vs <- vectorOf numElements (arbitrary @(F Pallas.ScalarField))
  -- Pick an invalid index: one that's beyond current size but within capacity
  invalidIndex <- chooseInt numElements (maxElements - 1)
  newValue <- arbitrary @(F Pallas.ScalarField)
  let
    nea = unsafePartial $ fromJust $ NEA.fromArray vs
    { head: a, tail: as } = NEA.uncons nea

    base :: MT.MerkleTree (Digest (F Pallas.ScalarField)) (F Pallas.ScalarField)
    base = MT.create a
    mt = MT.addMany base (List.fromFoldable as)
    addr = MT.Address (BigInt.fromInt invalidIndex)
    result = MT.set mt addr newValue
  pure $ case result of
    Nothing -> true === true
    Just _ -> withHelp false ("set should return Nothing for invalid address " <> show invalidIndex <> " (tree has " <> show numElements <> " elements)")