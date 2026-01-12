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
import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Poseidon.Class (class PoseidonField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.Data.MerkleTree.Helpers (PoseidonHash)
import Test.QuickCheck (Result, arbitrary, quickCheck, quickCheckGen, (===))
import Test.QuickCheck.Gen (Gen, vectorOf)
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

canRecoverElementsAddMany :: forall f. PoseidonField f => Proxy f -> NonEmptyList f -> Result
canRecoverElementsAddMany _ expected@(NonEmptyList (NonEmpty a as)) =
  let
    base :: MT.MerkleTree (PoseidonHash f) f
    base = MT.create a
    mt = MT.addMany base (List.fromFoldable as)
    elems = MT.toUnfoldable mt
  in
    Array.fromFoldable expected === elems

canRecoverElementsAdd :: forall f. PoseidonField f => Proxy f -> NonEmptyList f -> Result
canRecoverElementsAdd _ expected@(NonEmptyList (NonEmpty a as)) =
  let
    base :: MT.MerkleTree (PoseidonHash f) f
    base = MT.create a
    mt = foldl MT.add_ base as
    elems = MT.toUnfoldable mt
  in
    Array.fromFoldable expected === elems

-- Path validation law: For any element in the tree, its path should validate against the root
pathValidationLaw :: forall f. PoseidonField f => Proxy f -> NonEmptyList f -> Result
pathValidationLaw _ (NonEmptyList (NonEmpty a as)) =
  let
    base :: MT.MerkleTree (PoseidonHash f) f
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
  vs <- vectorOf (2 `pow` targetDepth) (arbitrary @Pallas.ScalarField)
  extraElement <- arbitrary @Pallas.ScalarField
  let
    nea = unsafePartial $ fromJust $ NEA.fromArray vs
    { head: a, tail: as } = NEA.uncons nea

    base :: MT.MerkleTree (PoseidonHash Pallas.ScalarField) Pallas.ScalarField
    base = MT.create a
    fullTree = MT.addMany base (List.fromFoldable as)
    depthBefore = MT.depth fullTree
    expandedTree = MT.add_ fullTree extraElement
    depthAfter = MT.depth expandedTree
  pure $ (depthBefore == targetDepth && depthAfter == targetDepth + 1) === true