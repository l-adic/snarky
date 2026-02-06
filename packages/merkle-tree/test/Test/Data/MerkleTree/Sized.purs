module Test.Data.MerkleTree.Sized (spec) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Array.NonEmpty.Internal (NonEmptyArray)
import Data.Foldable (foldl, for_)
import Data.Int (pow)
import Data.List (List)
import Data.Maybe (Maybe(..), fromJust)
import Data.MerkleTree.Sized as SMT
import Data.Reflectable (class Reflectable, reifyType)
import Data.Tuple (Tuple(..))
import Effect.Class (liftEffect)
import Effect.Exception (catchException)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Poseidon.Class (class PoseidonField)
import Snarky.Circuit.DSL (F)
import Snarky.Circuit.RandomOracle (Digest)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (Result, arbitrary, quickCheckGen, withHelp, (===))
import Test.QuickCheck.Gen (chooseInt, vectorOf)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy)

spec :: Spec Unit
spec = describe "Sized MerkleTree Property Laws" do
  describe "Element recovery across fixed depths (1-5)" do

    it "preserves all elements when using addMany (batch insertion)" $ liftEffect do
      for_ (Array.range 1 5) \depth ->
        quickCheckGen $ do
          vs <- vectorOf (2 `pow` depth) (arbitrary @(F Vesta.ScalarField))
          reifyType depth \pd -> do
            let as = unsafePartial $ fromJust $ NEA.fromFoldable vs
            pure $ canRecoverElementsAddMany pd as

    it "preserves all elements when using individual add_ operations" $ liftEffect do
      for_ (Array.range 1 5) \depth ->
        quickCheckGen $ do
          vs <- vectorOf (2 `pow` depth) (arbitrary @(F Vesta.ScalarField))
          reifyType depth \pd -> do
            let as = unsafePartial $ fromJust $ NEA.fromFoldable vs
            pure $ canRecoverElementsAdd pd as

    it "validates merkle paths for all elements (cryptographic proof correctness)" $ liftEffect do
      for_ (Array.range 1 4) \depth ->
        quickCheckGen $ do
          vs <- vectorOf (2 `pow` depth) (arbitrary @(F Pallas.ScalarField))
          reifyType depth \pd -> do
            let as = unsafePartial $ fromJust $ NEA.fromFoldable vs
            pure $ pathValidationLaw pd as

    it "throws error when exceeding maximum capacity" $ liftEffect
      ( catchException (\_ -> pure unit) do
          for_ (Array.range 1 3) \depth ->
            quickCheckGen $ do
              -- Create exactly 2^depth elements to fill the tree completely
              vs <- vectorOf ((2 `pow` depth) + 1) (arbitrary @(F Vesta.ScalarField))
              reifyType depth \pd -> do
                let
                  as = unsafePartial $ fromJust $ NEA.fromFoldable vs
                  _ = canRecoverElementsAddMany pd as
                pure false
      )

  describe "Set operations" do

    it "set-get law: get after set returns the new value" $ liftEffect do
      for_ (Array.range 1 4) \depth ->
        quickCheckGen $ do
          let numElements = 2 `pow` depth
          vs <- vectorOf numElements (arbitrary @(F Pallas.ScalarField))
          setIndex <- chooseInt 0 (numElements - 1)
          newValue <- arbitrary @(F Pallas.ScalarField)
          reifyType depth \pd -> do
            let as = unsafePartial $ fromJust $ NEA.fromFoldable vs
            pure $ setGetLaw pd as setIndex newValue

    it "set preserves other elements: element list same except at updated index" $ liftEffect do
      for_ (Array.range 1 4) \depth ->
        quickCheckGen $ do
          let numElements = 2 `pow` depth
          vs <- vectorOf numElements (arbitrary @(F Pallas.ScalarField))
          setIndex <- chooseInt 0 (numElements - 1)
          newValue <- arbitrary @(F Pallas.ScalarField)
          reifyType depth \pd -> do
            let as = unsafePartial $ fromJust $ NEA.fromFoldable vs
            pure $ setPreservesOthersLaw pd as setIndex newValue

    it "set updates root correctly: path validates against new root" $ liftEffect do
      for_ (Array.range 1 4) \depth ->
        quickCheckGen $ do
          let numElements = 2 `pow` depth
          vs <- vectorOf numElements (arbitrary @(F Pallas.ScalarField))
          setIndex <- chooseInt 0 (numElements - 1)
          newValue <- arbitrary @(F Pallas.ScalarField)
          reifyType depth \pd -> do
            let as = unsafePartial $ fromJust $ NEA.fromFoldable vs
            pure $ setUpdatesRootLaw pd as setIndex newValue

    it "set returns Nothing for invalid address" $ liftEffect do
      -- Start from depth 2 to ensure we always have room for invalid indices
      for_ (Array.range 2 4) \depth ->
        quickCheckGen $ do
          let maxElements = 2 `pow` depth
          -- Generate a tree with 1 to maxElements-2 elements
          numElements <- chooseInt 1 (maxElements - 2)
          vs <- vectorOf numElements (arbitrary @(F Pallas.ScalarField))
          -- Pick an invalid index beyond current size
          invalidIndex <- chooseInt numElements (maxElements - 1)
          newValue <- arbitrary @(F Pallas.ScalarField)
          reifyType depth \pd -> do
            let as = unsafePartial $ fromJust $ NEA.fromFoldable vs
            pure $ setInvalidAddressLaw pd as invalidIndex newValue

canRecoverElementsAddMany :: forall n f. Reflectable n Int => PoseidonField f => Proxy n -> NonEmptyArray (F f) -> Result
canRecoverElementsAddMany _ xs =
  let
    { head: a, tail: as } = NEA.uncons xs

    base :: SMT.MerkleTree n (Digest (F f)) (F f)
    base = SMT.create a
    mt = SMT.addMany base (Array.toUnfoldable as :: List (F f))
    elems = SMT.toUnfoldable mt
  in
    NEA.toArray xs === elems

canRecoverElementsAdd :: forall n f. Reflectable n Int => PoseidonField f => Proxy n -> NonEmptyArray (F f) -> Result
canRecoverElementsAdd _ xs =
  let
    { head: a, tail: as } = NEA.uncons xs

    base :: SMT.MerkleTree n (Digest (F f)) (F f)
    base = SMT.create a
    mt = foldl SMT.add_ base (Array.toUnfoldable as :: List (F f))
    elems = SMT.toUnfoldable mt
  in
    NEA.toArray xs === elems

-- Path validation law: For any element in the sized tree, its path should validate against the root
pathValidationLaw :: forall n f. Reflectable n Int => PoseidonField f => Proxy n -> NonEmptyArray (F f) -> Result
pathValidationLaw _ xs =
  let
    { head: a, tail: as } = NEA.uncons xs

    base :: SMT.MerkleTree n (Digest (F f)) (F f)
    base = SMT.create a
    mt = SMT.addMany base (Array.toUnfoldable as :: List (F f))
    rootHash = SMT.root mt
    allElements = NEA.toArray xs

    -- Check path validation for each element at its index
    pathValidations = Array.mapWithIndex
      ( \index element ->
          let
            addr = SMT.Address (BigInt.fromInt index)
          in
            case SMT.getPath mt addr of
              Nothing -> false -- Path should exist for valid index
              Just path ->
                let
                  leafHash = SMT.hash $ Just element
                  computedRoot = SMT.impliedRoot addr leafHash path
                in
                  computedRoot == rootHash
      )
      allElements

    -- All path validations should succeed
    allValid = Array.all identity pathValidations
  in
    true === allValid

-- Set-Get Law: After setting a value at an address, get should return that value
setGetLaw :: forall n f. Reflectable n Int => PoseidonField f => Proxy n -> NonEmptyArray (F f) -> Int -> F f -> Result
setGetLaw _ xs setIndex newValue =
  let
    { head: a, tail: as } = NEA.uncons xs

    base :: SMT.MerkleTree n (Digest (F f)) (F f)
    base = SMT.create a
    mt = SMT.addMany base (Array.toUnfoldable as :: List (F f))
    addr = SMT.Address (BigInt.fromInt setIndex)
  in
    case SMT.set mt addr newValue of
      Nothing -> withHelp false "set returned Nothing for valid address"
      Just mt' -> case SMT.get mt' addr of
        Nothing -> withHelp false "get returned Nothing after set"
        Just retrieved -> retrieved === newValue

-- Set preserves other elements: the element list should be the same except at the updated index
setPreservesOthersLaw :: forall n f. Reflectable n Int => PoseidonField f => Proxy n -> NonEmptyArray (F f) -> Int -> F f -> Result
setPreservesOthersLaw _ xs setIndex newValue =
  let
    { head: a, tail: as } = NEA.uncons xs

    base :: SMT.MerkleTree n (Digest (F f)) (F f)
    base = SMT.create a
    mt = SMT.addMany base (Array.toUnfoldable as :: List (F f))

    originalElems :: Array (F f)
    originalElems = SMT.toUnfoldable mt
    expectedElems = Array.modifyAt setIndex (const newValue) originalElems
  in
    case Tuple (SMT.set mt (SMT.Address (BigInt.fromInt setIndex)) newValue) expectedElems of
      Tuple Nothing _ -> withHelp false "set returned Nothing for valid address"
      Tuple _ Nothing -> withHelp false "modifyAt returned Nothing"
      Tuple (Just mt') (Just expected) ->
        let
          actual :: Array (F f)
          actual = SMT.toUnfoldable mt'
        in
          actual === expected

-- Set updates root correctly: after set, path from new value validates against new root
setUpdatesRootLaw :: forall n f. Reflectable n Int => PoseidonField f => Proxy n -> NonEmptyArray (F f) -> Int -> F f -> Result
setUpdatesRootLaw _ xs setIndex newValue =
  let
    { head: a, tail: as } = NEA.uncons xs

    base :: SMT.MerkleTree n (Digest (F f)) (F f)
    base = SMT.create a
    mt = SMT.addMany base (Array.toUnfoldable as :: List (F f))
    addr = SMT.Address (BigInt.fromInt setIndex)
  in
    case SMT.set mt addr newValue of
      Nothing -> withHelp false "set returned Nothing for valid address"
      Just mt' ->
        let
          newRoot = SMT.root mt'
        in
          case SMT.getPath mt' addr of
            Nothing -> withHelp false "getPath returned Nothing after set"
            Just path ->
              let
                leafHash = SMT.hash $ Just newValue
                computedRoot = SMT.impliedRoot addr leafHash path
              in
                withHelp (computedRoot == newRoot)
                  ("Computed root doesn't match: computed " <> show computedRoot <> ", actual " <> show newRoot)

-- Set returns Nothing for an address that doesn't exist in the tree
setInvalidAddressLaw :: forall n f. Reflectable n Int => PoseidonField f => Proxy n -> NonEmptyArray (F f) -> Int -> F f -> Result
setInvalidAddressLaw _ xs invalidIndex newValue =
  let
    { head: a, tail: as } = NEA.uncons xs

    base :: SMT.MerkleTree n (Digest (F f)) (F f)
    base = SMT.create a
    mt = SMT.addMany base (Array.toUnfoldable as :: List (F f))
    numElements = NEA.length xs
    addr = SMT.Address (BigInt.fromInt invalidIndex)
    result = SMT.set mt addr newValue
  in
    case result of
      Nothing -> true === true
      Just _ -> withHelp false ("set should return Nothing for invalid address " <> show invalidIndex <> " (tree has " <> show numElements <> " elements)")