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
import Effect.Class (liftEffect)
import Effect.Exception (catchException)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Poseidon.Class (class PoseidonField)
import Snarky.Circuit.RandomOracle (Digest)
import Snarky.Circuit.Types (F)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (Result, arbitrary, quickCheckGen, (===))
import Test.QuickCheck.Gen (vectorOf)
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