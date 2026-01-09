module Test.Main where

import Prelude

import Data.Foldable (traverse_)
import Data.List (List(..), (:))
import Data.List as List
import Data.Maybe (Maybe(..))
import Effect (Effect)
import JS.BigInt as BigInt
import Poseidon.Class (class PoseidonField, hash)
import Snarky.Curves.Class (fromInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.MerkleTree (class Hashable, class MergeHash, Address(..))
import Snarky.Data.MerkleTree as MT
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

-- Newtype for Poseidon hash to avoid orphan instance
newtype PoseidonHash f = PoseidonHash f

derive newtype instance Eq f => Eq (PoseidonHash f)
derive newtype instance Show f => Show (PoseidonHash f)

-- Instance of MergeHash for PoseidonHash
instance PoseidonField f => MergeHash (PoseidonHash f) where
  merge (PoseidonHash left) (PoseidonHash right) = PoseidonHash (hash [ left, right ])

-- Instance of Hashable for PoseidonHash
instance PoseidonField f => Hashable f (PoseidonHash f) where
  hash = case _ of
    Nothing -> PoseidonHash (hash [ zero ])
    Just x -> PoseidonHash (hash [ x ])

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  describe "Snarky MerkleTree" do
    describe "Basic functionality" do
      it "creates a tree with single element" do
        let
          tree = MT.create (one :: Pallas.BaseField) :: MT.MerkleTree (PoseidonHash Pallas.BaseField) Pallas.BaseField
        MT.depth tree `shouldEqual` 0 -- OCaml starts at depth 0
        MT.root tree `shouldEqual` PoseidonHash (hash [ one ])
        MT.get tree (Address zero) `shouldEqual` Just one

      it "adds elements to tree" do
        let
          tree0 = MT.create (one :: Pallas.BaseField) :: MT.MerkleTree (PoseidonHash Pallas.BaseField) Pallas.BaseField
          tree1 = MT.add_ tree0 (fromInt 2)
          tree2 = MT.add_ tree1 (fromInt 3)
          result = List.sort (MT.toUnfoldable tree2)
        result `shouldEqual` List.sort (one : fromInt 2 : fromInt 3 : Nil)

      it "adds many elements" do
        let
          tree = MT.create (zero :: Pallas.BaseField) :: MT.MerkleTree (PoseidonHash Pallas.BaseField) Pallas.BaseField
          values = List.fromFoldable $ map fromInt [ 1, 2, 3 ]
          finalTree = MT.addMany tree values
          result = List.sort (MT.toUnfoldable finalTree)
        result `shouldEqual` List.sort (zero : one : fromInt 2 : fromInt 3 : Nil)

      it "gets path correctly" do
        let
          tree0 = MT.create (one :: Pallas.BaseField) :: MT.MerkleTree (PoseidonHash Pallas.BaseField) Pallas.BaseField
          tree1 = MT.add_ tree0 (one + one)
        case MT.getPath tree1 (Address zero) of
          Just path -> do
            let leafHash = PoseidonHash (hash [ one ])
            let computedRoot = MT.impliedRoot (Address zero) leafHash path
            computedRoot `shouldEqual` MT.root tree1
          Nothing -> false `shouldEqual` true

      it "free hash operations work" do
        let
          tree = MT.create (one :: Pallas.BaseField) :: MT.MerkleTree (PoseidonHash Pallas.BaseField) Pallas.BaseField
          freeRoot = MT.freeRoot tree
        case freeRoot of
          MT.HashValue _ -> true `shouldEqual` true -- Single element tree has just a hash value
          _ -> false `shouldEqual` true

      it "tree operations are safe" do
        let
          tree = MT.create (one :: Pallas.BaseField) :: MT.MerkleTree (PoseidonHash Pallas.BaseField) Pallas.BaseField
        -- Tree operations should not crash
        MT.depth tree `shouldEqual` 0

      it "maintains binary tree structure" do
        let
          tree0 = MT.create (zero :: Pallas.BaseField) :: MT.MerkleTree (PoseidonHash Pallas.BaseField) Pallas.BaseField
          tree1 = MT.add_ tree0 one
          tree2 = MT.add_ tree1 (fromInt 2)
          tree3 = MT.add_ tree2 (fromInt 3)
          tree4 = MT.add_ tree3 (fromInt 4)

        -- Check depths increase properly
        MT.depth tree0 `shouldEqual` 0
        MT.depth tree1 `shouldEqual` 1 -- First add doubles tree
        MT.depth tree2 `shouldEqual` 2 -- Second add doubles again
        MT.depth tree3 `shouldEqual` 2 -- Third add fits in existing structure
        MT.depth tree4 `shouldEqual` 3 -- Fourth add requires new level

        -- Verify all elements are retrievable
        MT.get tree4 (Address zero) `shouldEqual` Just zero
        MT.get tree4 (Address one) `shouldEqual` Just one
        MT.get tree4 (Address $ BigInt.fromInt 2) `shouldEqual` Just (fromInt 2)
        MT.get tree4 (Address $ BigInt.fromInt 3) `shouldEqual` Just (fromInt 3)
        MT.get tree4 (Address $ BigInt.fromInt 4) `shouldEqual` Just (fromInt 4)

        -- Verify implied roots work for each position
        traverse_
          ( \i ->
              case MT.get tree4 i of
                Just value -> do
                  case MT.getPath tree4 i of
                    Just path -> do
                      let leafHash = PoseidonHash (hash [ value ])
                      let computedRoot = MT.impliedRoot i leafHash path
                      computedRoot `shouldEqual` MT.root tree4
                    Nothing -> false `shouldEqual` true
                Nothing -> false `shouldEqual` true
          )
          (map (Address <<< BigInt.fromInt) (List.range 0 4))