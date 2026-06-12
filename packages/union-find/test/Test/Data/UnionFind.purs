-- | Tests for the mutable, array-backed union-find (the production
-- | structure — the pure Map-backed variant it replaced is gone).
-- |
-- | Contract notes the tests rely on:
-- |   * indices are DENSE non-negative ints: touching index `i` allocates
-- |     0..i as singleton classes, so `equivalenceClasses` enumerates every
-- |     allocated index, not just the ones a test mentioned;
-- |   * `connected` is derived: same `find` root.
-- |
-- | Property-style cases draw their inputs with `randomSample'` and check
-- | each sample in `Effect` directly — purescript-quickcheck has no
-- | monadic-property API, and this keeps `unsafePerformEffect` out.
module Test.Data.UnionFind where

import Prelude

import Data.Array as Array
import Data.Foldable (for_)
import Data.Traversable (traverse, traverse_)
import Data.UnionFind.Mutable (MutableUF, equivalenceClasses, find, fresh, union)
import Effect (Effect)
import Effect.Class (liftEffect)
import Test.QuickCheck.Gen (Gen, chooseInt, randomSample')
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

connected :: Int -> Int -> MutableUF -> Effect Boolean
connected x y uf = (==) <$> find x uf <*> find y uf

-- | Sample an effectful property 100 times.
forSamples :: forall a. Gen a -> (a -> Effect Unit) -> Effect Unit
forSamples gen check = randomSample' 100 gen >>= traverse_ check

idx :: Gen Int
idx = chooseInt 0 100

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  describe "Data.UnionFind.Mutable" do
    describe "Basic operations" do
      it "find returns element for singleton sets" do
        root <- liftEffect do
          uf <- fresh
          find 42 uf
        root `shouldEqual` 42

      it "connected returns true for same element" do
        r <- liftEffect do
          uf <- fresh
          connected 42 42 uf
        r `shouldEqual` true

      it "connected returns false for different elements initially" do
        r <- liftEffect do
          uf <- fresh
          connected 1 2 uf
        r `shouldEqual` false

      it "union makes elements connected" do
        r <- liftEffect do
          uf <- fresh
          union 1 2 uf
          connected 1 2 uf
        r `shouldEqual` true

      it "union is transitive" do
        r <- liftEffect do
          uf <- fresh
          union 1 2 uf
          union 2 3 uf
          connected 1 3 uf
        r `shouldEqual` true

      it "path compression keeps chains rooted together" do
        r <- liftEffect do
          uf <- fresh
          union 0 1 uf
          union 1 2 uf
          union 2 3 uf
          union 3 4 uf
          root0 <- find 0 uf
          root4 <- find 4 uf
          pure (root0 == root4)
        r `shouldEqual` true

    describe "Property-based tests (100 random samples each)" do
      it "reflexivity: every element is connected to itself" do
        liftEffect $ forSamples idx \x -> do
          uf <- fresh
          c <- connected x x uf
          c `shouldEqual` true

      it "find is idempotent" do
        liftEffect $ forSamples idx \x -> do
          uf <- fresh
          root1 <- find x uf
          root2 <- find root1 uf
          root2 `shouldEqual` root1

      it "symmetry: connected(x,y) = connected(y,x)" do
        liftEffect $ forSamples ({ x: _, y: _ } <$> idx <*> idx) \{ x, y } -> do
          uf1 <- fresh
          xy <- connected x y uf1
          uf2 <- fresh
          yx <- connected y x uf2
          xy `shouldEqual` yx

      it "transitivity after unions" do
        liftEffect $ forSamples ({ x: _, y: _, z: _ } <$> idx <*> idx <*> idx) \{ x, y, z } -> do
          uf <- fresh
          union x y uf
          union y z uf
          c <- connected x z uf
          c `shouldEqual` true

      it "union doesn't break existing connections" do
        liftEffect $ forSamples ({ a: _, b: _, c: _, d: _ } <$> idx <*> idx <*> idx <*> idx) \{ a, b, c, d } -> do
          uf <- fresh
          union a b uf
          wasConnected <- connected a b uf
          union c d uf
          stillConnected <- connected a b uf
          stillConnected `shouldEqual` wasConnected
          stillConnected `shouldEqual` true

    describe "Equivalence class properties" do
      it "equivalence classes partition the elements" do
        let elements = [ 1, 2, 3, 4, 5 ]
        r <- liftEffect do
          uf <- fresh
          union 1 2 uf
          union 2 3 uf
          union 4 5 uf
          group1 <- traverse (\x -> connected 1 x uf) elements
          group2 <- traverse (\x -> connected 4 x uf) elements
          pure { group1, group2 }
        r.group1 `shouldEqual` [ true, true, true, false, false ]
        r.group2 `shouldEqual` [ false, false, false, true, true ]

      it "all elements in same component have same representative" do
        roots <- liftEffect do
          uf <- fresh
          union 1 2 uf
          union 2 3 uf
          union 3 4 uf
          traverse (\x -> find x uf) [ 1, 2, 3, 4 ]
        Array.length (Array.nub roots) `shouldEqual` 1

      it "different components have different representatives" do
        r <- liftEffect do
          uf <- fresh
          union 1 2 uf
          union 3 4 uf
          root12 <- find 1 uf
          root34 <- find 3 uf
          pure { root12, root34 }
        r.root12 `shouldNotEqual` r.root34

    describe "Performance and edge cases" do
      it "handles many unions efficiently" do
        r <- liftEffect do
          uf <- fresh
          for_ (Array.range 0 98) \i -> union i (i + 1) uf
          connected 0 99 uf
        r `shouldEqual` true

      it "handles repeated unions of same elements" do
        r <- liftEffect do
          uf <- fresh
          union 1 2 uf
          union 1 2 uf
          union 2 1 uf
          union 1 2 uf
          connected 1 2 uf
        r `shouldEqual` true

      it "find creates singleton sets for new elements" do
        r <- liftEffect do
          uf <- fresh
          root1 <- find 42 uf
          root2 <- find 43 uf
          notConnected <- not <$> connected 42 43 uf
          pure (root1 == 42 && root2 == 43 && notConnected)
        r `shouldEqual` true

    describe "Complex scenarios" do
      it "handles star topology" do
        let leaves = [ 1, 2, 3, 4, 5 ]
        r <- liftEffect do
          uf <- fresh
          traverse_ (\l -> union 0 l uf) leaves
          allToCenter <- traverse (\l -> connected 0 l uf) leaves
          allPairs <- traverse (\i -> traverse (\j -> connected i j uf) leaves) leaves
          pure { allToCenter, allPairs }
        r.allToCenter `shouldEqual` [ true, true, true, true, true ]
        Array.all (Array.all identity) r.allPairs `shouldEqual` true

      it "handles multiple disconnected components" do
        r <- liftEffect do
          uf <- fresh
          union 1 2 uf
          union 2 3 uf
          union 4 5 uf
          union 5 6 uf
          _ <- find 7 uf
          comp1 <- traverse (\{ x, y } -> connected x y uf)
            [ { x: 1, y: 2 }, { x: 1, y: 3 }, { x: 2, y: 3 } ]
          comp2 <- traverse (\{ x, y } -> connected x y uf)
            [ { x: 4, y: 5 }, { x: 4, y: 6 }, { x: 5, y: 6 } ]
          between <- traverse (\{ x, y } -> not <$> connected x y uf)
            [ { x: 1, y: 4 }, { x: 1, y: 7 }, { x: 4, y: 7 } ]
          pure { comp1, comp2, between }
        r.comp1 `shouldEqual` [ true, true, true ]
        r.comp2 `shouldEqual` [ true, true, true ]
        r.between `shouldEqual` [ true, true, true ]

    describe "Equivalence classes enumeration" do
      it "returns all equivalence classes (dense: index 0 is allocated too)" do
        classes <- liftEffect do
          uf <- fresh
          union 1 2 uf
          union 2 3 uf
          union 4 5 uf
          _ <- find 6 uf
          equivalenceClasses uf
        -- allocated 0..6: {0} {1,2,3} {4,5} {6}
        Array.length classes `shouldEqual` 4
        Array.sort (Array.concat classes) `shouldEqual` [ 0, 1, 2, 3, 4, 5, 6 ]
        Array.any (\cls -> Array.sort cls == [ 1, 2, 3 ]) classes `shouldEqual` true
        Array.any (\cls -> Array.sort cls == [ 4, 5 ]) classes `shouldEqual` true
        Array.any (\cls -> Array.sort cls == [ 6 ]) classes `shouldEqual` true

      it "returns empty array for fresh union-find" do
        classes <- liftEffect do
          uf <- fresh
          equivalenceClasses uf
        classes `shouldEqual` []

      it "returns singleton classes for disconnected elements" do
        classes <- liftEffect do
          uf <- fresh
          _ <- find 1 uf
          _ <- find 2 uf
          _ <- find 3 uf
          equivalenceClasses uf
        -- dense: allocates 0..3
        Array.length classes `shouldEqual` 4
        Array.sort (Array.concat classes) `shouldEqual` [ 0, 1, 2, 3 ]
        Array.all (\cls -> Array.length cls == 1) classes `shouldEqual` true
